(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_val_record.ml
 **       lifting of a numerical domain into a value domain
 ** Jiangchao Liu, 2012/04/17 *)
open Data_structures
open Lib
open Offs

open Printf
open Dom_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Svenv_sig

open Nd_utils
open Dom_utils

(* Possible improvements:
 *  [XR=>JL] : please explain more
 *  - introduce node types and manage them at this level
 *)

(** Error report *)
let this_module = "val_num"

module TupleOrder =
  struct
    type t = int * int * int
    let compare (a: t) (b: t) =
      let a1, a2, a3 = a in
      let b1, b2, b3 = b in
      if a1 = b1 then
        if a2 = b2 then
          a3 - b3
        else
          a2 - b2
      else
        a1 - b1
  end

module TupleSet = Set.Make(TupleOrder)

let queries: TupleSet.t ref = ref TupleSet.empty
let node_counter: int ref = ref 0
let edge_counter: int ref = ref 0

let print_set = IntSet.iter (Format.printf "%d ")

let ljc_print_map = IntMap.iter (Format.printf "%d -> %d\n")


module DotChanel =
  (struct
    type t =
       { t_nodes: int IntMap.t;
         t_edges: TupleSet.t; }

    let empty =
      { t_nodes = IntMap.empty;
        t_edges = TupleSet.empty; }

    let add_node (id: int) (x: t) =
      node_counter := !node_counter + 1;
      { x with t_nodes = IntMap.add id !node_counter x.t_nodes }

    let add_edge_common (set: IntSet.t)
        (ori_edges:  TupleSet.t) (counter: int) =
      assert (not (IntSet.is_empty set));
      let _, nedges =
        IntSet.fold
          (fun elt acc ->
            let remain_set, edges = acc in
            let remain_set = IntSet.remove elt remain_set in
            let edges =
              IntSet.fold
                (fun ie iac -> TupleSet.add (elt,ie,0) iac) remain_set edges in
            remain_set, edges
          ) set (set, ori_edges) in
      nedges

    let add_guard_edge (set: IntSet.t) (x: t) =
      let set =
        IntSet.fold
          (fun a acc ->
            IntSet.add (IntMap.find a x.t_nodes) acc
          ) set IntSet.empty in
      let nedges = add_edge_common set x.t_edges !edge_counter in
      edge_counter := !edge_counter + 1;
      { x with t_edges = nedges }

    let join (lx: t) (rx: t): t =
      { lx with t_edges = TupleSet.union lx.t_edges rx.t_edges }

    let rename (nmap: (int * IntSet.t) IntMap.t) (x: t) =
      IntMap.fold
        (fun elt (id, idset) acc ->
          assert (IntMap.mem elt acc.t_nodes);
          let target_id = IntMap.find elt acc.t_nodes in
          let nodes = IntMap.add id target_id acc.t_nodes in
          let acc = { acc with t_nodes = IntMap.remove elt nodes } in
          IntSet.fold
            (fun ielt iacc ->
              let iacc = add_node ielt iacc in
              add_guard_edge (IntSet.add ielt (IntSet.singleton elt)) iacc
            ) idset acc
        ) nmap x

    let add_query_edge (set: IntSet.t) (x: t) =
      let set =
        IntSet.fold
          (fun a acc ->
            let na = IntMap.find a x.t_nodes in
            IntSet.add na acc
          ) set IntSet.empty in
      queries := add_edge_common set !queries !edge_counter;
      edge_counter := !edge_counter + 1

    let print (x: t) (mess: string)=
      let file = Printf.sprintf "record-%d-%s" !edge_counter mess in
      let oc = open_out file in
      fprintf oc "digraph g {\n labelloc = \"t\"; \n label = \"no title\";\n";
      fprintf oc "graph [ rankdir = \"LR\" ];\n";
      let num_2str (elt: int) =
        if IntMap.mem elt !Dom_val_maya.global_namer then
          IntMap.find elt !Dom_val_maya.global_namer
        else Pervasives.string_of_int elt in
      IntMap.iter
        (fun elt lab ->
          fprintf oc "\"%d\" [\ label = \"%s\" shape = \"record\"];\n"
            lab (num_2str elt)
        ) x.t_nodes;
      TupleSet.iter
        (fun (l,r,le) ->
          fprintf oc
            "\"%d\" -> \"%d\" [\ label = \"%d\" color = blue];\n" l r le
        ) x.t_edges;
      TupleSet.iter
        (fun (l,r,le) ->
          fprintf oc "\"%d\" -> \"%d\" [\ label = \"%d\" color = red];\n" l r le
        ) !queries;
      fprintf oc "}";
      close_out oc
  end)

module Make_num_record = functor (Dv: DOM_NUM) ->
  (struct
    let module_name = "dom_num_record"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name Dv.module_name (Dv.config_2str ())
    type t =
        { t_main: Dv.t;
          t_trace: DotChanel.t;}
    let bot: t =
      { t_main = Dv.bot;
        t_trace = DotChanel.empty }
    let is_bot x  = Dv.is_bot x.t_main
    (* Top element *)
    let top = {t_main = Dv.top; t_trace = DotChanel.empty}
    (* Pretty-printing *)
    let t_2stri namer str x =
      Dv.t_2stri namer str x.t_main

    (* Node addition and removal *)
    let add_node (id: int) (t: t): t =
      { t_main = Dv.add_node id t.t_main;
        t_trace = DotChanel.add_node id t.t_trace }

    let rem_node (id: int) (t: t): t =
      { t with t_main = Dv.rem_node id t.t_main}

    let check_nodes (s: IntSet.t) (x: t): bool =
      Dv.check_nodes s x.t_main

    (* Renaming *)
    let vars_srename (nr: 'a node_mapping) (t: t): t =
      { t_main = Dv.vars_srename nr t.t_main;
        t_trace = DotChanel.rename nr.nm_map t.t_trace }

    let nodes_filter (nkeep: IntSet.t) (t: t): t =
      { t with t_main = Dv.nodes_filter nkeep t.t_main }

    (** Comparison, Join and Widening operators *)
    let is_le (t0: t) (t1: t) (f: int -> int -> bool): bool =
      DotChanel.print t0.t_trace "is_le-l";
      DotChanel.print t1.t_trace "is_le-r";
      Dv.is_le  t0.t_main t1.t_main f

    let join (t0: t) (t1: t): t =
      DotChanel.print t0.t_trace "join-l";
      DotChanel.print t1.t_trace "join-r";
      { t_main = Dv.join t0.t_main t1.t_main;
        t_trace = DotChanel.join t0.t_trace t1.t_trace}
    let widen (t0: t) (t1: t): t =
      DotChanel.print t0.t_trace "widen-l";
      DotChanel.print t1.t_trace "widne-r";
      { t_main = Dv.widen t0.t_main t1.t_main;
        t_trace = DotChanel.join t0.t_trace t1.t_trace}

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (cons: n_cons) (t: t): bool =
      let set = n_cons_fold IntSet.add cons IntSet.empty in
      DotChanel.add_query_edge set t.t_trace;
      Dv.sat cons  t.t_main

    (** Transfer functions *)
    let assign (dst: int) (expr: n_expr) (t: t): t =
      let set = n_expr_fold IntSet.add  expr (IntSet.singleton dst) in
      { t_trace = DotChanel.add_guard_edge set t.t_trace;
        t_main = Dv.assign dst expr t.t_main}

    let guard (b: bool) (cons: n_cons) (t: t): t =
      let set = n_cons_fold IntSet.add cons IntSet.empty in
      { t_trace = DotChanel.add_guard_edge set t.t_trace;
        t_main = Dv.guard b cons t.t_main}

    (** Utilities for the abstract domain *)
    let simplify_n_expr (t: t): n_expr -> n_expr = Dv.simplify_n_expr t.t_main

    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another *)
    let expand (id: int) (nid: int) (x: t): t =
      { t_trace = DotChanel.add_guard_edge
          (IntSet.add id (IntSet.singleton nid))
          (DotChanel.add_node nid x.t_trace);
        t_main = Dv.expand id nid x.t_main }

    (* Upper bound of the constraits of two dimensions *)
    let compact (lid: int) (rid: int) (x: t): t =
      { t_trace = DotChanel.add_guard_edge
          (IntSet.add lid (IntSet.singleton rid)) x.t_trace;
        t_main = Dv.compact lid rid x.t_main }

    (* Conjunction *)
    let meet (lx: t) (rx: t): t =
      DotChanel.print lx.t_trace "meet l";
      DotChanel.print rx.t_trace "meet r";
      { lx with t_main = Dv.widen lx.t_main rx.t_main }

    (* Forget the information on a dimension *)
    let forget (id: int) (x: t): t =
      { x with t_main = Dv.forget id x.t_main}

    (** Export of range information *)
    (* bound of a variable  *)
    let bound_variable (dim: int) (x: t): interval =
      Dv.bound_variable dim x.t_main

    let get_svs (x: t) : IntSet.t =
      Dv.get_svs x.t_main

    let get_eq_class (i: int) (x: t): IntSet.t =
      Dv.get_eq_class i x.t_main
  end: DOM_NUM)
