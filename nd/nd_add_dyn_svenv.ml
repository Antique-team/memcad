(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_add_dyn_svenv.ml
 **       Set of symbolic variables is dealt dynamically:
 **       Variable are added in the underlying numerical domain
 **       only when it is required 
 ** Antoine Toubhans, 2013/09/30 *)
open Data_structures
open Lib
open Nd_sig
open Nd_utils

module Log =
  Logger.Make(struct let section = "nd_+dsve" and level = Log_level.DEBUG end)

(** Functor *)
module Add_dyn_svenv = functor (D: DOM_NUM_NB) ->
  (struct
    let module_name = "nd_add_dyn_svenv"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name D.module_name (D.config_2str ())
    type t =
        { t_u: D.t;     (* underlying numerical *)
          t_s: IntSet.t (* not yet added in underlying env *) }
    (* Bottom element *)
    let is_bot (x: t): bool = D.is_bot x.t_u
    (* Top element *)
    let top: t = 
      { t_u = D.top;
        t_s = IntSet.empty }
    (* Pretty-printing *)
    let t_2stri (sn: sv_namer) (ind: string) (x: t): string =
      Printf.sprintf "%s%sNot yet added in env: { %s }\n"
        (D.t_2stri sn ind x.t_u) ind 
	(IntSet.fold 
	   (fun key acc->
	     let s =
               try IntMap.find key sn with _ -> Pervasives.string_of_int key in
	     if String.length acc < 1 then s
	     else acc^","^s
	   ) x.t_s "")
    (* Variables management *)
    let add_node (i: int) (x: t): t =
      { x with 
        t_s = IntSet.add i x.t_s }
    let rem_node (i: int) (x: t): t = 
      if IntSet.mem i x.t_s then { x with t_s = IntSet.remove i x.t_s }
      else { x with t_u = D.rem_node i x.t_u }
    (* Move a node from t_s component to underlying numerical component *)
    let activate_node (i: int) (x: t): t =
      if IntSet.mem i x.t_s then
        { t_u = D.add_node i x.t_u;
          t_s = IntSet.remove i x.t_s }
      else x
    let vars_srename (nr: 'a node_mapping) (x: t): t = 
      let map, rem, s =
        IntSet.fold
          (fun i (m, r, s) ->
            if IntMap.mem i m then
              let j, sj = IntMap.find i m in
              IntMap.remove i m, r,
              IntSet.union sj (IntSet.add j s)
            else
              if IntSet.mem i r then
                m, IntSet.remove i r, s
              else
                m, r, IntSet.add i s
          ) x.t_s (nr.nm_map, nr.nm_rem, IntSet.empty) in
      { t_u = D.vars_srename { nr with
                               nm_map = map;
                               nm_rem = rem } x.t_u;
        t_s = s }
    let check_nodes (s: IntSet.t) (x: t): bool =
      D.check_nodes (IntSet.diff s x.t_s) x.t_u
    let nodes_filter (nkeep: IntSet.t) (x: t): t =
      { t_u = D.nodes_filter (IntSet.diff nkeep x.t_s) x.t_u;
        t_s = IntSet.inter x.t_s nkeep }

    (** Comparison and Join operators *)
    let is_le (x0: t) (x1: t) (sat_diseq: int -> int -> bool): bool =
      let x0_u = IntSet.fold D.rem_node (IntSet.diff x1.t_s x0.t_s) x0.t_u in
      let x0_u = IntSet.fold D.add_node (IntSet.diff x0.t_s x1.t_s) x0_u in
      D.is_le x0_u x1.t_u sat_diseq

    let join (x0: t) (x1: t): t =
      let x0_weak = IntSet.fold D.rem_node (IntSet.diff x1.t_s x0.t_s) x0.t_u
      and x1_weak = IntSet.fold D.rem_node (IntSet.diff x0.t_s x1.t_s) x1.t_u in
      { t_u = D.join x0_weak x1_weak;
        t_s = IntSet.union x0.t_s x1.t_s }

    let widen (x0: t) (x1: t): t =
      let x0_weak = IntSet.fold D.rem_node (IntSet.diff x1.t_s x0.t_s) x0.t_u
      and x1_weak = IntSet.fold D.rem_node (IntSet.diff x0.t_s x1.t_s) x1.t_u in
      { t_u = D.widen x0_weak x1_weak;
        t_s = IntSet.union x0.t_s x1.t_s }

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (c: n_cons) (x: t): bool =
      let x = n_cons_fold activate_node c x in
      D.sat c x.t_u

    (** Transfer functions *)
    let assign (dst: int) (expr: n_expr) (x: t): t =
      match expr with
      | Ne_rand ->
          if IntSet.mem dst x.t_s then x
          else { x with
                 t_u = D.assign dst Ne_rand x.t_u }
      | _ ->
          let x = activate_node dst x in
          let x = n_expr_fold activate_node expr x in
          { x with
            t_u = D.assign dst expr x.t_u }
    let guard (b: bool) (c: n_cons) (x: t): t =
      match c with
      | Nc_rand -> x
      | _ ->
          let x = n_cons_fold activate_node c x in
          { x with
            t_u = D.guard b c x.t_u }

    (** Utilities for the abstract domain *)
    let simplify_n_expr (x: t) (e: n_expr): n_expr =
      let x = n_expr_fold activate_node e x in
      D.simplify_n_expr x.t_u e

    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another *)
    let expand (id: int) (nid: int) (x: t): t = 
      if IntSet.mem id x.t_s then { x with t_s = IntSet.add nid x.t_s }
      else { x with t_u = D.expand id nid x.t_u }
    (* Upper bound of the constraits of two dimensions *)
    let compact (lid: int) (rid: int) (x: t): t = 
      match IntSet.mem lid x.t_s, IntSet.mem rid x.t_s with
      | false,false -> { x with t_u = D.compact lid rid x.t_u }
      | false, true -> { t_u = D.rem_node lid x.t_u;
                         t_s = IntSet.add lid (IntSet.remove rid x.t_s) }
      |  true,false -> { x with t_u = D.rem_node rid x.t_u }
      |  true, true -> { x with t_s = IntSet.remove rid x.t_s }

    (** Conjunction *)
    let meet (lx: t) (rx: t): t =
      let lx_strong = 
        IntSet.fold D.add_node (IntSet.diff lx.t_s rx.t_s) lx.t_u
      and rx_strong =
        IntSet.fold D.add_node (IntSet.diff rx.t_s lx.t_s) rx.t_u in
      { t_u = D.meet lx_strong rx_strong;
        t_s = IntSet.inter lx.t_s rx.t_s }

    (** Forget the information on a dimension *)
    let sv_forget (id: int) (x: t): t =
      if IntSet.mem id x.t_s then x
      else
        { t_u = D.rem_node id x.t_u;
          t_s = IntSet.add id x.t_s }

    (** Export of range information *)
    (* the bound of a variable *)
    let bound_variable (dim: int) (x: t): interval =
      if IntSet.mem dim x.t_s then
        { intv_inf = None;
          intv_sup = None; }
      else
        D.bound_variable dim x.t_u

    (** Extract the set of all SVs *)
    let get_svs (x: t): IntSet.t =
      IntSet.union (D.get_svs x.t_u) x.t_s

    (** Extract all SVs that are equal to a given SV *)
    let get_eq_class (i: int) (x: t): IntSet.t =
      if IntSet.mem i x.t_s then (IntSet.singleton i)
      else D.get_eq_class i x.t_u
  end: DOM_NUM_NB)
