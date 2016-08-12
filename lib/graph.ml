(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph.ml
 **       graphs over arbitrary keys
 ** Xavier Rival, 2012/07/21 *)
open Data_structures

(** Error report (for module lib) *)
module Log = Logger.Make(struct let section = "graph___" and level = Log_level.DEBUG end)

let debug = true

(** Signature of the graph functor *)
module type GRAPH =
  sig
    type key
    type set
    type t
    (* Empty *)
    val empty: t
    (* Addition of a node, if not already there *)
    val node_add: key -> t -> t
    (* Successors of a node *)
    val node_successors: key -> t -> set
    (* Addition of an edge *)
    val edge_add: key -> key -> t -> t
    (* Printer and to string with indentation *)
    val t_2stri: string -> t -> string
    (* Building from a list of edges *)
    val of_list: (key * key) list -> t
    (* Number of nodes *)
    val num_nodes: t -> int
    (* Tarjan *)
    val tarjan: t -> set list
  end

(** The graph functor *)
module Graph = functor (O: OrderedType) ->
  (struct
    type key = O.t
    module M = MapMake( O )
    module S = SetMake( O )
    type set = S.t
    type t = S.t M.t
    (* Empty *)
    let empty: t = M.empty
    (* Addition of a node, if not already there *)
    let node_add (n: key) (x: t): t =
      if M.mem n x then x
      else M.add n S.empty x
    (* Successors of a node *)
    let node_successors (pre: key) (x: t): S.t =
      try M.find pre x with Not_found -> S.empty
    (* Addition of an edge *)
    let edge_add (pre: key) (post: key) (x: t): t =
      let s = node_successors pre x in
      M.add pre (S.add post s) (node_add pre (node_add post x))
    (* Printer and to string with indentation *)
    let t_2stri (ind: string) (x: t): string =
      let elt_printer (i: key) (s: set): string =
        Printf.sprintf "%s%s => { %s }\n" ind (O.t_2str i) (S.t_2str "; " s) in
      M.fold
        (fun i s acc ->
          Printf.sprintf "%s%s" acc (elt_printer i s)
        ) x ""
    (* Building from a list of edges *)
    let of_list (l: (key * key) list): t =
      List.fold_left
        (fun acc (pre, post) ->
          edge_add pre post acc
        ) empty l
    (* Number of nodes *)
    let num_nodes (x: t): int = M.cardinal x
    (* Tarjan *)
    let tarjan (x: t): set list =
      let cnt: int ref = ref 0 in
      let index: int M.t ref = ref M.empty in
      let low: int M.t ref = ref M.empty in
      (* components maps each node to the least element of its scc *)
      let components: key M.t ref = ref M.empty in
      let lcomponents: set list ref = ref [ ] in
      let s: key Stack.t = Stack.create () in
      let mem (k: key): bool =
        let b = ref false in
        Stack.iter (fun kk -> if O.compare k kk = 0 then b := true) s;
        !b in
      let get_low (k: key): int =
        try M.find k !low with Not_found -> failwith "no low link" in
      let get_index (k: key): int =
        try M.find k !index with Not_found -> failwith "no index" in
      let set_low (k: key) (i: int): unit = low := M.add k i !low in
      let set_index (k: key) (i: int): unit = index := M.add k i !index in
      let rec strong_connect (v: key): unit =
        Log.info "strong_connect: %s" (O.t_2str v);
        let i = !cnt in
        set_index v i;
        set_low v i;
        Stack.push v s;
        incr cnt;
        let succ = node_successors v x in
        S.iter
          (fun w ->
            if not (M.mem w !index) then
              begin
                if debug then Log.info "rec-call: %s" (O.t_2str v);
                strong_connect w;
                set_low v (min (get_low v) (get_low w));
              end
            else if mem w then
              set_low v (min (get_low v) (get_index w));
          ) succ;
        if get_low v = get_index v then (* found a component ! *)
          let w: key ref = ref (Stack.pop s) in
          let comp = ref (S.singleton !w) in
          while O.compare !w v != 0 do
            w := Stack.pop s;
            comp := S.add !w !comp
          done;
          if debug then 
            Log.info "found component: { %s }" (S.t_2str "; " !comp);
          let repr = S.min_elt !comp in
          S.iter (fun k -> components := M.add k repr !components) !comp;
          lcomponents := !comp :: !lcomponents
      in
      M.iter
        (fun k _ ->
          if not (M.mem k !index) then
            strong_connect k
        ) x;
      !lcomponents
  end: GRAPH
    with type key = O.t
    and  type set = SetMake( O ).t )


(** Construction *)
module IntGraph = Graph( IntOrd )
module StringGraph = Graph( StringOrd )
