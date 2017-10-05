(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_encode.mli
 **       basic modules for graphs and encoded graphs output
 ** Francois Berenger and Huisong Li, started 2015/02/24 *)

open Data_structures
open Graph_sig
open Graph_utils
open Graph_visu_sig
open Ind_utils
open Ind_sig
open Sv_sig

module L  = BatList
module Pr = Printf

module Log =
  Logger.Make(struct let section = "gv_atom_" and level = Log_level.DEBUG end)

module Edge : EDGE =
struct
  (* types of edges are describbed in graph_sig.ml *)
  type args =
    nid list * nid list * nid list
  type t =
    | Empty of nid (* nid = node id *)
    | Inductive of string * nid * args (* (ind_name, nid, ind_args) *)
    (* (ind_name, src_nid, src_args, src_offsets, dst_nid, dst_args) *)
    | Segment of string * nid * args * Offs.OffSet.t * nid * args
    (* (src_node, src_offset, dst_node, dst_offset) *)
    | Points_to of (nid * Offs.t * nid * Offs.t) list

  let extract_arg (arg: ind_args): args =
    arg.ia_ptr, arg.ia_int, arg.ia_set

  let extract_ind_args ind =
    extract_arg ind.ie_args

  let extract_seg_args seg =
    (extract_arg seg.se_sargs, extract_arg seg.se_dargs)

  let of_node (src: node): t =
    let src_node = src.n_i in
    (* process its outgoing edges *)
    match src.n_e with
    | Hemp     -> Empty src_node
    | Hind ind -> Inductive (ind.ie_ind.i_name, src_node, extract_ind_args ind)
    | Hseg seg ->
        let dst_node = seg.se_dnode in
        let seg_ind = seg.se_ind in
        let ind_name = seg_ind.i_name in
        let src_args, dst_args = extract_seg_args seg in
        (* currently in memcad: a segment is only between nodes with
         * the same inductive definition. So we use the more restricted
         * ind.i_self_dirs here instead of ind.i_dirs.
         * This will prevent segments from being extended (offsets
         * at extremities being folded into the segment) too much
         * during join of paths. *)
        let ind_offsets = seg_ind.i_may_self_dirs in
        Segment (ind_name, src_node, src_args, ind_offsets, dst_node, dst_args)
    | Hpt block_frag ->
        let edges =
          (* src offs to dest node and offs *)
          let src_to_dst = Block_frag.map_to_list block_frag in
          let res =
            L.map
              (fun (src_bound, dst_pt_edge) ->
                let src_offs = Bounds.to_offs src_bound in
                let dst_node, dst_offs = (Block_frag.elt dst_pt_edge).pe_dest in
                (src_node, src_offs, dst_node, dst_offs)
              ) src_to_dst in
          if !Flags.no_ind_prev_fields then
            (* filter out backward edges flagged as such by the ind. def. *)
            match ind_of_node src with
            | None -> res (* node not result of past unfolding *)
            | Some ind_name ->
                let ind = ind_find ind_name in
                let prev_fields = ind.i_pr_offs in
                L.filter
                  (fun (_src_node, src_off, _dst_node, _dst_off) ->
                    not (Offs.OffSet.mem src_off prev_fields)
                  ) res
          else
            res in
        Points_to edges

  (* list useful offsets of each node, based on the list of edges,
     so that we can create nodes with only their needed offsets *)
  let list_offsets (edges: t list): IntSet.t IntMap.t =
    let record_offset (k: nid) (v: Offs.t) (m: IntSet.t IntMap.t) =
      let int_offs = Offs.to_int v in
      let map_replace k v m =
        IntMap.add k v (IntMap.remove k m) in
      try
        let prev_set = IntMap.find k m in
        let new_set = IntSet.add int_offs prev_set in
        map_replace k new_set m
      with
      | Not_found -> IntMap.add k (IntSet.singleton int_offs) m in
    L.fold_left
      (fun acc edge ->
        match edge with
        | Empty _ | Inductive _ -> acc
        | Segment (_ind_name, src_nid, _, offsets, _dst_nid, _) ->
            Offs.OffSet.fold (fun off acc2 -> record_offset src_nid off acc2)
              offsets acc
        | Points_to pt_edges ->
            L.fold_left
              (fun acc (src_nid, src_offs, dst_nid, dst_offs) ->
                record_offset src_nid src_offs
                  (record_offset dst_nid dst_offs acc)
              ) acc pt_edges
      ) IntMap.empty edges

  (* allowed_dest_nodes is used for pruning:
   * only edges with a destination in 'allowed_dest_nodes' are converted *)
  let to_string (n: t) (allowed_dest_nodes: node IntMap.t): string =
    let arg_2str args =
      let pa, ia, sa = args in
      (Lib.intlist_2str pa)^"|"^
      (Lib.intlist_2str ia)^"|"^
      (Lib.intlist_2str sa) in
    match n with
    | Empty nid -> ""
          (* (\* if you want a dummy reflexive edge instead: *\) *)
          (* Pr.sprintf "\"%d\" -> \"%d\" [ label = \"emp\" ];\n" *)
          (*   nid nid *)
    | Points_to src_dst_list ->
        let res = ref "" in
        L.iter
          (fun (src_nid, src_offs, dst_nid, dst_offs) ->
            if IntMap.mem dst_nid allowed_dest_nodes then
              let src_off = Offs.to_int src_offs in
              let dst_off = Offs.to_int dst_offs in
              res := !res ^
                     (Pr.sprintf "\"%d\":f%d -> \"%d\":f%d;\n"
                        src_nid src_off dst_nid dst_off)
          ) src_dst_list;
        !res
    | Inductive (_name, _nid, _args) ->
        ""
    | Segment (ind_name, src_nid, src_args, _offsets, dst_nid, dst_args) ->
        if IntMap.mem dst_nid allowed_dest_nodes then
          Pr.sprintf "\"%d\":f0 -> \"%d\":f0 [ label = \"%s %s %s\" ];\n"
            src_nid dst_nid
            (arg_2str src_args) ind_name (arg_2str dst_args)
        else
          ""
end

module Node : NODE =
struct
  type t = { id:      nid      ;
             name:    string   ;
             typ:     ntyp     ; (* node type *)
             alloc:   nalloc   ; (* node allocation type *)
             offsets: IntSet.t ; (* edges src/dest from/to that node *)
             node:    node     } (* corresponding graph node *)

  let get_name_uid (namer: namer) (id: int): string =
    try
      let name, uid = namer id in
      Pr.sprintf "%s.%d" name uid
    with Not_found -> "_"

  let create (n: node) (namer: namer) (offsets: IntSet.t IntMap.t): t =
    let id = n.n_i in
    let name = get_name_uid namer id in
    let typ = n.n_t in
    let alloc = n.n_alloc in
    let offsets =
      try IntMap.find id offsets
      with Not_found -> IntSet.singleton 0 in
    let node = n in
    { id; name; typ; alloc; offsets; node }

  let is_leaf (n: node): bool =
    match Edge.of_node n with
    | Edge.Empty _ -> true
    | _ -> false

  (* set of node ids that you can reach from this node *)
  let successors (n: node): IntSet.t =
    match Edge.of_node n with
    | Edge.Empty _
    | Edge.Inductive _ -> IntSet.empty
    | Edge.Segment (_ind_name, _src_nid, _src_args,
                    _offsets, dst_nid, _dst_args) ->
        IntSet.singleton dst_nid
    | Edge.Points_to src_dsts ->
        L.fold_left
          (fun acc (_src_nid, _, dst_nid, _) -> IntSet.add dst_nid acc)
          IntSet.empty src_dsts

  (* same as successors but keeping source node offset followed *)
  let successors_offs (n: node): (step * int) list =
    match Edge.of_node n with
    | Edge.Empty _ | Edge.Inductive _ -> []
    | Edge.Segment (ind_name, _src_nid, _src_args,
                    src_offs, dst_nid, _dst_args) ->
        let offsets = Offs.OffSet.elements src_offs in
        [ Segment (ind_name, offsets), dst_nid ]
    | Edge.Points_to src_dsts ->
        L.map
          (fun (_src_nid, src_off, dst_nid, _dst_offs) ->
            (Offset src_off, dst_nid)
          ) src_dsts

  (* is node 'n' the source of an inductive edge ? *)
  let is_inductive_src (n: t): bool =
    match Edge.of_node n.node with
    | Edge.Inductive _ -> true
    | _ -> false

  (* is it OK to fold this node *)
  let can_fold (n: node): bool =
    (* not on the stack *)
    n.n_alloc <> Nstack &&
    n.n_alloc <> Nstatic &&
    (* only one outgoing edge *)
    (match Edge.of_node n with
     | Edge.Empty _ | Edge.Inductive _ | Edge.Segment _   -> true
     | Edge.Points_to src_dsts -> List.length src_dsts = 1)

  let to_string (selected_vars: IntSet.t) (node: t): string =
    let arg_2str args =
      let pa, ia, sa = args in
      (Lib.intlist_2str pa)^"|"^
      (Lib.intlist_2str ia)^"|"^
      (Lib.intlist_2str sa) in
    let label_str =
      IntSet.fold
        (fun offset acc ->
          let str =
            if offset <> 0 then
              acc ^ (Pr.sprintf " | <f%d> +%d" offset offset)
            else
              let nalloc_str = nalloc_2str_short node.alloc in
              let ntype_str = ntyp_2str_short node.typ in
              let ntype_str =
                if can_fold node.node then ntype_str ^ " f"
                else ntype_str in
              if nalloc_str = "" then
                Pr.sprintf "<f0> %d=%s: %s" node.id node.name ntype_str
              else
                Pr.sprintf "<f0> %d=%s: %s %s"
                  node.id node.name nalloc_str ntype_str in
          match Edge.of_node node.node with
          | Edge.Inductive (ind_name, _ind, args) ->
              let args_str = arg_2str args in
              Pr.sprintf "%s %s(%s)\\=\\=\\>" str ind_name args_str
          | Edge.Empty _ -> str ^ " NULL"
          | _ -> str
        ) node.offsets "" in
    if is_inductive_src node || IntSet.mem node.id selected_vars then
      Pr.sprintf "\"%d\" [fontname=\"bold\" \
                  label=\"%s\" shape=\"record\" style=\"bold\"];\n"
        node.id label_str
    else
      Pr.sprintf "\"%d\" [label=\"%s\" shape=\"record\"];\n"
        node.id label_str
end
