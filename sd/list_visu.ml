(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_visu.ml
 **       functions for graphical output of lists
 ** Francois Berenger, started 2016/08/24 *)

open Data_structures
open Graph_sig
open List_sig

module PGN = Printable_graph.Node
module PGE = Printable_graph.Edge
module PG = Printable_graph.Graph

module Log =
  Logger.Make(struct let section = "lv______" and level = Log_level.DEBUG end)

let get_name (namer: namer) (id: int): string =
  try
    let name = fst (namer id) in
    Printf.sprintf "%d=%s: " id name
  with Not_found -> (* anonymous var *)
    Printf.sprintf "%d=_: " id

let edges_of_ptedge_blockfrag pb =
  (* src offset to dest nid and offset *)
  let src_to_dst = Block_frag.map_to_list pb in
  List.map
    (fun (src_bound, dst_pt_edge) ->
       let src_off = Bounds.to_offs src_bound in
       let dst_nid, dst_off = (Block_frag.elt dst_pt_edge).pe_dest in
       (Offs.to_int src_off, dst_nid, Offs.to_int dst_off)
    ) src_to_dst

let string_of_listind (lc: l_call): string =
  let string_of_string_opt = function
    | None -> ""
    | Some s -> s in
  let ind_name = string_of_string_opt lc.lc_def.ld_name in
  match lc.lc_args with
  | [] -> ind_name
  | _ -> Printf.sprintf "%s %s" ind_name (List_utils.l_call_setvars_2str lc)

(* list all edges starting from that node *)
let edges_of_node (ln: lnode): PGE.t list =
  let src_nid = ln.ln_i in
  match ln.ln_e with
  | Lhemp
  | Lhlist _ -> []
  | Lhlseg (lc, dst_nid) ->
      [PGE.create src_nid 0 dst_nid 0 ("seg:" ^ (string_of_listind lc)) PGE.Segment]
  | Lhpt mc ->
      let dsts = edges_of_ptedge_blockfrag mc in
      List.map (fun (src_off, dst_nid, dst_off) ->
          PGE.create src_nid src_off dst_nid dst_off "" PGE.Simple
        ) dsts

let output_dot (options: visu_option list)
    (filename: string) (vars: string list) (mem: lmem) (namer: namer) (out: out_channel)
  : unit =
  let mem_nodes = List_utils.nodes_of_lmem mem in
  let nodes_and_edges =
    List.map (fun n ->
        let edges = edges_of_node n in
        let kind, nb_fields, suffix = match n.ln_e with
          | Lhemp -> (PGN.Plain, 1, "")
          | Lhpt _ -> (PGN.Plain, List.length edges, "")
          | Lhlist lc -> (PGN.Ind_start, 1, " ind:" ^ (string_of_listind lc))
          | Lhlseg (_, _) -> (PGN.Seg_start, 1, "")
        in
        (PGN.create n.ln_i ((get_name namer n.ln_i) ^ suffix) kind nb_fields n.ln_typ, edges)
      ) mem_nodes
  in
  let nodes = List.map fst nodes_and_edges in
  let all_nids = List.map (fun node -> PGN.(node.id)) nodes in
  let selected_vars = StringSet.of_list vars in
  let roots =
    List.filter
      (fun nid ->
        try
          let var_name, _ = namer nid in
          StringSet.mem var_name selected_vars
        with _ -> false
      ) all_nids in
  let roots = IntSet.of_list roots in
  let all_edges = List.map snd nodes_and_edges in
  let edges = List.flatten all_edges in
  let graph = PG.create nodes edges filename in
  let graph =
    if List.mem Cut_leaves options then
      PG.cut_ordinary_leaves graph
    else
      graph in
  if List.mem Successors options && List.mem Connex_component options then
    Log.fatal_exn "output_dot: SUCC and CC visu options are exclusive";
  let graph =
    if List.mem Successors options then
      PG.successors_only roots graph
    else if List.mem Connex_component options then
      PG.connected_component roots graph
    else
      graph in
  Printf.fprintf out "%s" (PG.to_dot_string graph)
