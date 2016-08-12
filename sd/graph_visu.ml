(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_visu.ml
 **       export graphs for visualization in the dot format for graphviz
 ** Francois Berenger and Huisong Li, started 2015/02/24 *)

open Data_structures
open Graph_sig
open Graph_utils
open Graph_visu_atom
open Graph_visu_common

module L  = BatList
module Pr = Printf

module Log =
  Logger.Make(struct let section = "gv______" and level = Log_level.DEBUG end)

let nodes_of_graph (g: graph): Graph_sig.node list =
  L.map snd (IntMap.bindings g.g_g)

let merge_int_sets (groups: IntSet.t list): IntSet.t =
  L.fold_left IntSet.union IntSet.empty groups

let connected_components (g: graph): IntSet.t list =
  let is_linked_to (n: node) (group: IntSet.t): bool =
    if IntSet.mem n.n_i group then true (* n is in the group *)
    else
      IntSet.exists (* or one of its successors is *)
        (fun s -> IntSet.mem s group) (Node.successors n) in
  let rec loop (nodes: node list) (acc: IntSet.t list): IntSet.t list =
    match nodes with
    | [] -> acc
    | n :: ns ->
        let connected, not_connected = L.partition (is_linked_to n) acc in
        let new_acc = (merge_int_sets connected) :: not_connected in
        loop ns new_acc in
  let nodes = nodes_of_graph g in
  let init = L.map (fun n -> IntSet.singleton n.n_i) nodes in
  loop nodes init

(* remove from 'g' all leaves which are not inductive edges *)
let cut_ordinary_leaves (g: graph): graph =
  let rec loop (to_visit: IntSet.t) (visited: IntSet.t) (acc: IntSet.t) =
    if IntSet.is_empty to_visit then
      acc
    else
      let curr, remaining = IntSet.pop_min to_visit in
      let curr = get_node curr g in
      let nexts = Node.successors curr in
      let nexts = IntSet.filter (fun n -> not (IntSet.mem n visited)) nexts in
      let to_visit' = IntSet.union nexts remaining in
      let visited' = IntSet.add curr.n_i visited in
      let acc' =
        if Node.is_leaf curr then acc
        else IntSet.add curr.n_i acc in
      loop to_visit' visited' acc' in
  let all_nodes = get_all_nodes g in
  let interesting_nodes = loop all_nodes IntSet.empty IntSet.empty in
  let new_map =
    IntMap.filter (fun k _v -> IntSet.mem k interesting_nodes) g.g_g in
  { g with g_g = new_map }

(* pretty print graph out in .dot format for the
 * graphviz tools (dot, dotty, etc.) *)
let pp_all_graph
    (title: string) (g: graph) (namer: namer) (out: out_channel)
  : unit =
  let nodes = nodes_of_graph g in
  let edges = L.map Edge.of_node nodes in
  let offsets = Edge.list_offsets edges in
  (* graph header *)
  Pr.fprintf out
    ("digraph g {\n" ^^
     "// title\n" ^^
     "labelloc=\"t\";\n" ^^
     "label=\"%s\";\n") title;
  Pr.fprintf out "graph [ rankdir = \"LR\" ];\n";
  (* nodes *)
  L.iter
    (fun n ->
      let node = Node.create n namer offsets in
      Pr.fprintf out "%s" (Node.to_string IntSet.empty node)
    ) nodes;
  (* edges *)
  L.iter (fun e -> Pr.fprintf out "%s" (Edge.to_string e g.g_g)) edges;
  Pr.fprintf out "}\n" (* end of digraph *)

(* pretty print only 'interesting_nodes' from 'g' *)
let pp_pruned_graph
    (title: string)
    (interesting_nodes: IntSet.t)
    (g: graph)
    (namer: namer)
    (out: out_channel): unit =
  let interesting_graph = filter_nodes interesting_nodes g in
  (* call pp_graph on the graph with an updated list of nodes *)
  pp_all_graph title interesting_graph namer out

(* graph pruned using the connected component criterion *)
let pp_pruned_graph_cc (title: string) (vars_to_keep: StringSet.t)
    (g: graph) (namer: namer) (out: out_channel): unit =
  let components = connected_components g in
  (* keep only connected components which have at least one node *)
  (* we are interested into *)
  let interesting_components =
    L.filter
      (fun c ->
        IntSet.exists
          (fun i ->
            let name = get_name namer i in
            StringSet.mem name vars_to_keep
          ) c
      ) components in
  let interesting_nodes = merge_int_sets interesting_components in
  pp_pruned_graph title interesting_nodes g namer out

(* graph pruned using the 'successors of' criterion *)
let pp_pruned_graph_succ
    (title: string)
    (root_vars: StringSet.t)
    (g: graph)
    (namer: namer)
    (out: out_channel): unit =
  let interesting_nodes = successors_only root_vars g namer in
  pp_pruned_graph title interesting_nodes g namer out

(* 'vars' is a list of variables (their names) that you want to keep in
 * the output graph; if 'vars' is empty: all nodes of the graph are kept *)
let pp_graph
    (title: string)
    (vars: string list)
    (opts: visu_option list)
    (g: graph)
    (namer: namer)
    (out: out_channel): unit =
  let cc_mode = L.mem Connex_component opts in
  let succ_mode = L.mem Successors opts in
  let cut_leaves_mode = L.mem Cut_leaves opts in
  let g =
    if cut_leaves_mode then cut_ordinary_leaves g
    else g in
  if vars = [] then
    begin
      if cc_mode then Log.warn "pp_graph: CC ignored";
      if succ_mode then Log.warn "pp_graph: SUCC ignored";
      pp_all_graph title g namer out
    end
  else
    let f =
      match cc_mode, succ_mode with
      | false, false -> failwith "pp_graph: use either CC or SUCC"
      | true , true  -> assert(false) (* case filtered out earlier *)
      | true , false -> pp_pruned_graph_cc
      | false, true  -> pp_pruned_graph_succ in
    let var_set = StringSet.of_list vars in
    f title var_set g namer out
