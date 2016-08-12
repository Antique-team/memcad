(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_visu_common.ml
 **       functions common to graphs and encoded graphs output
 ** Francois Berenger and Huisong Li, started 2015/02/24 *)

open Data_structures
open Graph_sig
open Graph_utils
open Graph_visu_atom

let get_name (namer: namer) (id: int): string =
  try fst (namer id)
  with Not_found -> "_"

let successors_only
    (root_vars: StringSet.t)
    (g: graph)
    (namer: namer): IntSet.t =
  (* keep only nodes from 'g' which are successors (direct or not)
   * of nodes in 'vars' *)
  let descendants (g: graph) (vars: IntSet.t): IntSet.t =
    let rec loop to_visit visited =
      if IntSet.is_empty to_visit then
        visited
      else
        let curr, remaining = IntSet.pop_min to_visit in
        let nexts =
          try Node.successors (get_node curr g)
          with Not_found -> IntSet.empty in
        let to_visit' = IntSet.diff (IntSet.union remaining nexts) visited in
        let visited' = IntSet.add curr visited in
        loop to_visit' visited' in
    loop vars IntSet.empty in
  let root_nodes =
    IntMap.fold
      (fun k _v acc ->
         try
           let name = get_name namer k in
           if StringSet.mem name root_vars then IntSet.add k acc
           else acc
         with Not_found -> acc (* anonymous node *)
      ) g.g_g IntSet.empty in
  descendants g root_nodes

let filter_nodes (interesting_nodes: IntSet.t) (g: graph): graph =
  let new_map =
    IntMap.fold
      (fun k v acc ->
        if IntSet.mem k interesting_nodes then IntMap.add k v acc
        else acc
      ) g.g_g IntMap.empty in
  { g with g_g = new_map }
