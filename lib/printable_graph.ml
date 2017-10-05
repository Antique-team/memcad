(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: printable_graph.ml
 **       Graph meant to be printed out
 ** Francois Berenger, 2016/11/16 *)

open Data_structures
open Sv_sig

module Node = struct
  type kind = Plain | Ind_start | Seg_start

  type t = { id:        int; (* nid *)
             name:      string;
             kind:      kind;
             nb_fields: int;
             typ:       ntyp }

  let create id name kind nb_fields typ: t =
    begin
      match kind with
      | Ind_start | Seg_start -> assert (nb_fields = 1)
      | _ -> ()
    end;
    { id; name; kind; nb_fields; typ }

  (* graphviz dot format string output *)
  let to_dot_string (node: t): string =
    let maybe_bold =
      match node.kind with
      | Ind_start -> "fontname=\"bold\" style=\"bold\""
      | _ -> "" in
    let ntype_str = Ind_utils.ntyp_2str_short node.typ in
    let label = Printf.sprintf "<f0> %s %s" node.name ntype_str in
    let fields =
      let res = ref label in
      for i = 1 to node.nb_fields - 1 do
        (* fields are assumed a 32 bits size (4 bytes) *)
        res := !res ^ (Printf.sprintf " | <f%d> +%d" (4*i) (4*i))
      done;
      !res in
    Printf.sprintf "\"%d\" [%s label=\"%s\" shape=\"record\"];\n"
      node.id maybe_bold fields
end

module Edge =
  struct
    type kind =
      | Simple
      | Segment

    type t =
        { src_nid: int; (* source nid *)
          src_off: int; (* offset in source node *)
          dst_nid: int; (* destination nid *)
          dst_off: int; (* offset in destination node *)
          label: string;
          kind: kind }

    let create src_nid src_off dst_nid dst_off label kind: t =
      { src_nid; src_off; dst_nid; dst_off; label; kind }

    (* graphviz dot format string output *)
    let to_dot_string (edge: t): string =
      Printf.sprintf "\"%d\":f%d -> \"%d\":f%d [ label = \"%s\" ];\n"
        edge.src_nid edge.src_off edge.dst_nid edge.dst_off edge.label
  end

module Graph =
  struct

    open Node
    open Edge

    type t =
        { nodes: Node.t list; (* all nodes *)
          edges: Edge.t list; (* all edges *)
          title: string }

    let create nodes edges title =
      { nodes; edges; title }

        (* graphviz dot format string output *)
    let to_dot_string (graph: t): string =
      let buff = Buffer.create 80 in
      (* header *)
      Buffer.add_string buff "digraph g {\n";
      Buffer.add_string buff "labelloc=\"t\";\n";
      Buffer.add_string buff (Printf.sprintf "label=\"%s\";\n" graph.title);
      Buffer.add_string buff "graph [ rankdir = \"LR\" ];\n";
      (* nodes *)
      List.iter
        (fun n -> Buffer.add_string buff (Node.to_dot_string n)) graph.nodes;
      (* edges *)
      List.iter
        (fun e -> Buffer.add_string buff (Edge.to_dot_string e)) graph.edges;
      (* footer *)
      Buffer.add_string buff "}\n"; (* end of digraph *)
      Buffer.contents buff

    (* all node ids directly connected to 'nid' *)
    let direct_successors (nid: int) (graph: t): IntSet.t =
      List.fold_left (fun acc edge ->
        if edge.src_nid = nid then
          IntSet.add edge.dst_nid acc
        else
          acc
                     ) IntSet.empty graph.edges

    (* list all connected components of 'g' *)
    let connected_components (graph: t): IntSet.t list =
      let all_edges = graph.edges in
      let is_connected s1 s2 =
        IntSet.inter s1 s2 <> IntSet.empty in
      let may_merge s1 s2 =
        if is_connected s1 s2 then
          IntSet.union s1 s2
        else
          s2 in
      let rec loop = function
        | [] -> []
        | x :: xs ->
            if List.exists (is_connected x) xs then
              loop (List.map (may_merge x) xs)
            else
              x :: loop xs in
      let init =
        List.fold_left (fun acc edge ->
          (IntSet.of_list [edge.src_nid; edge.dst_nid]) :: acc
                       ) [] all_edges in
      loop init

    let filter_nodes nodes nids_to_keep =
      List.filter (fun node ->
        IntSet.mem node.id nids_to_keep
                  ) nodes

    let neg_filter_nodes nodes nids_to_discard =
      List.filter (fun node ->
        not (IntSet.mem node.id nids_to_discard)
                  ) nodes

    let filter_edges edges nids_to_keep =
      List.filter (fun edge ->
        IntSet.mem edge.src_nid nids_to_keep &&
        IntSet.mem edge.dst_nid nids_to_keep
                  ) edges

    let connected_component (roots: IntSet.t) (graph: t): t =
      let comps = connected_components graph in
      let selected_comps =
        List.filter (fun comp ->
          IntSet.inter roots comp <> IntSet.empty
                    ) comps in
      let all_nodes = graph.nodes in
      let all_edges = graph.edges in
      let nids_to_keep =
        List.fold_left IntSet.union IntSet.empty selected_comps in
      let remaining_nodes = filter_nodes all_nodes nids_to_keep in
      let remaining_edges = filter_edges all_edges nids_to_keep in
      create remaining_nodes remaining_edges graph.title

    (* return a new graph where nodes which are not descendants
     * of any of 'root_vars' were removed *)
    let successors_only (roots: IntSet.t) (graph: t): t =
      let all_nodes = graph.nodes in
      let all_edges = graph.edges in
      let rec loop to_visit visited =
        if IntSet.is_empty to_visit then visited
        else
          let curr, remaining = IntSet.pop_min to_visit in
          let nexts = direct_successors curr graph in
          let to_visit' = IntSet.diff (IntSet.union remaining nexts) visited in
          let visited' = IntSet.add curr visited in
          loop to_visit' visited' in
      let nids_to_keep = loop roots IntSet.empty in
      let remaining_nodes = filter_nodes all_nodes nids_to_keep in
      let remaining_edges = filter_edges all_edges nids_to_keep in
      create remaining_nodes remaining_edges graph.title

    (* remove from 'graph' all leaves which are not inductive edges *)
    let cut_ordinary_leaves (graph: t): t =
      let all_nodes = graph.nodes in
      let all_edges = graph.edges in
      let all_nids =
        IntSet.of_list
          (List.map (fun node -> node.id) all_nodes) in
      let nid2node =
        List.fold_left (fun acc node ->
          IntMap.add node.id node acc
                       ) IntMap.empty all_nodes in
      let edge_start_nids =
        IntSet.of_list
          (List.map (fun edge -> edge.src_nid) graph.edges) in
      let all_leaves = IntSet.diff all_nids edge_start_nids in
      let nids_to_remove =
        IntSet.filter (fun nid ->
          let node = IntMap.find nid nid2node in
          node.kind = Node.Plain
                      ) all_leaves in
      let remaining_nodes = neg_filter_nodes all_nodes nids_to_remove in
      let remaining_edges =
        List.filter (fun edge ->
          not (IntSet.mem edge.dst_nid nids_to_remove)
                    ) all_edges in
      create remaining_nodes remaining_edges graph.title
  end
