(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_strategies.ml
 **       functions to discover strategies for other transfer functions
 ** Xavier Rival, 2012/02/23 *)
open Data_structures
open Graph_sig
open Graph_utils
open Ind_sig
open Lib

(** Error handling *)
module Log =
  Logger.Make(struct let section = "g_strats" and level = Log_level.DEBUG end)

(** Exception, to quickly stop a search with no positive answer *)
exception Stop


(** Extraction of inductives compatible with a points-to edge *)
let extract_compatible_inductives
    (is_seg: bool) (* whether we search for a segment (no emp case needed) *)
    (mcr: pt_edge Block_frag.t): ind StringMap.t =
  let check_pt_rule (r: irule): bool =
    try
      (* extract the points-to edges specified in the rule,
       * and see if they match with fragment mcr *)
      let rule_pts =
        List.filter (function Hacell _ -> true | _ -> false) r.ir_heap in
      if !Flags.flag_debug_gr_strat then
        Log.force "considering:\n%s\ntrying: %d - %d"
          (heap_frag_2stri "  " (-99) (Hpt mcr)) (List.length rule_pts)
          (Block_frag.cardinal mcr);
      let matched =
        List.fold_left
          (fun acc -> function
            | Hacell c ->
                begin
                  try
                    let pt =
                      Block_frag.find_addr (Bounds.of_offs c.ic_off) mcr in
                    if Offs.size_to_int_opt pt.pe_size = Some c.ic_size then
                      1 + acc
                    else raise Stop
                  with Not_found -> raise Stop
                end
            | Haind  _ -> acc
          ) 0 rule_pts in
      matched = Block_frag.cardinal mcr
    with
    | Stop -> false in
  StringMap.fold
    (fun name ind acc ->
      let b_pt =
        List.fold_left
          (fun acc r -> acc || check_pt_rule r) false ind.i_rules in
      let b_base =
        if is_seg then (* any inductive will approximate the empty segment *)
          true
        else (* there should be a rule yielding an empty heap *)
          List.exists (fun r -> r.ir_kind = Ik_empz) ind.i_rules in
      if !Flags.flag_debug_gr_strat then
        Log.force "Result for inductive %s: %b,%b" name b_pt b_base;
      if b_pt && b_base then StringMap.add name ind acc
      else acc
    ) !Ind_utils.ind_defs StringMap.empty


(** Search for possible segment directions *)
let extract_segment_directions_pt
    (src: int) (* starting nodes *)
    (nodes: IntSet.t) (* nodes that we consider *)
    (offs: Offs.OffSet.t)  (* set of offsets that can be used in traversal *)
    (g: graph): (int * int) list =
  let rec reach_from (seen: IntSet.t) (src: int): IntSet.t =
    if node_mem src g then
      match (node_find src g).n_e with
      | Hemp | Hind _ ->
          seen 
      | Hseg seg_edge -> 
          reach_from (IntSet.add seg_edge.se_dnode seen) seg_edge.se_dnode
      | Hpt mc ->
          if !Flags.flag_debug_gr_strat then Log.force "pt @ %d" src;
          Block_frag.fold_base
            (fun o p acc ->
              if Offs.OffSet.mem (Bounds.to_offs o) offs then
                let nxt = fst p.pe_dest in
                if !Flags.flag_debug_gr_strat then Log.force "+ %d" nxt;
                if IntSet.mem nxt seen then acc
                else reach_from (IntSet.add nxt acc) nxt
              else acc
            ) mc seen
    else seen in
  let reach =
    IntSet.remove src
      (IntSet.inter nodes (reach_from (IntSet.singleton src) src)) in
  IntSet.fold (fun j acc -> (src, j) :: acc) reach [ ]
let extract_segment_directions
    (nodes: IntSet.t) (* starting nodes *)
    (offs: Offs.OffSet.t)  (* set of offsets that can be used in traversal *)
    (g: graph): (int * int) list =
  IntSet.fold
    (fun src acc ->
      if node_mem src g then
        match (node_find src g).n_e with
        | Hpt  _ -> extract_segment_directions_pt src nodes offs g @ acc
        | Hseg se ->
            (* if IntSet.mem dst nodes then (src, dst) :: acc *)
            (* else acc *)
            (* XR: I do not understand this comment *)
            (* HS: this is only used for checking direction, it is
             * too strong to check the dst in nodes, so I delete the check,
             * actually, we need check the reach node*)
            extract_segment_directions_pt src nodes offs g @ acc
            (* (src, dst) :: acc *)
        | Hind _ | Hemp -> acc
      else acc
    ) nodes [ ]
