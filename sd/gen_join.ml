(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: gen_join.ml
 **       Generic elements used in the join algorithm
 ** Xavier Rival, 2014/03/04 *)
open Data_structures
open Lib

open Gen_dom

open Graph_sig
open Nd_sig

open Graph_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "gen_join" and level = Log_level.DEBUG end)

(** Kinds of rules in the join algorithm *)
type rkind =
  | Rpp | Rii         (* matching of pairs of pt/inductive edges *)
  | Rsegintro of side (* introduction of a segment *)
  | Rsegext           (* extension of a segment *)
  | Riweak            (* inductive in the left; weaken in the right graph *)
  | Rweaki            (* inductive in the right; weaken in the left graph *)
  | Rindintro         (* introduction of an inductive *)
  | Rsplitind of side (* seperate an inductive edge by introducing a segment *)
  | Rsegext_ext       (* extension of segments on both sides *)

(** Status, with set of applicable rules *)
type instances = PairSet.t
type rules =
    { (** Classical rules of separation logic with inductives *)
      r_pt_prio:    instances; (* prioretary points-to edges *)
      r_pt_pt:      instances; (* matching a pair of points-to edges *)
      r_ind_ind:    instances; (* matching a pair of inductive edges *)
      r_weak_ind:   instances; (* weaken into an inductive (left) *)
      r_ind_weak:   instances; (* weaken into an inductive (right) *)
      r_segintro_l: instances; (* introduction of a segment (left is empty) *)
      r_segintro_r: instances; (* introduction of a segment (right is empty) *)
      r_segext:     instances; (* extension of a segment *)
      r_indintro:   instances; (* introduction of an inductive *)
      (** Rules based on more global rewrittings of formulas *)
      (* split an inductive edge to a segment and inductive edge
       * (right is empty) *)
      r_splitind_l: instances;
      (* split an inductive edge to a segment and inductive edge
       * (left is empty) *)
      r_splitind_r: instances;
      (* extension of segments on both sides *)
      r_segext_ext: instances }

(** Utilities and Pretty-printing *)
(* Emmpty set of rules *)
let empty_rules = { r_pt_prio    = PairSet.empty ;
                    r_pt_pt      = PairSet.empty ;
                    r_ind_ind    = PairSet.empty ;
                    r_weak_ind   = PairSet.empty ;
                    r_ind_weak   = PairSet.empty ;
                    r_segintro_l = PairSet.empty ;
                    r_segintro_r = PairSet.empty ;
                    r_segext     = PairSet.empty ;
                    r_indintro   = PairSet.empty ;
                    r_splitind_l = PairSet.empty ;
                    r_splitind_r = PairSet.empty ;
                    r_segext_ext = PairSet.empty ; }
(* Pretty-printing *)
let kind_2str: rkind -> string = function
  | Rpp         -> "pt-pt"
  | Rii         -> "ind-ind"
  | Rsegintro s -> if s = Lft then "seg-intro-l" else "seg-intro-r"
  | Rsegext     -> "seg-ext"
  | Riweak      -> "ind-weak"
  | Rweaki      -> "weak-ind"
  | Rindintro   -> "ind-intro"
  | Rsplitind s   -> if s = Lft then "sep-ind-l" else "sep-ind-r"
  | Rsegext_ext -> "seg_ext_ext"
let rules_2str (r: rules): string =
  let instances_2str (name: string) (s: PairSet.t): string =
    if s != PairSet.empty then
      Printf.sprintf "%s %s\n" name (pairset_2str s)
    else "" in
  (instances_2str "pt-prio:     " r.r_pt_prio)
  ^ (instances_2str "pt-pt:       " r.r_pt_pt)
  ^ (instances_2str "ind-ind:     " r.r_ind_ind)
  ^ (instances_2str "weak-ind:    " r.r_weak_ind)
  ^ (instances_2str "ind-weak:    " r.r_ind_weak)
  ^ (instances_2str "seg-intro-l: " r.r_segintro_l)
  ^ (instances_2str "seg-intro-r: " r.r_segintro_r)
  ^ (instances_2str "seg-ext:     " r.r_segext)
  ^ (instances_2str "ind-intro:   " r.r_indintro)
  ^ (instances_2str "split-ind-l: " r.r_splitind_l)
  ^ (instances_2str "split-ind-r: " r.r_splitind_r)
  ^ (instances_2str "seg_ext_ext: " r.r_segext_ext)

(** Strategy function, returning the next applicable rule *)
(* current strategy:
 *  1. pt-prio
 *  2. segext_ext
 *  3. ind-ind
 *  4. seg-intro-l
 *     seg-intro-r
 *  5. seg-ext
 *  6. weak-ind
 *     ind-weak
 *  7. pt-pt
 *  8. ind-intro
 *  9. splitind_l
 *     splitind_r *)
let rules_next (r: rules): (rkind * (int * int) * rules) option =
  if r.r_pt_prio != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_prio in
    Some (Rpp, p,
          { r with r_pt_prio = PairSet.remove p r.r_pt_prio })
  else if r.r_segext_ext != PairSet.empty then
    (* used to be after ind-ind and seg-intro *)
    let p = PairSet.min_elt r.r_segext_ext in
    Some (Rsegext_ext, p,
          { r with r_segext_ext = PairSet.remove p r.r_segext_ext })
  else if r.r_ind_ind != PairSet.empty then
    let p = PairSet.min_elt r.r_ind_ind in
    Some (Rii, p,
          { r with r_ind_ind = PairSet.remove p r.r_ind_ind })
  else if r.r_segintro_l != PairSet.empty then
    let p = PairSet.min_elt r.r_segintro_l in
    Some (Rsegintro Lft, p,
          { r with r_segintro_l = PairSet.remove p r.r_segintro_l })
  else if r.r_segintro_r != PairSet.empty then
    (* introduction of a segment from empty region in the right graph:
     * this may not be the right place for this rule *)
    let p = PairSet.min_elt r.r_segintro_r in
    Some (Rsegintro Rgh, p,
          { r with r_segintro_r = PairSet.remove p r.r_segintro_r })
  else if r.r_segext != PairSet.empty then
    let p = PairSet.min_elt r.r_segext in
    Some (Rsegext, p,
          { r with r_segext = PairSet.remove p r.r_segext })
  else if r.r_ind_weak != PairSet.empty then
    let p = PairSet.min_elt r.r_ind_weak in
    Some (Riweak, p,
          { r with r_ind_weak = PairSet.remove p r.r_ind_weak })
  else if r.r_weak_ind != PairSet.empty then
    let p = PairSet.min_elt r.r_weak_ind in
    Some (Rweaki, p,
          { r with r_weak_ind = PairSet.remove p r.r_weak_ind })
  else if r.r_pt_pt != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_pt in
    Some (Rpp, p,
          { r with r_pt_pt = PairSet.remove p r.r_pt_pt })
  else if r.r_indintro != PairSet.empty then
    let p = PairSet.min_elt r.r_indintro in
    Some (Rindintro, p,
          { r with r_indintro = PairSet.remove p r.r_indintro })
  else if r.r_splitind_l != PairSet.empty then
    let p = PairSet.min_elt r.r_splitind_l in
    Some (Rsplitind Lft, p,
          { r with r_splitind_l = PairSet.remove p r.r_splitind_l })
  else if r.r_splitind_r != PairSet.empty then
    let p = PairSet.min_elt r.r_splitind_r in
    Some (Rsplitind Rgh, p,
          { r with r_splitind_r = PairSet.remove p r.r_splitind_r })
  else None

(** Collecting applicable rules *)
let collect_rules_sv_gen
    (is_prio: int * int -> bool) (* whether pt rules are prioritary (init) *)
    (is_seg: bool)  (* whether candidate for extension as segments *)
    (is_seg_intro: bool)         (* whether seg intro *)
    (jrel: node_relation)        (* node relation *)
    (il: int) (kl: region_kind)  (* left node  *)
    (ir: int) (kr: region_kind)  (* right node *)
    (jr: rules): rules =
  if !Flags.flag_debug_join_strategy then
    Log.force "searching for rules at %d,%d" il ir;
  (* Searching for siblings (only in the right graph) *)
  let detect_siblings (sd: side) (i: int) (jr: rules): rules =
    let sib = Nrel.siblings sd i jrel in
    if !Flags.flag_debug_join_shape then
      Log.force "Siblings %s at %d (%d)[%b]: %s"
        (Graph_algos.side_2str sd) i (IntSet.cardinal sib)
        (IntSet.cardinal sib > 1) (IntSet.t_2str "; " sib);
    if IntSet.cardinal sib > 1 then
      match sd with
      | Lft ->
          let l =
            IntSet.fold (fun j -> PairSet.add (i, j)) sib jr.r_segintro_l in
          { jr with r_segintro_l = l }
      | Rgh ->
          let l =
            IntSet.fold (fun j -> PairSet.add (j, i)) sib jr.r_segintro_r in
          { jr with r_segintro_r = l }
    else jr in
  if is_seg then
    { jr with r_segext_ext = PairSet.add (il, ir) jr.r_segext_ext }
  else
    let jr = detect_siblings Lft il jr in
    let jr = detect_siblings Rgh ir jr in
    (* Regular rules *)
    let nrules =
      match kl, kr with
      (* empty nodes, no rule to add *)
      | Kemp, Kemp -> jr
      (* usual atomic rules *)
      | Kpt , Kpt  ->
          if is_prio (il, ir) && not is_seg_intro then
            { jr with r_pt_prio = PairSet.add (il, ir) jr.r_pt_prio }
          else
            { jr with r_pt_pt = PairSet.add (il, ir) jr.r_pt_pt }
      | Kind, Kind ->
          { jr with r_ind_ind = PairSet.add (il, ir) jr.r_ind_ind }
      | Kemp, Kind
      | Kpt , Kind ->
          { jr with r_weak_ind = PairSet.add (il, ir) jr.r_weak_ind }
      | Kind, Kemp
      | Kind, Kpt  ->
          { jr with r_ind_weak = PairSet.add (il, ir) jr.r_ind_weak }
      | Kseg, Kseg
      | Kseg, Kpt 
      | Kpt , Kseg ->
          { jr with r_segext = PairSet.add (il, ir) jr.r_segext }
      (* cases with no rule to add, no relevant weakening;
       * those edges may get discared due to siblings (other nodes in
       * relation with the same nodes) *)
      | Kemp, Kpt 
      | Kpt, Kemp ->
          { jr with r_indintro = PairSet.add (il, ir) jr.r_indintro }
      | Kemp, Kseg
      | Kseg, Kemp ->
          if !Flags.flag_debug_join_strategy then
            Log.force "cancelling seg-emp";
          jr
      | Kind, Kseg ->
          { jr with r_ind_weak = PairSet.add (il, ir) jr.r_ind_weak }
      | Kseg, Kind ->
          { jr with r_weak_ind = PairSet.add (il, ir) jr.r_weak_ind } in
    nrules

(** Invalidation of rules that were performed or disabled, by the application
 ** of another rule *)
(* Kinds of elements to invalidate *)
type invalid =
  | Ipt                (* a points to region *)
  | Iind               (* an inductive predicate *)
  | Inone              (* nothing *)
  | Iblob of IntSet.t  (* a memory blob *)
  | Isiblings          (* siblings of a node *)
(* Case of a local rule *)
let invalidate_rules
    (isl: nid) (isr: nid)
    (invl: invalid) (invr: invalid) (r: rules): rules =
  (* Map over the rules type *)
  let map_rules (f: string -> PairSet.t -> PairSet.t) (r: rules): rules =
    { r_pt_prio    = f "pt-prio"   r.r_pt_prio;
      r_pt_pt      = f "pt-pt"     r.r_pt_pt;
      r_ind_ind    = f "ind-ind"   r.r_ind_ind;
      r_weak_ind   = f "wk-ind"    r.r_weak_ind;
      r_ind_weak   = f "ind-wk"    r.r_ind_weak;
      r_segintro_l = r.r_segintro_l; (* no invalidate on seg-intro *)
      r_segintro_r = r.r_segintro_r; (* no invalidate on seg-intro *)
      r_segext     = f "seg-ext"   r.r_segext;
      r_indintro   = f "ind-intro" r.r_indintro;
      r_splitind_l = r.r_splitind_l; (* no invalidate in sep-ind *)
      r_splitind_r = r.r_splitind_r; (* no invalidate in sep-ind *)
      r_segext_ext = f "segext-ext" r.r_segext_ext } in
  (* Invalidate rules over a set *)
  let invalidate (il, ir) (msg: string) (s: PairSet.t): PairSet.t =
    if !Flags.flag_debug_join_strategy then
      Log.force "invalidating %s join rule at (%d,%d)" msg il ir;
    PairSet.remove (il, ir) s in
  let invalidate_map
      (f: (int * int) -> bool) (msg: string) (s: PairSet.t): PairSet.t =
    PairSet.fold
      (fun p acc ->
        if f p then invalidate p msg acc
        else acc
      ) s s in
  (* Rules consuming *one* node in each side *)
  let invalidate_l  = invalidate_map (fun (x, _) -> x = isl)
  and invalidate_r  = invalidate_map (fun (_, y) -> y = isr)
  and invalidate_lr = invalidate_map (fun (x, y) -> x = isl || y = isr) in
  (* Rules consuming a blob in one side *)
  let invalidate_nb (s: IntSet.t) =
    map_rules (invalidate_map (fun (_, y) -> IntSet.mem y s)) in
  let invalidate_bn (s: IntSet.t) =
    map_rules (invalidate_map (fun (x, _) -> IntSet.mem x s)) in
  let invalidate_bb (sl: IntSet.t) (sr: IntSet.t) =
    map_rules
      (invalidate_map (fun (x, y) -> IntSet.mem x sl || IntSet.mem y sr)) in
  match invl, invr with
  | Ipt, Ipt ->
      { r with
        r_pt_prio = invalidate_lr "a" r.r_pt_prio;
        r_pt_pt   = invalidate_lr "b" r.r_pt_pt }
  | Iind, Iind ->
      { r with
        r_ind_ind  = invalidate_lr "c" r.r_ind_ind;
        r_weak_ind = invalidate_r  "d" r.r_weak_ind;
        r_ind_weak = invalidate_l  "e" r.r_ind_weak }
  | Inone   , Iblob br -> invalidate_nb br r
  | Iblob bl, Iblob br -> invalidate_bb bl br r
  | Iblob bl, Inone    -> invalidate_bn bl r
  | Isiblings, Inone -> r (* no invalidate on seg-intro *)
  | Inone, Isiblings -> r (* no invalidate on seg-intro *)
  | _, _ -> Log.todo_exn "invalidate"

(** Extraction of mappings *)
let extract_mappings
    (svl: IntSet.t) (svr: IntSet.t)
    (nr: Graph_sig.node_relation): unit node_mapping * unit node_mapping =
  if false then
    Log.info "Node_relation(extract_mappings):\n%s"
      (Graph_utils.Nrel.nr_2strc nr);
  let init (sv: IntSet.t): unit node_mapping =
    { nm_map    = IntMap.empty ;
      nm_rem    = sv ;
      nm_suboff = fun _ -> true ; } in
  IntMap.fold
    (fun i (il, ir) (accl, accr) ->
      Nd_utils.add_to_mapping il i accl, Nd_utils.add_to_mapping ir i accr
    ) nr.n_pi (init svl, init svr)

(** Specific functions *)
let rules_add_weakening (p: int * int) (r: rules): rules =
  { r with r_indintro = PairSet.add p r.r_indintro }
let rules_add_splitind_l (p: int * int) (r: rules): rules =
  { r with r_splitind_l = PairSet.add p r.r_splitind_l }
let rules_add_splitind_r (p: int * int) (r: rules): rules =
  { r with r_splitind_r = PairSet.add p r.r_splitind_r }
