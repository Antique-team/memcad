(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: gen_is_le.ml
 **       Generic elements used in the inclusion checking algorithm
 ** Xavier Rival, 2014/03/06 *)
open Data_structures
open Lib

open Gen_dom

(** Error report *)
module Log =
  Logger.Make(struct let section = "gen_isle" and level = Log_level.DEBUG end)

(** Exception when inclusion fails be checked *)
exception Le_false of string

(** Rules that could be applied right away *)
(* Kinds of rules *)
type rkind =
  (* Reaching a stop node *)
  | Rstop
  (* Siblings, detection of void segments *)
  | Rvs
  (* Conventional pair of edges *)
  | Rpp | Rii | Rss | Rsi | Rei | Rpi | Rps
(* Record of rules that can be activated *)
type instances = PairSet.t
type rules =
    { r_stop:    instances ; (* stop node, for which a hint was supplied *)
      r_pt_prio: instances ; (* prioretary pt rules (at the beginning *)
      r_pt_pt:   instances ; (* match points-to *)
      r_ind_ind: instances ; (* match inductives *)
      r_seg_seg: instances ; (* eat left segment and move on *)
      r_seg_ind: instances ; (* eat left segment and move on *)
      r_emp_ind: instances ; (* unfold right inductive *)
      r_pt_ind:  instances ; (* unfold right inductive *)
      r_void_seg:instances ; (* empty right segment *)
      r_pt_seg:  instances ; (* unfold right segment *) }

(** Utilities and Pretty-printing *)
(* Empty set of applicable rules *)
let empty_rules: rules =
  { r_stop     = PairSet.empty ;
    r_pt_prio  = PairSet.empty ;
    r_pt_pt    = PairSet.empty ;
    r_ind_ind  = PairSet.empty ;
    r_seg_seg  = PairSet.empty ;
    r_seg_ind  = PairSet.empty ;
    r_emp_ind  = PairSet.empty ;
    r_pt_ind   = PairSet.empty ;
    r_void_seg = PairSet.empty ;
    r_pt_seg   = PairSet.empty }
(* Pretty-printing *)
let rkind_2str: rkind -> string = function
  | Rstop -> "stop"
  | Rvs   -> "siblings+segment"
  | Rpp   -> "pt-pt"
  | Rii   -> "ind-ind"
  | Rss   -> "seg-seg"
  | Rsi   -> "seg-ind"
  | Rei   -> "emp-seg"
  | Rpi   -> "pt-ind"
  | Rps   -> "pt-seg"
let rules_2str (r: rules): string =
  let instances_2str (name: string) (s: instances): string =
    if s != PairSet.empty then Printf.sprintf "%s %s\n" name (pairset_2str s)
    else "" in
  (instances_2str "stop:     " r.r_stop)
  ^ (instances_2str "pt-prio:  " r.r_pt_prio)
  ^ (instances_2str "pt-pt:    " r.r_pt_pt)
  ^ (instances_2str "ind-ind:  " r.r_ind_ind)
  ^ (instances_2str "seg-seg:  " r.r_seg_seg)
  ^ (instances_2str "seg-ind:  " r.r_seg_ind)
  ^ (instances_2str "emp-ind:  " r.r_emp_ind)
  ^ (instances_2str "pt-ind:   " r.r_pt_ind)
  ^ (instances_2str "void-seg: " r.r_void_seg)
  ^ (instances_2str "pt-seg:   " r.r_pt_seg)

(** Strategy function; returns next rule to apply *)
(* current strategy:
 *  0. stop (exit)
 *  1. pt-prio
 *  2. ind-ind, seg-seg, seg-ind
 *  3. pt-seg, pt-ind
 *  4. pt-pt
 *  5. emp-ind, emp-seg
 * this is basically the big selector... *)
let rules_next (r: rules): (rkind * (int * int) * rules) option =
  if r.r_stop != PairSet.empty then
    let p = PairSet.min_elt r.r_stop in
    Some (Rstop, p,
          { r with r_stop = PairSet.remove p r.r_stop })
  else if r.r_pt_prio != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_prio in
    Some (Rpp, p,
          { r with r_pt_prio = PairSet.remove p r.r_pt_prio })
  else if r.r_ind_ind != PairSet.empty then
    let p = PairSet.min_elt r.r_ind_ind in
    Some (Rii, p,
          { r with r_ind_ind = PairSet.remove p r.r_ind_ind })
  else if r.r_pt_pt != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_pt in
    Some (Rpp, p,
          { r with r_pt_pt = PairSet.remove p r.r_pt_pt })
  else if r.r_seg_seg != PairSet.empty then
    let p = PairSet.min_elt r.r_seg_seg in
    Some (Rss, p,
          { r with r_seg_seg = PairSet.remove p r.r_seg_seg })
  else if r.r_seg_ind != PairSet.empty then
    let p = PairSet.min_elt r.r_seg_ind in
    Some (Rsi, p,
          { r with r_seg_ind = PairSet.remove p r.r_seg_ind })
  else if r.r_void_seg != PairSet.empty then
    let p = PairSet.min_elt r.r_void_seg in
    Some (Rvs, p,
          { r with r_void_seg = PairSet.remove p r.r_void_seg })
  else if r.r_pt_seg != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_seg in
    Some (Rps, p,
          { r with r_pt_seg = PairSet.remove p r.r_pt_seg })
  else if r.r_pt_ind != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_ind in
    Some (Rpi, p,
          { r with r_pt_ind = PairSet.remove p r.r_pt_ind })
  else if r.r_emp_ind != PairSet.empty then
    let p = PairSet.min_elt r.r_emp_ind in
    Some (Rei, p,
          { r with r_emp_ind = PairSet.remove p r.r_emp_ind })
  else None

(** Collecting applicable rules at a graph node *)
let collect_rules_sv_gen
    (sv_kind: int -> 'a -> region_kind)
    (sv_seg_end: int -> 'a -> int option)
    (is_prio: bool) (* whether pt rules are prioritary (init) *)
    (hintl: int Aa_sets.t option) (* optional hint ("stop" nodes) *)
    (end_seg: IntSet.t) (* optional end of segment points *)
    (ni: Graph_sig.node_embedding) (* mapping, used to guess siblings *)
    (gl: 'a) (gr: 'a)
    (il: int) (ir: int) (acc: rules): rules =
  (* Function to collect regular rules (all except void-seg and stop);
   *  - it should be called only when there is no occurrence of a "stop" here!
   *  - it will be called after siblings search *)
  let do_regular_rules acc =
    (* Search for regular inclusion testing rules *)
    match sv_kind il gl, sv_kind ir gr with
    | Kemp, Kemp -> acc
    | Kpt , Kpt  ->
        if is_prio then
          { acc with r_pt_prio = PairSet.add (il, ir) acc.r_pt_prio }
        else
          { acc with r_pt_pt = PairSet.add (il, ir) acc.r_pt_pt }
    | Kind, Kind ->
        { acc with r_ind_ind = PairSet.add (il, ir) acc.r_ind_ind }
    | Kseg, Kseg ->
        { acc with r_seg_seg = PairSet.add (il, ir) acc.r_seg_seg }
    | Kseg, Kind ->
        { acc with r_seg_ind = PairSet.add (il, ir) acc.r_seg_ind }
    | Kemp, Kind ->
        { acc with r_emp_ind = PairSet.add (il, ir) acc.r_emp_ind }
    | Kpt , Kind ->
        { acc with r_pt_ind  = PairSet.add (il, ir) acc.r_pt_ind  }
    | Kemp, Kseg ->
        { acc with r_void_seg = PairSet.add (il, ir) acc.r_void_seg }
    | Kpt , Kseg ->
        { acc with r_pt_seg  = PairSet.add (il, ir) acc.r_pt_seg  }
    | Kind, Kpt  | Kseg, Kpt  | Kind, Kemp 
    | Kseg, Kemp | Kpt , Kemp | Kemp, Kpt
    | Kind, Kseg ->
        (* no immediately applicable rule *)
        acc in
  (* 1. Extraction of siblings information for segment *)
  let acc =
    let siblings = Graph_utils.Nemb.siblings ni in
    if siblings != IntMap.empty && !Flags.flag_debug_is_le_shape then
      begin
        Log.force "Siblings in is_le:";
        IntMap.iter (fun i s -> Log.force " %d: %s" i (intset_2str s))
          siblings;
      end;
    IntMap.fold
      (fun il sr acc ->
        IntSet.fold
          (fun isr acc ->
            match sv_seg_end isr gr with
            | Some sed ->
                if IntSet.mem sed sr then
                  begin
                    if !Flags.flag_debug_is_le_shape then
                      Log.force "keeping sibling: (%d,%d)===>(%d,%d)"
                        il isr il sed;
                    { acc with
                      r_void_seg = PairSet.add (il, isr) acc.r_void_seg }
                  end
                else acc
            | _ -> acc
          ) sr acc
      ) siblings acc in
  (* 2. Checks whether il was marked as a stop position in the left graph
   *    (i.e., a position where a folding hint was supplied)
   * 3. Collect the regular rules, if not stop *)
  match hintl with
  | None ->
      if IntSet.mem il end_seg then
        (* end of segment we are trying to introduce:
         * only collect emp-xyz rules *)
        match sv_kind il gl, sv_kind ir gr with
        | Kemp, Kemp -> acc
        | Kemp, Kind ->
            { acc with r_emp_ind = PairSet.add (il, ir) acc.r_emp_ind }
        | Kemp, Kseg ->
            { acc with r_void_seg = PairSet.add (il, ir) acc.r_void_seg }
        | _, _ -> acc
      else (* any other case: collect as many rules as possible *)
        do_regular_rules acc
  | Some h ->
      if Aa_sets.mem il h then
        begin
          if !Flags.flag_debug_is_le_shape then
            Log.force "IsLe hint<stop>: %d { %s }" il
              (Aa_sets.t_2str ", " string_of_int h);
          { acc with
            r_stop = PairSet.add (il, ir) acc.r_stop }
        end
      else do_regular_rules acc

(** Invalidation of rules that were performed or disabled, by the application
 ** of another rule *)
let invalidate_rules
    (isl: int) (isr: int)
    (hl: region_kind) (hr: region_kind) (r: rules): rules =
  let invalidate (il, ir) (s: PairSet.t): PairSet.t =
    if !Flags.flag_debug_is_le_strategy then
      Log.force "invalidating is_le rule at (%d,%d)" il ir;
    PairSet.remove (il, ir) s in
  let invalidate_map (f: (int * int) -> bool) (s: PairSet.t): PairSet.t =
    PairSet.fold
      (fun p acc ->
        if f p then invalidate p acc
        else acc
      ) s s in
  let invalidate_l  = invalidate_map (fun (x, _) -> x = isl)
  and invalidate_r  = invalidate_map (fun (_, y) -> y = isr)
  and invalidate_lr = invalidate_map (fun (x, y) -> x = isl || y = isr) in
  match hl, hr with
  | Kpt , Kpt  ->
      { r with
        r_pt_prio  = invalidate_lr r.r_pt_prio;
        r_pt_pt    = invalidate_lr r.r_pt_pt;
        r_pt_ind   = invalidate_l  r.r_pt_ind;
        r_pt_seg   = invalidate_l  r.r_pt_seg }
  | Kind, Kind ->
      { r with
        r_ind_ind  = invalidate_lr r.r_ind_ind;
        r_seg_ind  = invalidate_r  r.r_seg_ind;
        r_emp_ind  = invalidate_r  r.r_emp_ind;
        r_pt_ind   = invalidate_r  r.r_pt_ind }
  | Kemp, Kseg ->
      { r with
        r_seg_seg  = invalidate_r r.r_seg_seg;
        r_void_seg = invalidate_r r.r_void_seg;
        r_pt_seg   = invalidate_r r.r_pt_seg }
  | Kseg, Kseg ->
      { r with
        r_seg_seg  = invalidate_r r.r_seg_seg;
        r_seg_ind  = invalidate_l r.r_seg_ind;
        r_void_seg = invalidate_r r.r_void_seg;
        r_pt_seg   = invalidate_r r.r_pt_seg }
  | Kseg, Kind ->
      { r with
        r_seg_ind  = invalidate_l r.r_seg_ind }
  | Kemp, Kemp -> r
  | _, _ -> Log.fatal_exn "invalidate_rules unhandled case"
