(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_abs.ml
 **       experimental partial unary abstraction algorithm
 ** Xavier Rival, 2014/04/03 *)
open Data_structures
open Flags
open Lib

open Ind_sig
open List_sig
open Nd_sig
open Set_sig
open Sv_sig

open List_utils

(** Improvements to consider:
 *   - document hints, or remove if not needed
 *   - consider reducing segments as well
 **)

(** Error report *)
module Log =
  Logger.Make(struct let section = "l_abs___" and level = Log_level.DEBUG end)

(* Local debug flag *)
let debug_module = false

(** Function trying to perform a weakening at a specific SV i *)
let local_abstract_one
    ~(stop: int Aa_sets.t option) (* SVs to stop at *)
    (i: int)                   (* SV considered as a basis for the weakening *)
    (ld: l_call)               (* candidate call *)
    (sat: n_cons -> bool)      (* value satisfiability check *)
    (setsat: set_cons -> bool) (* set satisfiability check *)
    (m: lmem)
    (rel: int IntMap.t)    (* used to project out SVs which have been used *)
    : lmem * (int IntMap.t) * (IntSet.t IntMap.t) * (set_cons list)  =
  if debug_module then
    Log.debug "CALL local abstract-shape at SV %d" i;
  (* Creation of a memory state with only a list edge *)
  let mlist = list_edge_add i ld (sv_add i Ntaddr lmem_empty) in
  let key =
    IntMap.fold
      (fun id _ key ->
        if id <> i then 
          Keygen.use_key key id
        else key
      ) rel (mlist.lm_nkey) in
  (* Exclude the source node from the hing *)
  let stop = Option.map (Aa_sets.remove i) stop in
  (* Application of the inclusion check algorithm *)
  let le_res =
    let inj = Aa_maps.singleton i i in
    (* for now, we do not attempt to reduce segments *)
    List_is_le.is_le_weaken_guess ~stop:stop m
      IntSet.empty IntSet.empty (* no segment *)
      sat setsat { mlist with lm_nkey = key }
      inj Aa_maps.empty in
  (* If inclusion finds something, weaken *)
  match le_res with
  | `Ilr_not_le -> m, IntMap.empty, IntMap.empty, [ ]
  | `Ilr_le_list (rem, inj, sinj, s_info) ->
      (list_edge_add i ld rem), inj, sinj, s_info 
  | `Ilr_le_lseg (rem, it, inj, sinj, s_info) ->
      (lseg_edge_add i it ld rem), inj, sinj, s_info

(** Main weakening function; tries to apply weakening at each point *)
let local_abstract
    ~(stop: int Aa_sets.t option) (* SVs to stop at *)
    (sat: n_cons -> bool)         (* constraint satisfiability check *)
    (setsat: set_cons -> bool)
    (m: lmem)
    : lmem * (int IntMap.t) * (IntSet.t IntMap.t) * (set_cons list) =
  if debug_module then
    Log.debug "CALL local abstract";
  (* First step: gather candidates for weakening *)
  let candidates =
    IntMap.fold
      (fun i ln acc ->
        match ln.ln_e, ln.ln_odesc with
        | Lhemp, _ | Lhlist _, _ | Lhlseg _, _ | _, None -> 
            acc
        | Lhpt _, Some ld ->
            let lc =
              if ld.ld_set = None then { lc_def = ld ; lc_args = [ ] }
              else Log.todo_exn "get_set_args" in
            IntMap.add i lc acc
      ) m.lm_mem (IntMap.empty) in
  (* 2. attempts to perform weakening for each candidate *)
  IntMap.fold
    (fun i lc (macc, inj_acc, sinj_acc, info_acc) ->
      let macc, inj, sinj, s_info = 
        local_abstract_one ~stop:stop i lc sat setsat macc inj_acc in
      let sub_merge k x y =
        match x, y with
        | None, None | None, Some _ -> y
        | Some _, None -> x
        | Some l, Some r -> 
            if l = r then Some l
            else Log.fatal_exn "local_abstract: merge not match" in
      let sub_merge_set k x y =
        match x, y with
        | None, None | None, Some _ -> y
        | Some _, None -> x
        | Some l, Some r -> Some (IntSet.union l r)  in
      ( macc,
        IntMap.merge sub_merge inj inj_acc,
        IntMap.merge sub_merge_set sinj_acc sinj,
        List.rev_append s_info info_acc )
    ) candidates (m, IntMap.empty, IntMap.empty, [ ])
