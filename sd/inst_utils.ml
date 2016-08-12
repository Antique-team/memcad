(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: inst_utils.ml
 **       utilities for the instantiation of set parameters
 ** Xavier Rival, Huisong Li, 2015/04/05 *)
open Data_structures
open Lib

open Inst_sig
open Set_sig

open Set_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "ins_uts_" and level = Log_level.DEBUG end)

let debug_module = false


(** Data-type *)
type setv_inst = Inst_sig.setv_inst


(** Basic functions on set parameters instantiations *)
(* Empty *)
let setv_inst_empty =
  { setvi_add   = IntSet.empty;
    setvi_rem   = IntSet.empty;
    setvi_eqs   = IntMap.empty;
    setvi_guess = IntMap.empty;
    setvi_none  = IntSet.empty;
    setvi_props = [ ];
    setvi_prove = [ ] }

(* Pretty-printing *)
let setv_inst_2stri (ind: string) (inst: setv_inst): string =
  let s =
    Printf.sprintf "%sadd: %s\n%srem: %s\n" ind (intset_2str inst.setvi_add)
       ind (intset_2str inst.setvi_rem) in
  let s =
    IntMap.fold
      (fun setv ex acc ->
        Printf.sprintf "%s%sS[%d] |=> %s\n" acc ind setv (set_expr_2str ex)
      ) inst.setvi_eqs s in
  let s =
    IntMap.fold
      (fun setv sv acc ->
        Printf.sprintf "%s%sS[%d] |:> N[%d]\n" acc ind setv sv
      ) inst.setvi_guess s in
  let s =
    IntSet.fold
      (fun setv acc ->
        Printf.sprintf "%s%sS[%d] |=> ???\n" acc ind setv
      ) inst.setvi_none s in
  let s =
    List.fold_left
      (fun acc sc ->
        Printf.sprintf "%s%s+ %s\n" acc ind (set_cons_2str sc)
      ) s inst.setvi_props in
  List.fold_left
    (fun acc sc ->
      Printf.sprintf "%s%s? |- %s\n" acc ind (set_cons_2str sc)
    ) s inst.setvi_prove

(* Add a new setv *)
let add_setv (setv: int) (inst: setv_inst): setv_inst =
  assert (not (IntSet.mem setv inst.setvi_add));
  assert (not (IntSet.mem setv inst.setvi_rem));
  { inst with setvi_add = IntSet.add setv inst.setvi_add }

(* Remove a previously added setv *)
let rem_setv (setv: int) (inst: setv_inst): setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  assert (not (IntSet.mem setv inst.setvi_rem));
  { inst with setvi_rem = IntSet.add setv inst.setvi_rem }

(* Is setv free in inst ? *)
let setv_inst_free (setv: int) (inst: setv_inst): bool =
  not (IntMap.mem setv inst.setvi_eqs) && not (IntSet.mem setv inst.setvi_none)
    && not (IntMap.mem setv inst.setvi_guess)

(* Bind setv to eq in inst *)
let setv_inst_bind (setv: int) eq (inst: setv_inst): setv_inst =
  if debug_module then
    Log.debug "trying to bind: %d\n%s" setv (setv_inst_2stri "  " inst);
  assert (IntSet.mem setv inst.setvi_add);
  if setv_inst_free setv inst then
    { inst with setvi_eqs = IntMap.add setv eq inst.setvi_eqs }
  else Log.fatal_exn "setv_inst_bind: %d already specified" setv

(* Mark setv as unknown, with no information *)
let setv_inst_nobind (setv: int) (inst: setv_inst): setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if setv_inst_free setv inst then
    { inst with setvi_none = IntSet.add setv inst.setvi_none }
  else Log.fatal_exn "setv_inst_nobind: %d already specified" setv

(* Mark setv as unknown, can be "guessed" later using an element *)
let setv_inst_guess (setv: int) (sv: int) (inst: setv_inst): setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if setv_inst_free setv inst then
    { inst with setvi_guess = IntMap.add setv sv inst.setvi_guess }
  else Log.fatal_exn "setv_inst_guess: %d already specified" setv

(* Overwrite a previously done binding *)
let setv_inst_over_bind (setv: int) (ex: set_expr) (inst: setv_inst)
    : setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if IntSet.mem setv inst.setvi_none then
    setv_inst_bind setv ex
      { inst with setvi_none = IntSet.remove setv inst.setvi_none }
  else Log.fatal_exn "setv_inst_make_guess: setv not guessable"

(* Constrain setv, by "guessing" it as ex *)
let setv_inst_make_guess (setv: int) (ex: set_expr) (inst: setv_inst)
    : setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if IntMap.mem setv inst.setvi_guess then
    setv_inst_bind setv ex
      { inst with setvi_guess = IntMap.remove setv inst.setvi_guess }
  else Log.fatal_exn "setv_inst_make_guess: setv not guessable"


(** Completion of an instantiation *)
let setv_inst_complete
    (roots: IntSet.t)
    (set_sat: set_cons -> bool)
    (inst: setv_inst)
    : setv_inst =
  let debug_loc = false in
  (* 1. improve instantiation by binding roots instead of others
   *    if S[i] |=> S[k] and xnum |- S[k] = S[j], with S[j] root, then
   *    we use S[i] |=> S[j] instead *)
  let inst =
    IntMap.fold
      (fun setv ex acc ->
        match ex with
        | S_var setv0 ->
            if IntSet.mem setv0 roots then acc
            else
              let rootsok =
                IntSet.fold
                  (fun i acc ->
                    if debug_loc then Log.info "point: %d, %d" i setv0;
                    if set_sat (S_eq (S_var i, S_var setv0)) then
                      IntSet.add i acc
                    else acc
                  ) roots IntSet.empty in
              if IntSet.cardinal rootsok > 0 then
                (* replace with the lowest root ID *)
                let root = IntSet.min_elt rootsok in
                { inst with
                  setvi_eqs = IntMap.add setv (S_var root) inst.setvi_eqs }
              else acc
        | _ -> acc
      ) inst.setvi_eqs inst in
  (* 2. adjust guesses based on membership *)
  let inst =
    IntMap.fold
      (fun setv sv acc ->
        let l =
          IntSet.fold
            (fun root acc ->
              if set_sat (S_mem (sv, S_var root)) then root :: acc
              else acc
            ) roots [ ] in
        match l with
        | root0 :: _ -> setv_inst_make_guess setv (S_var root0) acc
        | _ -> acc
      ) inst.setvi_guess inst in
  if debug_loc then Log.info "setv_inst_complete,Ph3";
  inst


(** Strengthening of an instantiation *)
let setv_inst_strengthen (iref: setv_inst) (itgt: setv_inst): setv_inst =
  IntSet.fold
    (fun setv acc ->
      try setv_inst_over_bind setv (IntMap.find setv iref.setvi_eqs) acc
      with Not_found -> acc
    ) itgt.setvi_none itgt


let fold_add (f: int -> 'a -> 'a) (inst: setv_inst) (x: 'a): 'a =
  IntSet.fold f inst.setvi_add x
let fold_rem (f: int -> 'a -> 'a) (inst: setv_inst) (x: 'a): 'a =
  IntSet.fold f inst.setvi_rem x
