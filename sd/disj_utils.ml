(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: disj_utils.ml
 **       structures used in disjunction domains
 ** Xavier Rival, 2012/07/10 *)
open Data_structures
open Disj_sig
open Lib

module Log =
  Logger.Make(struct let section = "disj_uts" and level = Log_level.DEBUG end)

(** Pretty-printing *)
let h_unfold_2str = function
  | Uguard  -> "guard"
  | Uassign -> "assign"
  | Uunfold -> "unfold"
let abs_hist_atom_2str = function
  | Ah_if (l, b) -> Printf.sprintf "[if?%c@%d]" (if b then 't' else 'f') l
  | Ah_while l -> Printf.sprintf "[while@%d]" l
  | Ah_unfold (u, l, i) -> Printf.sprintf "[U:%s@%d:%d]" (h_unfold_2str u) l i
let abs_hist_2str (ah: abs_hist): string =
  Printf.sprintf "[%s]" (gen_list_2str "" abs_hist_atom_2str "::" ah)

(** Comparison *)
let loc_compare: loc -> loc -> int = (-)
let h_unfold_compare u0 u1 =
  match u0, u1 with
  | Uguard, Uguard | Uassign, Uassign | Uunfold, Uunfold -> 0
  | Uguard, _ -> -1
  | _, Uguard -> 1
  | Uassign, _ -> -1
  | _, Uassign -> 1
let aha_compare (a0: abs_hist_atom) (a1: abs_hist_atom): int =
  match a0, a1 with
  (* cases with the same head *)
  | Ah_if (l0, b0), Ah_if (l1, b1) ->
      let c = loc_compare l0 l1 in
      if c != 0 then c else compare b0 b1
  | Ah_while l0, Ah_while l1 ->
      loc_compare l0 l1
  | Ah_unfold (u0, l0, i0), Ah_unfold (u1, l1, i1) ->
      let c = loc_compare l0 l1 in
      if c != 0 then c else compare i0 i1
  (* Ah_temp < Ah_if < Ah_while < Ah_guard < Ah_assign *)
  | Ah_if _, _ -> -1
  | _, Ah_if _ ->  1
  | Ah_while _, _ -> -1
  | _, Ah_while _ ->  1
let ah_compare (ah0: abs_hist) (ah1: abs_hist): int =
  let l0 = List.length ah0 and l1 = List.length ah1 in
  let c = l0 - l1 in
  if c != 0 then c
  else
    List.fold_left2
      (fun c a0 a1 ->
        if c = 0 then aha_compare a0 a1
        else c
      ) 0 (List.rev ah0) (List.rev ah1)


(** Unification, sharing common sub-strings *)
let ah_unify (ah0: abs_hist) (ah1: abs_hist): abs_hist =
  let rec aux l0 l1 =
    match l0, l1 with
    | [], _ | _, [] -> []
    | t0 :: u0, t1 :: u1 ->
        if aha_compare t0 t1 = 0 then t0 :: aux u0 u1
        else [] in
  List.rev (aux (List.rev ah0) (List.rev ah1))


(** Decides whether ah0 is a prefix of ah1 *)
let ah_is_prefix (ah0: abs_hist) (ah1: abs_hist): bool =
  let rec aux l0 l1 =
    match l0, l1 with
    | [ ], _ -> true
    | _, [ ] -> false
    | t0 :: u0, t1 :: u1 ->
        aha_compare t0 t1 = 0 && aux u0 u1 in
  aux (List.rev ah0) (List.rev ah1)


(** Maps and Sets for storage *)
module AHOrd =
  struct
    type t = abs_hist
    let compare = ah_compare
    let t_2str = abs_hist_2str
  end
module AHMap = MapMake( AHOrd )
module AHSet = SetMake( AHOrd )

(** Sanity check *)
(* Verification that an abs_hist_fun does not have several
 * partitions with the same token
 *   => i.e., each partition should have a unique token
 *)
let ahf_sanity_check (msg: string) (ahf: 'a abs_hist_fun): unit =
  Log.info "ahf_sanity_check: #disj. %d" (List.length ahf);
  if !Flags.flag_sanity_disj then
    let m =
      List.fold_left
        (fun acc (ah, _) ->
          let old_n = try AHMap.find ah acc with Not_found -> 0 in
          AHMap.add ah (old_n + 1) acc
        ) AHMap.empty ahf in
    AHMap.iter
      (fun ah n ->
        if n > 1 then
          begin
            Log.info "Situation of disjuncts:";
            List.iter
              (fun (a, _) ->
                Log.info " - %s" (abs_hist_2str a)
              ) ahf;
            Log.warn "%s, sanity check failed<%s>:%d"
              msg (abs_hist_2str ah) n
          end
      ) m
