(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: inst_utils.mli
 **       utilities for the instantiation of set parameters
 ** Xavier Rival, Huisong Li, 2015/04/05 *)
open Data_structures

open Inst_sig
open Set_sig

type setv_inst = Inst_sig.setv_inst

(** Set parameters instantiations *)
val setv_inst_empty: setv_inst
val setv_inst_2stri: string -> setv_inst -> string

(* Add a new setv *)
val add_setv: int -> setv_inst -> setv_inst
(* Remove a previously added setv *)
val rem_setv: int -> setv_inst -> setv_inst

val setv_inst_free: int -> setv_inst -> bool
val setv_inst_bind: int -> set_expr -> setv_inst -> setv_inst
val setv_inst_nobind: int -> setv_inst -> setv_inst
val setv_inst_guess: int -> int -> setv_inst -> setv_inst
val setv_inst_over_bind: int -> set_expr -> setv_inst -> setv_inst
val setv_inst_make_guess: int -> set_expr -> setv_inst -> setv_inst

val setv_inst_complete: IntSet.t -> (set_cons -> bool)
  -> setv_inst -> setv_inst
val setv_inst_strengthen: setv_inst -> setv_inst  -> setv_inst



val fold_add: (int -> 'a -> 'a) -> setv_inst -> 'a -> 'a
val fold_rem: (int -> 'a -> 'a) -> setv_inst -> 'a -> 'a
