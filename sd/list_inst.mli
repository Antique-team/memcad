(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_inst.mli
 **       Instantiation of set parameters for the list domain join
 ** Xavier Rival, 2015/07/16 *)
open Data_structures

open Inst_sig
open List_sig
open Set_sig

(** Initialization of instantiation *)
val l_call_empty: l_call -> setv_inst -> setv_inst

(** Handling unresolved set constraints from is_le *)
val do_setconses:
    (int -> set_par_type option) (* Extraction of SETV types *)
  -> l_call                      (* Call used for the comparison *)
    -> l_call                    (* Call produced in the output *)
      -> int IntMap.t            (* Is_le mapping for symbolic variables *)
        -> IntSet.t IntMap.t     (* Is_le mapping for set parameters *)
          -> set_cons list       (* Constraints to process *)
            -> setv_inst         (* Previous instantiation *)
              -> setv_inst       (* Finished instantiation *)
