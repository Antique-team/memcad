(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_mat.mli
 **       materialization support for the list abstract domain
 ** Xavier Rival, 2014/03/02 *)
open List_sig
open Set_sig

(** Unfolding primitive *)
val unfold: int
  -> bool (* whether to include only non empty segment cases *)
    -> lmem -> unfold_result list
