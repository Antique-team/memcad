(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_abs.mli
 **       experimental partial unary abstraction algorithm
 ** Xavier Rival, 2014/04/03 *)
open Data_structures
open List_sig
open Nd_sig
open Set_sig

(** Main weakening function; tries to apply weakening at each point *)
val local_abstract:
    stop: int Aa_sets.t option (* SVs to stop at *)
  -> (n_cons -> bool)          (* constraint satisfiability check *)
  -> (set_cons -> bool)        (* set constraint satisfiability check *)
  -> lmem
  -> lmem * (int IntMap.t) * (IntSet.t IntMap.t) * (set_cons list)
