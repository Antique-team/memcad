(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: disj_utils.mli
 **       structures used in disjunction domains
 ** Xavier Rival, 2012/07/10 *)
open Data_structures
open Disj_sig

(** Pretty-printing *)
val abs_hist_atom_2str: abs_hist_atom -> string
val abs_hist_2str: abs_hist -> string

(** Comparison *)
val aha_compare: abs_hist_atom -> abs_hist_atom -> int
val ah_compare: abs_hist -> abs_hist -> int

(** Unification, sharing common sub-strings *)
val ah_unify: abs_hist -> abs_hist -> abs_hist

(** Decides whether ah0 is a prefix of ah1 *)
val ah_is_prefix: abs_hist -> abs_hist -> bool

(** Maps and Sets for storage *)
module AHOrd: (OrderedType with type t = abs_hist)
module AHMap: (MAP with type key = abs_hist)
module AHSet: (SET with type elt = abs_hist)

(** Sanity check *)
(* Verification that an abs_hist_fun does not have several
 * partitions with the same token
 *   => i.e., each partition should have a unique token
 *)
val ahf_sanity_check: string -> 'a abs_hist_fun -> unit
