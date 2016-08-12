(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_ind_infer.mli
 **       inference of inductive definitions from C type definitions
 ** Xavier Rival, 2013/01/05 *)
open C_sig
open Ind_sig

(** Inference function *)
(* Reads all typedefs, and try to propose inductive definitions for
 * them, assuming:
 *   - all inductives have a "0" case, with empty memory
 *   - all inductives have no parameter
 *   - all inductives correspond to list, trees and the like
 *)
val compute_inductives: c_prog -> ind list

(** Compatibility checking *)
(* checks whether an inductive definition is compatible with a type
 * according to the types of the fields *)
val test_compat_ind: c_type -> ind -> bool
