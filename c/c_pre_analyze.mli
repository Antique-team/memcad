(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_pre_analyze.mli
 **       pre-analysis, to tune the analyzer
 ** Xavier Rival, 2011/10/14 *)
open Ast_sig
open C_sig
open C_analysis_sig
open Data_structures

(** Liveness analysis *)
(* Computation of live variables
 *  - it should help guiding weak abstraction
 *  - for now, we use a reference *)

(* Type definition: should be moved somewhere *)
(* Analysis result:
 *   stmt -> set of variables that are "live" *)
type live = VarSet.t IntMap.t
(* Extraction of live variables at a given point *)
val live_at: c_loc -> VarSet.t
(* The liveness analysis *)
val live_prog: string -> c_prog -> live

(** Pre-analysis domain based on access paths *)
module Path_liveness: DOM_LIVENESS

(** Pre-analysis domain based on variables (access paths are ignored) *)
module Var_liveness: DOM_LIVENESS

(** Functor to construct the pre-analysis *)
module Gen_pre_analysis: functor (D: DOM_LIVENESS) -> PRE_ANALYSIS


(** TODO XR => JL: add comments to these definitions *)
module Materialization: DOM_PRE_PROPERTY
module Gen_path_sensitive_pre_analysis: functor 
  (D: DOM_PRE_PROPERTY) -> PRE_PATH_SENSITIVE_ANALYSIS

