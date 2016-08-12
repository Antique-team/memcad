(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ind_analysis.mli
 **       extracts cstr relations from an inductive
 ** Antoine Toubhans, 2012/04/24 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig
open Ind_sig
open Constrain_sig

(* tools for pre-analysis *)
val cstri_get_formal_arg: id list -> cstr_indcall -> formal_arg -> id
val cstrs_get_formal_arg: id list -> cstr_segcall -> formal_arg -> id

(* reading for inductive preds *)
val cstri_read_aform: aform -> id list -> cstr_indcall -> cstr 
val cstri_read_cell: cell -> id list -> cstr_indcall -> cstr
val cstri_read_indcall: indcall -> id list -> cstr_indcall
  -> cstr_indcall -> cstr
(* reading for segment preds *)
val cstrs_read_aform: aform -> id list -> cstr_segcall -> cstr 
val cstrs_read_cell: cell -> id list -> cstr_segcall -> cstr
val cstrs_read_indcall: indcall -> id list -> cstr_indcall
  -> cstr_segcall -> cstr
val cstrs_read_segcall: indcall -> id list -> cstr_segcall
  -> cstr_segcall -> cstr

(* inductive analysis *)
val ind_preds: cstr_indcall StringMap.t ref
val ind_preds_find: string -> cstr_indcall 
val ind_preds_init: unit -> unit

(* segment analysis *)
val seg_preds: cstr_segcall StringMap.t ref
val seg_preds_find: string -> cstr_segcall 
val seg_preds_init: unit -> unit
