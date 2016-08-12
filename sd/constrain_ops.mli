(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: constrain_ops.mli
 **       join algorithms
 ** Antoine Toubhans, 2012/04/22 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig
open Ind_sig
open Constrain_sig
open Constrain_utils

(* id_mapping utilitary functions *)
val id_map_empty: unit -> id_mapping
val id_map_add: id -> id -> id -> id_mapping -> id_mapping
val id_map_left_right: id -> id_mapping -> id
val id_map_right_left: id -> id_mapping -> id

(* comparison operator functions *)
val c_path_is_le: c_path -> c_path -> cstr -> bool
val is_le: (id, id) PMap.t -> cstr -> cstr -> bool

(* meeting operator functions *)
val meet_left: (id, id) PMap.t -> cstr -> cstr -> cstr

(* join operator functions *)
val path_join: path -> path -> path 

val c_path_join: id_mapping -> c_path -> c_path -> c_path option
val c_path_join_eq_left: id_mapping -> c_path -> c_path
val c_path_join_eq_right: id_mapping -> c_path -> c_path

val d_path_join: id_mapping -> d_path -> d_path -> d_path option
val d_path_join_eq_left: id_mapping -> d_path -> d_path
val d_path_join_eq_right: id_mapping -> d_path -> d_path

val join: id_mapping -> cstr -> cstr -> cstr -> cstr

(* inductive is_le & join *)
val make_cstri: int -> int -> int -> cstr_indcall * id list
val is_le_cstr_indcall: cstr_indcall -> cstr_indcall -> bool
val join_cstr_indcall: cstr_indcall -> cstr_indcall -> cstr_indcall 
val join_cstr_indcall_list: cstr_indcall list -> cstr_indcall 

(* segment is_le & join *)
val make_cstrs: int -> int -> int -> cstr_segcall * id list
val is_le_cstr_segcall: cstr_segcall -> cstr_segcall -> bool
val join_cstr_segcall: cstr_segcall -> cstr_segcall -> cstr_segcall 
val join_cstr_segcall_list: cstr_segcall list -> cstr_segcall 
