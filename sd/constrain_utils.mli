(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: constrain_utils.mli
 **       basic tools
 ** Antoine Toubhans, 2012/04/19 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig
open Constrain_sig

(* To-do: add more comments on the functions below *)

(* id utility tools *)
val id_next: id -> id
val id_zero: id
val id_eq: id -> id -> bool
val destination_eq: destination -> destination -> bool

(* paths utility tools *)
val path_concat: path -> path -> path
val path_is_rigid: path -> bool

(* c_path utility tools *)
val c_path_concat: c_path -> id -> c_path -> c_path option
val c_path_get_args: c_path -> id PSet.t
val c_path_map: (id -> id) -> c_path -> c_path
val c_path_map_null: id -> c_path -> c_path
val c_path_eq: c_path -> c_path -> bool

(* d_path utility tools *)
val d_path_concat: d_path -> id -> d_path -> d_path option
val d_path_get_args: d_path -> id PSet.t
val d_path_map: (id -> id) -> d_path -> d_path
val d_path_map_null: id -> d_path -> d_path option
val d_path_eq: d_path -> d_path -> bool

(* eq classes utility functions *)
val eq_class_create_singl: id -> eq_class -> eq_cl_loc * eq_class
val eq_class_fusion: eq_cl_loc -> eq_cl_loc -> eq_class -> 
  eq_cl_loc * id PSet.t * eq_class
val eq_class_remove: eq_cl_loc -> id -> eq_class -> eq_class
val eq_class_find: eq_cl_loc -> eq_class -> id PSet.t
val fold_eq_class: (id -> id -> 'a -> 'a) -> (id -> 'a -> 'a) ->
  eq_class -> 'a -> 'a

(* node utility function *)
val iter_fw_paths: (path -> destination -> unit) -> node -> unit
val iter_bw_paths: (path -> id -> unit) -> node -> unit
val fold_fw_paths: (path -> destination -> 'a -> 'a) -> node -> 'a -> 'a
val fold_bw_paths: (path -> id -> 'a -> 'a) -> node -> 'a -> 'a
val for_all_paths: (path -> destination -> bool) -> node -> bool
val iter_c_paths: (c_path -> unit) -> node -> unit
val fold_c_paths: (c_path -> 'a -> 'a) -> node -> 'a -> 'a
val iter_d_paths: (d_path -> unit) -> node -> unit
val fold_d_paths: (d_path -> 'a -> 'a) -> node -> 'a -> 'a
val for_all_c_paths: (c_path -> bool) -> node -> bool
val for_all_d_paths: (d_path -> bool) -> node -> bool

val add_fw_paths: path -> destination -> node -> node
val add_bw_paths: path -> id -> node -> node
val remove_fw_paths: path -> destination -> node -> node
val remove_bw_paths: path -> id -> node -> node

(* initializers *)
val init_eq_class: eq_class
val top: unit -> cstr

(* pretty printing *)
val id_2str: id -> string
val path_2str: path -> string
val destination_2str: destination -> string
val c_path_2str: id -> c_path -> string
val d_path_2str: id -> d_path -> string
val eq_cl_loc_2str: eq_cl_loc -> string
val node_2stri: string -> id -> node -> string
val eq_class_2stri: string -> eq_class -> string
val cstr_2stri: string -> cstr -> string
val cstr_2str: cstr -> string 
val cstr_indcall_2stri: string -> cstr_indcall -> string
val cstr_segcall_2stri: string -> cstr_segcall -> string
val id_mapping_2stri: string -> id_mapping -> string

(* general tools *)
val get_node: id -> cstr -> node

(* testing *)
val are_id_eq: id -> id -> cstr -> bool
val is_id_null: id -> cstr -> bool
val is_id_not_null: id -> cstr -> bool
val are_destination_eq: destination -> destination -> cstr -> bool
val is_there_path: id -> path -> destination -> cstr -> bool
val for_all_node: (id -> node -> bool) -> cstr -> bool
val is_bot: cstr -> bool

(* sanity checks *)
val sanity_check: string -> cstr -> unit

(** utlilitary functions *)
val create_fresh_node: cstr -> id * cstr
val create_nfresh_nodes: int -> cstr -> id list * cstr
val remove_node: id -> cstr -> cstr
val add_null: id -> cstr -> cstr
val add_not_null: id -> cstr -> cstr
val add_eq: id -> id -> cstr -> cstr
val add_dst_eq: destination -> destination -> cstr -> cstr
val add_path: id -> path -> destination -> cstr -> cstr
val remove_path: id -> path -> destination -> cstr -> cstr
val add_c_path: id -> c_path -> cstr -> cstr
val remove_c_path: id -> c_path -> cstr -> cstr
val add_d_path: id -> d_path -> cstr -> cstr
val remove_d_path: id -> d_path -> cstr -> cstr

val find_paths: id -> path -> cstr -> destination PSet.t
val find_bw_paths: id -> path -> cstr -> id PSet.t

val find_d_path: id -> (d_path -> bool) -> cstr -> d_path option

(* returns the equality class of NULL *)
val find_nulls: cstr -> id PSet.t
(* returns a map of (index -> equality class) *)
val find_eq_classes: cstr -> id PSet.t IntMap.t
