(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_utils.mli
 **       utilities for set domain
 ** Huisong Li, 2014/09/25 *)
open Data_structures
open Lib
open Set_sig
open List_sig

(* Pretty-printing *) 
val set_expr_2str:  set_expr -> string
val set_cons_2str:  set_cons -> string
val set_par_type_2str: set_par_type -> string

(** Mapping functions *)
(* Empty mapping *)
val setv_mapping_empty: setv_mapping
(* Addition of a new node *)
val add_to_mapping: int -> int -> setv_mapping -> setv_mapping
(* Pretty-printing *)
val setv_mapping_2str: setv_mapping -> string
(* Extraction of mappings and the set var on both sides *)
val extract_mappings: (int*int) IntMap.t 
  -> setv_mapping * setv_mapping * IntSet.t
(* Map translation *)
val s_expr_map: (int -> int) -> (int -> int) -> set_expr -> set_expr
val s_cons_map: (int -> int) -> (int -> int) -> set_cons -> set_cons

(** Transformers over set_expr and set_cons *)
(*  Take a function for setv to set_expr, and substitute everywhere *)
val transform_expr: (int -> set_expr) -> set_expr -> set_expr
val transform_cons: (int -> set_expr) -> set_cons -> set_cons

(** Set of setv that appear *)
val set_expr_setvs: set_expr -> IntSet.t
val set_cons_setvs: set_cons -> IntSet.t

(** Pruning some SETVs from a list of set constraints *)
(* This function should return an equivalent set of constraints, where
 * some SETVs are removed (it is used for is_le) *)
val set_cons_prune_setvs: IntSet.t -> set_cons list -> set_cons list


(* generate set constraints that should be proved equal from left side
 * that is, when a set variable \sete is mapped to many set
 * variables {\sete' \setf', ...}, choose one mapped set variable
 * (like \sete') and add equality constraints on
 * all the mapped set variables *)
val gen_eq_setctr: setv_embedding -> set_expr IntMap.t * set_cons list

(* replace instantiated set variables from a set expression*)
val replace_sexpr: set_expr -> set_expr IntMap.t -> int IntMap.t ->
  set_expr
(* replace instantiated set variables from set constraints *)
val replace_cons: set_cons list -> set_expr IntMap.t -> int IntMap.t
  -> set_cons list

(* instantiate set variables from equality set constraints *)
val instantiate: set_cons list -> set_expr IntMap.t -> int IntMap.t
  -> set_expr IntMap.t * set_cons list

(* check if there is non instantiated set variables,
 * if there is non instantiated set variables, compute the minimal
 * set of non-instantiated set variables, that needs to instantiated
 * to fresh set variables *)
val check_non_inst: set_cons list -> set_expr IntMap.t -> IntSet.t

(* liner uplus or union set variables from set expression *)
val linear_svars: set_expr -> bool -> (IntSet.t * IntSet.t) option

(* make uplus or union set expression *)
val make_sexp: IntSet.t -> IntSet.t ->  bool -> set_expr
(** Functions on node injections (for is_le) *)
module Semb:
    sig
      val empty: setv_embedding
      (* To string, compact version *)
      val ne_2str: setv_embedding -> string
      (* To string, long version *)
      val ne_full_2stri: string -> setv_embedding -> string
      (* Tests membership *)
      val mem: int -> setv_embedding -> bool
      (* Find an element in the mapping *)
      val find: int -> setv_embedding -> IntSet.t
      (* Add an element to the mapping *)
      val add: int -> int -> setv_embedding -> setv_embedding
      (* Initialization *)
      val init: setv_emb -> setv_embedding
      (* Extraction of siblings information *)
      val siblings: setv_embedding -> IntSet.t IntMap.t
    end
