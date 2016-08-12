(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_sig.ml
 **       set domain interface
 ** Huisong Li, Xavier Rival, 2014/08/22 *)
open Data_structures
open Svenv_sig
open Offs
open Nd_sig


(** For the interface with the shape domain *)
(* Mapping from one join argument into the result
 * - sm_map:
 *     map a SETV into: a SETV + a set of other SETVs
 *     (renaming performed in two steps: first rename; second add equalities);
 * - sm_rem:
 *     SETVs to remove *)
type setv_mapping =
    { sm_map:    (int * IntSet.t) IntMap.t ;
      sm_rem:    IntSet.t ;  }
(* Mapping for the inclusion check *)
type setv_emb = (int, int) Aa_maps.t
type setv_embedding =
    { n_img: IntSet.t IntMap.t; (* direct image *)
      n_pre: IntSet.t IntMap.t  (* pre-image, used to detect siblings *) }

(** Type of set constraints *)
type nid = int (* SV (symboilc var id) *)
type sid = int (* SETV (set var id) *)
type set_par_type =
    { st_const: bool; (* "const":   propagates through inductino *)
      st_add:   bool; (* "add":     additive over segment/inductive comp. *)
      st_head:  bool; (* "head":    set of all the inductive sub-calls roots *)
      st_mono:  bool; (* "montone": can always be weakened to bigger *) }
type set_expr =
  | S_var of sid                       (* E *)
  | S_node of nid                      (* singleton: {\alpha} *)
  | S_uplus of set_expr * set_expr     (* E0 \uplus F1 *)
  | S_union of set_expr * set_expr     (* E0 \union F1 *)
  | S_empty                            (* empty set *)
type set_cons = 
  | S_mem of nid * set_expr         (* \alpha0 \in E1 *)
  | S_eq of set_expr * set_expr     (* E0 = E1 *)
  | S_subset of set_expr * set_expr (* E0 \subset E1 *)


module type DOMSET =
  sig
    (** Type of abstract values *)
    type t
    (* Bottom element (empty context) *)
    val bot: t
    val is_bot: t -> bool
    (* Top element (empty context) *)
    val top: t
    (* Pretty-printing, with indentation *)
    val t_2stri: string IntMap.t -> string -> t -> string
    (** Management of symbolic variables *)
    (* For sanity check *)
    val check_nodes: IntSet.t -> t -> bool
    (* Symbolic variables *)
    val sv_add: int -> t -> int * t
    val sv_rem: int -> t -> t
    (* check if a set var root *)
    val setv_is_root: int -> t -> bool
    (* collect root set variables*)
    val setv_col_root: t -> IntSet.t
    (* Set variables *)
    val setv_add: ?root: bool -> ?kind: set_par_type option 
      -> ?name: string option -> int -> t -> t
    val setv_rem: int -> t -> t
    (** Comparison and join operators *)
    (* Comparison *)
    val is_le: t -> t -> bool
    (* Weak bound: serves as widening *)
    val weak_bnd: t -> t -> t
    (* Upper bound: serves as join and widening *)
    val upper_bnd: t -> t -> t
    (** Set satisfiability *)
    val set_sat: set_cons -> t -> bool
    (** Set condition test *)
    val set_guard: set_cons -> t -> t
    (** Forget (if the meaning of the sv changes) *)
    val forget: int -> t -> t (* will be used for assign *)
    (** Renaming (e.g., post join) *)
    val symvars_srename: (Offs.t * int) OffMap.t -> (int * Offs.t) node_mapping 
      -> setv_mapping option -> t -> t
    (* Synchronization of the SV environment*)
    val sve_sync_top_down: svenv_mod -> t -> t
    (* Removes all symbolic vars that are not in a given set *)
    (* may change a little bit *)
    val symvars_filter: IntSet.t -> IntSet.t -> t -> t     
  end


(** Functions to do later:
 ** These functions will be useful only when testing join. *)
(*
    (* Check the symbolic vars correspond exactly to given set *)
    val symvars_check: IntSet.t -> t -> bool (* may change a little bit *)
    (* Removes all symbolic vars that are not in a given set *)
    val symvars_filter: IntSet.t -> t -> t (* may change a little bit *)
*)
