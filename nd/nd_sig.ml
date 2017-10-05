(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_sig.ml
 **       numerical domain layers signatures
 ** Xavier Rival, 2011/07/03 *)
open Apron
open Data_structures

(** For incremental bottom reduction *)
(* When an abstract value representing _|_ is encountered,
 * and if Flags.do_raise_on_bottom is set,
 * the exception below may be raised *)
exception Bottom

(** Carrying out names through printers *)
type sv_namer = string IntMap.t (* maps certain SVs to a string *)

(** A format of expressions and constraints for the numeric domain only *)
(* It is rather close to Apron expressions, but there are differences:
 *  - no environment, no "string" vars
 *  - no notion of type (for now)
 *  - Ne_rand may evaluate to any value; it should appear only at the top-level
 *)
type n_expr =
  | Ne_rand (* random value *)
  | Ne_csti of int (* for now, only integer values *)
  | Ne_cstc of char
  | Ne_var of int (* corresponds to a node in the graph *)
  | Ne_bin of Texpr1.binop * n_expr * n_expr
type n_cons =
  | Nc_rand
  | Nc_bool of bool
  | Nc_cons of Tcons1.typ * n_expr * n_expr

(** Support for arrays requires exporting range information *)
(* An interval: None means infinity *)
type interval = 
    { intv_inf: int option;
      intv_sup: int option; }

(** For the interface with the shape domain *)
(* Mapping from one join argument into the result
 * - nm_map:
 *     map a nodeID into: a nodeID + a set of other nodesIDs
 *     (renaming performed in two steps: first rename; second add equalities);
 * - nm_rem:
 *     nodeIDs to remove
 * - nm_suboff:
 *     function to decide admissible sub-memory offsets,
 *     i.e., sub-memory environment offsets to preserve *)
type 'a node_mapping =
    { nm_map:    (int * IntSet.t) IntMap.t ; (* mapping n -> elt+set *)
      nm_rem:    IntSet.t ; (* nodes to abstract away *)
      nm_suboff: ('a -> bool) ; (* admissible submem offsets *) }


(** Signature of the numerical domain, without a bottom element *)
module type DOM_NUM_NB =
  sig
    include INTROSPECT
    type t
    (* Bottom element (might be detected) *)
    val is_bot: t -> bool
    (* Top element *)
    val top: t
    (* Pretty-printing *)
    val t_2stri: sv_namer -> string -> t -> string
    (* Variables managemement *)
    val add_node: int -> t -> t
    val rem_node: int -> t -> t
    val vars_srename: 'a node_mapping -> t -> t
    val check_nodes: IntSet.t -> t -> bool
    val nodes_filter: IntSet.t -> t -> t
    (** Comparison, Join and Widening operators *)
    val is_le: t -> t -> (int -> int -> bool) -> bool
    val join: t -> t -> t
    val widen: t -> t -> t
    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    val sat: n_cons -> t -> bool
    (** Transfer functions *)
    val assign: int -> n_expr -> t -> t
    val guard: bool -> n_cons -> t -> t
    (** Utilities for the abstract domain *)
    val simplify_n_expr: t -> n_expr -> n_expr
    (** Summarizing dimensions related operations *)
    val expand: int -> int -> t -> t
    val compact: int -> int -> t -> t
    (** Conjunction *)
    val meet: t -> t -> t
    (** Drop information on an SV *)
    val sv_forget: int -> t -> t
    (** Export of range information *)
    val bound_variable: int -> t -> interval
    (** Extract the set of all SVs *)
    val get_svs: t -> IntSet.t
    (** Extract all SVs that are equal to a given SV *)
    val get_eq_class: int -> t -> IntSet.t
  end


(** Signature of the numerical domain, with a bottom element *)
module type DOM_NUM =
  sig
    include INTROSPECT
    type t
    (* Bottom element *)
    val bot: t
    val is_bot: t -> bool
    (* Top element *)
    val top: t
    (* Pretty-printing *)
    val t_2stri: sv_namer -> string -> t -> string
    (* Variables managemement *)
    val add_node: int -> t -> t
    val rem_node: int -> t -> t
    val vars_srename: 'a node_mapping -> t -> t
    val check_nodes: IntSet.t -> t -> bool
    val nodes_filter: IntSet.t -> t -> t
    (** Comparison and Join operators *)
    val is_le: t -> t -> (int -> int -> bool) -> bool
    val join: t -> t -> t
    val widen: t -> t -> t
    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    val sat: n_cons -> t -> bool
    (** Transfer functions *)
    val assign: int -> n_expr -> t -> t
    val guard: bool -> n_cons -> t -> t
    (** Utilities for the abstract domain *)
    val simplify_n_expr: t -> n_expr -> n_expr
    (** Summarizing dimensions related operations *)
    val expand: int -> int -> t -> t
    val compact: int -> int -> t -> t
    (** Conjunction of two inputs  *)
    val meet: t -> t -> t
    (** Forget the information on a dimension *)
    val sv_forget: int -> t -> t
    (** Export of range information *)
    val bound_variable: int -> t -> interval
    (** Extract the set of all SVs *)
    val get_svs: t -> IntSet.t
    (** Extract all SVs that are equal to a given SV *)
    val get_eq_class: int -> t -> IntSet.t
  end
