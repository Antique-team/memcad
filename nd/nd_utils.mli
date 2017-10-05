(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_utils.mli
 ** utilities for numerical domain
 ** Xavier Rival, 2011/07/03 *)
open Data_structures
open Nd_sig
(* External: Apron components *)
open Apron

(** Managing Apron variables *)
val make_var: int -> Var.t

(** SV printers *)
(* Nodes *)
val node_2str: int -> string
(* Variables *)
val var_2int: Var.t -> int
val var_2str: Var.t -> string

(* Turning interval into string *)
val interv_2str:  interval -> string  

(** Apron interface helpers *)
(* Turning Apron level 0 structures into strings *)
val coeff_2str: Coeff.t -> string
val unop_2str: Texpr0.unop -> string
val binop_2str: Texpr0.binop -> string
val cons_op_2str: Lincons0.typ -> string
val cons_trailer_2str: Lincons0.typ -> string
(* Turning Apron level 1 structures into strings *)
val texpr1_2str: sv_namer -> Texpr1.t -> string
(* Debug pp for environments *)
val environment_2str: sv_namer -> Environment.t -> string

(* Turns a set of constraints into a string *)
val linconsarray_2stri: sv_namer -> string -> Lincons1.earray -> string

(** Numeric domain expressions *)
(* Conversion into strings and pretty-printing *)
val n_expr_2str: n_expr -> string
val n_cons_2str: n_cons -> string
(* Translation into Apron expressions, with environment *)
val translate_n_expr: Environment.t -> n_expr -> Texpr1.t
val translate_n_cons: Environment.t -> n_cons -> Tcons1.t
(* Map translations *)
val n_expr_map: (int -> int) -> n_expr -> n_expr
val n_cons_map: (int -> int) -> n_cons -> n_cons
(* Substitutions *)
val n_expr_subst: (int -> n_expr) -> n_expr -> n_expr
val n_cons_subst: (int -> n_expr) -> n_cons -> n_cons
(* Iterators (for searching variables or verifying variables properties) *)
val n_expr_fold: (int -> 'a -> 'a) -> n_expr -> 'a -> 'a
val n_cons_fold: (int -> 'a -> 'a) -> n_cons -> 'a -> 'a
(* Check absence of Ne_rand *)
val n_expr_no_rand: n_expr -> bool
(* Negation of an n_cons *)
val neg_n_cons: n_cons -> n_cons
(* Simplification of constraints, and pairs of expressions bound by an equality
 * or disequality constraint *)
val n_expr_simplify: n_expr * n_expr -> n_expr * n_expr
val n_cons_simplify: n_cons -> n_cons
(* Decomposition to turn into a pair (base, offset),
 * when known to be an address
 * (may return None, if no decompisition is found) *)
val n_expr_decomp_base_off: n_expr -> (int * n_expr) option

(** Widening utilities: make constraints for widening thresholds *)
val make_widening_thresholds: Environment.t -> Lincons1.earray

(** Mapping functions *)
(* Empty mapping *)
val node_mapping_empty: 'a node_mapping
(* Addition of a new node *)
val add_to_mapping: int -> int -> 'a node_mapping -> 'a node_mapping
(* Pretty-printing *)
val node_mapping_2str: 'a node_mapping -> string

(** Decomposition *)
(* Splitting of an expression into a pair formed of a variable 
 * and a linear combination of factors *)
val decomp_lin: n_expr -> int * n_expr
val decomp_lin_opt: n_expr -> (int * n_expr) option

(** Atoms used in add_eqs and add_diseqs *)
(* Constraints involve atoms *)
type atom =
  | Acst of int (* stands for integer constant *)
  | Anode of int (* stands for a graph node *)
(* Ordered structure *)
module AtomOrd: (Set.OrderedType with type t = atom)
(* Dictionaries *)
module AtomSet: (Set.S with type elt = atom)
module AtomMap: (Map.S with type key = atom)
(* Pretty-printing *)
val atom_2str: sv_namer -> atom -> string
val atomset_2str: sv_namer -> AtomSet.t -> string
(* Conversion of n_expressions to atom *)
val n_expr_2atom: n_expr -> atom option
