(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: bound_sig.ml
 **       A naive implementation of bounds
 ** Xavier Rival, Pascal Sotin, 2012/04/29 *)
open Data_structures
open Nd_sig
open Off_sig

module type BOUNDS =
  sig
    (** Type of bounds *)
    (* Bound set implementation has a "main offset" and a set of others *)
    type t
    (* Size is the same as in the module Offs *)
    type size = Offs.size

    (** Printing *)
    val t_2str: t -> string
        
    (** Constructors *)
    (* From an offset *)
    val of_offs: Offs.t -> t
    (* From a set of offsets *)
    val of_offset: Offs.OffSet.t -> t
    (* Null offset *)
    val zero: t
    (* Integer offset *)
    val of_int: int -> t
    (* String offset *)
    val of_string: string -> t
    (* Field (string+int) offset *)
    val of_field: string * int -> t
    (* From a numerical domain expression *)
    val of_n_expr: n_expr -> t
        
    (** Extraction *)
    (* To offset *)
    val to_offs: t -> Offs.t
    (* To list of offsets *)
    val to_off_list: t -> Offs.t list

    (** Merging *)
    val merge: t -> t -> t

    (** Intersection (keep offsets in both members) *)
    val inter: t -> t -> t

    (** Comparisons *)
    (* Whether an offset is constant *)
    val t_is_const: t -> bool
    (* Compare, syntactic on AST, to build sets *)
    val compare: t -> t -> int
    (* Equality test *)
    val eq: t -> t -> bool
    (* Compatibility test *)
    val compat: t -> t -> t option
    (* Compare, semantic *)
    val leq: (n_cons -> bool) -> t -> t -> bool
    (* Nullness test *)
    val is_zero: t -> bool
    (* Semantic comparison of bounds:
     *  - returns Some i (i \in {-1,0,1}) if it can be decided
     *  - otherwise, returns None *)
    val t_order: (n_cons -> bool) -> t -> t -> int option

    (** Arithmetics *)
    val add_int: t -> int -> t
    val add: t -> t -> t
    val add_size: t -> size -> t
    val sub: t -> t -> size
    val sub_t: t -> t -> t
    val mul_int: t -> int -> t
    (* Split a bound modulo some given stride *)
    val modulo_split: int -> t -> (t * t) (* aligned + bias *)
    (* Checks whether is aligned on stride *)
    val is_on_stride: int -> t -> bool

    (** Utilities *)
    (* Ids of symbolic variables *)
    val t_sym_var_ids_add: IntSet.t -> t -> IntSet.t

    (** Unification *)
    val unify: t -> t -> (int * int * int) list * t
    val unify_all: t -> t -> ((int * int * int) list * t) option
    
    (** Renaming *)
    val rename: int IntMap.t -> t -> t
  end
