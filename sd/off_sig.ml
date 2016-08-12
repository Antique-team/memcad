(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: off_sig.ml
 **       offset definitions
 ** Xavier Rival, 2011/06/29 *)
open Data_structures
open Nd_sig

module type OFF_SIG =
  sig
    (* type of offsets (in a memory block) *)
    type t
    (* type describing the size of a memory (sub-)block *)
    type size

    (** Printing *)
    val t_2str: t -> string
    val size_2str: size -> string

    (** Constructors and conversions *)
    (* Null offset, and size *)
    val zero: t
    val size_zero: size
    (* Integer offset *)
    val of_int: int -> t
    (* String offset *)
    val of_string: string -> t
    (* Field (string+int) offset *)
    val of_field: string * int -> t
    (* From a numerical domain expression *)
    val of_n_expr: n_expr -> t
    (* Size, from an integer *)
    val size_of_int: int -> size
    (* Size, from offset *)
    val to_size: t -> size
    (* Offset, from size *)
    val of_size: size -> t
    (* Turning an offset into an integer, if possible *)
    val to_int_opt: t -> int option
    val size_to_int_opt: size -> int option
    (* Turning an offset into an integer, or failing *)
    val to_int: t -> int
    (* Turning an offset into an n_expr *)    
    val to_n_expr: t -> n_expr
    val size_to_n_expr: size -> n_expr

    (** Comparisons *)
    (* Whether an offset is constant *)
    val t_is_const: t -> bool
    (* Whether a size is constant *)
    val size_is_const: size -> bool
    (* Compare, syntactic on AST, to build sets *)
    val compare: t -> t -> int
    (* Equality test *)
    val eq: t -> t -> bool
    val size_eq: size -> size -> bool
    (* Compare, semantic *)
    val leq: (n_cons -> bool) -> t -> t -> bool
    (* Nullness test *)
    val is_zero: t -> bool
    (* Semantic comparison of sizes:
     *  - returns Some i (i \in {-1,0,1}) if it can be decided
     *  - otherwise, returns None *)
    val size_order: (n_cons -> bool) -> size -> size -> int option
    (* Semantic comparison of sizes; attempts to prove that s0 <= s1 *)
    val size_leq: (n_cons -> bool) -> size -> size -> bool
    (* Idem for offsets: search for fields in physical placement order *)
    val t_order: (n_cons -> bool) -> t -> t -> int option

    (** Arithmetics *)
    val add_int: t -> int -> t
    val add: t -> t -> t
    val add_size: t -> size -> t
    val size_add_size: size -> size -> size
    val sub: t -> t -> size
    val sub_t: t -> t -> t (* hack to keep more expressiveness in join *)
    val size_sub_size: size -> size -> size
    val mul_int: t -> int -> t
    (* Split an offset modulo some given stride *)
    val modulo_split: int -> t -> (t * t) (* aligned + bias *)
    (* Checks whether is aligned on stride *)
    val is_on_stride: int -> t -> bool

    (** Utilities *)
    (* Ids of symbolic variables *)
    val t_sym_var_ids_add: IntSet.t -> t -> IntSet.t
    val size_sym_var_ids_add: IntSet.t -> size -> IntSet.t

    (** Unification *)
    val t_unify: t -> t -> ((int * int * int) list * t) option
    val size_unify: size -> size -> ((int * int * int) list * size) option
    
    (** Renaming *)
    val t_rename: int IntMap.t -> t -> t
    val size_rename: int IntMap.t -> size -> size
    val t_rename_opt: int IntMap.t -> t -> t option
  end
