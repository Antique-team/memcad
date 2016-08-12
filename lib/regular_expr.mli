(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: regular_expr.mli
 ** generic regular expression
 ** Antoine Toubhans, 2012/05/29 *)
open Data_structures
open Flags
open Lib

(** type of regex *)
type 'a t

(** constructors *)
(* 0 *)
val zero: 'a t
(* 1 *)
val one: 'a t
(* a -> a *)
val label: 'a -> 'a t
(* L1 -> L2 -> L1+L2 *)
val plus: 'a t -> 'a t -> 'a t
(* L1 -> L2 -> L1.L2 *)
val concat: 'a t -> 'a t -> 'a t
(* L -> L* *)
val star: 'a t -> 'a t
(* { a1, ..., an } -> (a1+...+an)* *)
val set_2t: 'a PSet.t -> 'a t

(** pretty printing *)
val t_2str: ('a -> string) -> 'a t -> string

(** testing tools *)
val is_label: 'a t -> 'a option
(* A regular expression is rigid iff its corresponding set of words
 *   is a singleton.
 * function "is_rigid" is conservative,
 *   e.g., it returns false on "0 + 1" *)
val is_rigid: 'a t -> bool
(* F regular expression is finite
 *   iff its corresponding set of words is finite
 * function "is_finite" is conservative;
 *   e.g., it returns false on "0*" or "1*" *)
val is_finite: 'a t -> bool
(* does the empty word belong to the set of words corresponding
 * to some regular expression *)
val has_empty: 'a t -> bool

(** comparison tools *)
(* language inclusion (conservative) *)
val is_le: 'a t -> 'a t -> bool
(* semantic equality (conservative) *)
val eq: 'a t -> 'a t -> bool

(** transformation tools *)
(* simplifying *)
val simplify: 'a t -> 'a t 
(* find generators of a language L i.e
 * labels { a1, a2, ... an } s.t.
 * L <= 1 + a1.L + ... + an.L *)
val generators: 'a t -> 'a PSet.t 
