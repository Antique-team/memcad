(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_eqs.mli
 **       equalities between two sets of symbolic variables
 ** Antoine Toubhans, 2013/12/02 *)

(** Main type *)

(* Equalities between elements of type 'a and elements of type 'b *)
type ('a, 'b) t

(* Empty set of equalities *)
val empty: ('a, 'b) t

(* Pretty printing *)
val t_2stri: ('a -> string) -> ('b -> string) -> string -> ('a, 'b) t -> string

(* Sanity check *)
val sanity_check: string -> ('a, 'b) t -> unit

(** Read equalities *)

(* Are two element equal *)
val are_eq: 'a -> 'b -> ('a, 'b) t -> bool

(* Find a "b" element that is equal to an "a" element *)
val find_eq_a: 'a -> ('a, 'b) t -> 'b option

(* Find an "a" element that is equal to a "b" element *)
val find_eq_b: 'b -> ('a, 'b) t -> 'a option

(** Write / Unwrite equalities *)

(* Write equality [a=b] *)
val write_eq: 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t

(* Forget about an "a" element *)
val forget_a: 'a -> ('a, 'b) t -> ('a, 'b) t

(* Forget about a "b" element *)
val forget_b: 'b -> ('a, 'b) t -> ('a, 'b) t

(** Iterators *)

(* Iter, over equivalence classes *)
val iter: ('a list -> 'b list -> unit) -> ('a, 'b) t -> unit

(* Fold, over equivalence classes *)
val fold: ('a list -> 'b list -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
