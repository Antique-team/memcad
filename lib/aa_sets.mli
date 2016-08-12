(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: aa_sets.mli
 **       Arne Anderson implementation for polymorphic sets
 ** Xavier Rival, 2012/11/19 *)

type 'a t

(** Basic functions (accesses, add, remove) *)
(* Empty element *)
val empty: 'a t
(* Emptiness test *)
val is_empty: 'a t -> bool
(* Membership test *)
val mem: 'a -> 'a t -> bool
(* Adding an element *)
val add: 'a -> 'a t -> 'a t
(* Removing an element *)
val remove: 'a -> 'a t -> 'a t

(** Iterators *)
val iter: ('a -> unit) -> 'a t -> unit
val fold: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

(** Extremal elements *)
val choose: 'a t -> 'a
val min_elt: 'a t -> 'a

(** Set operations *)
val singleton: 'a -> 'a t
val cardinal: 'a t -> int
val union: 'a t -> 'a t -> 'a t
val exists: ('a -> bool) -> 'a t -> bool
val filter: ('a -> bool) -> 'a t -> 'a t
val for_all: ('a -> bool) -> 'a t -> bool
val subset: 'a t -> 'a t -> bool
val equal: 'a t -> 'a t -> bool

val fold_subset: ('a t -> 'b -> 'b) -> 'a t -> 'b -> 'b

(** Printing *)
val t_2str: string -> ('a -> string) -> 'a t -> string
