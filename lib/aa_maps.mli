(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: aa_maps.mli
 **       Arne Anderson implementation for polymorphic maps
 ** Xavier Rival, 2012/11/19 *)

type ('a, 'b) t

(** Basic functions (accesses, add, remove) *)
(* Empty element *)
val empty: ('a, 'b) t
(* Emptiness test *)
val is_empty: ('a, 'b) t -> bool
(* Membership test *)
val mem: 'a -> ('a, 'b) t -> bool
(* Finding an element *)
val find: 'a -> ('a, 'b) t -> 'b
(* Adding an element *)
val add: 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t
(* Removing an element *)
val remove: 'a -> ('a, 'b) t -> ('a, 'b) t
(* Singleton map *)
val singleton: 'a -> 'b -> ('a, 'b) t

(** Iterators *)
val iter: ('a -> 'b -> unit) -> ('a, 'b) t -> unit
val map: ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
val fold_left: ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
val fold_right: ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
val fold: ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c

(** Extremal elements *)
val min_binding: ('a, 'b) t -> 'a * 'b
val min_key: ('a, 'b) t -> 'a
val choose: ('a, 'b) t -> 'a * 'b

(** Printing *)
val t_2str: string -> string -> ('a -> 'b -> string) -> ('a, 'b) t -> string

(** Utilities *)
val size: ('a, 'b) t -> int
