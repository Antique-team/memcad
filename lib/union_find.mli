(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: union_find.mli
 **       Union-Find data structure
 ** Antoine Toubhans, 2013/04/11 *)

(* Main type *)
type 'a t

(* Pretty print  *)
val t_2stri: string -> ( 'a -> string )->  'a t -> string

(* Sanity check *)
val sanity_check: string -> 'a t -> unit
(* Empty *) 
val empty: 'a t
(* Mem, returns true if an element belongs to the structure *)
val mem: 'a -> 'a t -> bool
(* Is_representative, returns true iff an id is a representive *)
val is_representative: 'a -> 'a t -> bool
(* Add, add a new element, take a representative as optional argument *)
val add: 'a -> ?rep: 'a -> 'a t -> 'a t
(* Rem, remove an element,
 * returns another element of its class if there exists so *)
val rem: 'a -> 'a t -> 'a option * 'a t
(* Rem_class, remove a whole class, given its representative element *)
val rem_class: 'a -> 'a t -> 'a t
(* Find, returns the representative of the class of a given element
 * the returned union-find element is for path compression *)
val find: 'a -> 'a t -> 'a * 'a t
(* find_class, returns the class that has a given representative *)
val find_class: 'a -> 'a t -> 'a list
(* Union r1 r2, merge two classes, given their representatives r1 and r2;
 * r1 remains a representative, r2 do not *)
val union: 'a -> 'a -> 'a t -> 'a t
val is_same_class: 'a -> 'a -> 'a t -> bool
val fold: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
(* Classes meet ? *)
val meet: 'a t -> 'a t -> 'a t
(* lift an element to the representive of a class *)
val lift_rep: 'a -> 'a t ->  'a t

(** Lattice operation *)
(* Rename, replace one element by another *)
val var_rename: 'a -> 'a -> 'a t -> 'a t
(* Is_le, Point-wise inclusion checking, returns a function from
 * Right representatives to Left representative if successful *)
val is_le: 'a t -> 'a t -> ('a, 'a) Aa_maps.t option
