(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: keygen.mli
 ** generation of keys in [0,n]
 ** Xavier Rival, 2013/05/16 *)
open Data_structures

(** Structure to keep free keys *)
type t

(** Functions over t *)
(* Sanity check *)
val sanity_check: string -> IntSet.t -> t -> unit
(* Empty *)
val empty: t
(* Pretty-printing *)
val t_2str: t -> string
(* Generate a new key *)
val gen_key: t -> t * int
(* Use a key *)
val use_key: t -> int -> t
(* Is a key used *)
val key_is_used: t -> int -> bool
(* Release a key *)
val release_key: t -> int -> t
(* Get all nodes (for debug) *)
val get_nodes: t -> IntSet.t
(* Equality test (expensive) *)
val equal: t -> t -> bool
