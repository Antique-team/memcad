(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: refcount.mli
 **       A basic (persistent) reference counting structure
 ** Xavier Rival, 2016/04/11 *)

(** Structure describing reference counts *)
type 'a t


(** Basic operations *)

(* Empty *)
val empty: 'a t

(* Pp *)
val t_2stri: ('a -> string) -> string -> 'a t -> string

(* Reference addition/removal *)
val incr: 'a -> 'a t -> 'a t
val decr: 'a -> 'a t -> 'a t * bool (* true if down to 0 *)

(* Check if positive reference *)
val hasref: 'a -> 'a t -> bool (* true if >= 1 *)
