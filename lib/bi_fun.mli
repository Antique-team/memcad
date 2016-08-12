(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: bi_fun.mli
 **       Bi-directional representation of finite functions
 **       i.e., with both the function and its inverse
 ** Xavier Rival, 2013/07/20 *)

(* Finite function structure *)
type ('a, 'b) t

(** Emptiness *)
(* Empty, not assumed bijection *)
val empty: ('a, 'b) t
(* Empty, assumed bijection (safety checks that it remains one) *)
val empty_inj: ('a, 'b) t
(* Test *)
val is_empty: ('a, 'b) t -> bool

(** Pretty-printing *)
(* Simple pp, of only one table (for now) *)
val t_2str: string -> ('a -> string) -> ('b -> string) -> ('a, 'b) t -> string
(* Full pretty-printing *)
val t_2strf: ('a -> string) -> ('b -> string) -> ('a, 'b) t -> string

(** Sanity check *)
val sanity_check: string -> ('a, 'b) t -> unit

(** Operations *)
(* Size *)
val size: ('a, 'b) t -> int
(* Membership *)
val mem_dir: 'a -> ('a, 'b) t -> bool
val mem_inv: 'b -> ('a, 'b) t -> bool
(* Direct image *)
val image: 'a -> ('a, 'b) t -> 'b
val image_opt: 'a -> ('a, 'b) t -> 'b option
val whole_image: ('a, 'b) t -> 'b Aa_sets.t
(* Reverse image *)
val inverse: 'b -> ('a, 'b) t  -> 'a Aa_sets.t
val inverse_opt: 'b -> ('a, 'b) t  -> 'a option
val inverse_inj: 'b -> ('a, 'b) t -> 'a
(* Removal *)
val rem_dir: 'a -> ('a, 'b) t -> ('a, 'b) t
val rem_inv: 'b -> ('a, 'b) t -> ('a, 'b) t
(* Addition *)
val add: 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t

(** Iter and Fold operations **)
(* Iter on the domain *)
val iter_dir: ('a -> 'b -> unit) -> ('a, 'b) t -> unit
(* Fold on the domain *)
val fold_dom: ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
(* Fold on the image *)
val fold_inverse: ('b -> 'a Aa_sets.t -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
