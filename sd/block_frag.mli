(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: block_frag.mli
 **       Partitions of contiguous blocks
 ** Xavier Rival and Pascal Sotin, 2012/04/24 *)
open Data_structures
open Nd_sig

(** Block partition data type, with:
 **  'a: keys, ie offsets;
 **  'b: values, ie destination nodes *)

type bound = (*Offs.t*) Bounds.t

(* A record in the map encloses an edge, a prev and a next *)
type 'a block_entry

(* A block_map contains a set of entries, bound to offsets:
 *  key->value *)
type 'a block_map

(* A block fragmentation also contains the first and last values *)
type 'a block_frag
type 'a t = 'a block_frag


(** Pretty-printing *)
(* Parametric version, prints contents *)
val block_entry_2str: ('a -> string) -> 'a block_entry -> string
val block_frag_2stri: string -> ('a -> string) -> 'a block_frag -> string
val block_frag_2str: ('a -> string) -> 'a block_frag -> string
(* Short version, will not print contents *)
(* val block_frag_2strc: 'a t -> string *)


(** Creation *)
(* Empty block *)
val create_empty: bound -> 'a block_frag
val create_block_span: bound -> bound -> 'a -> 'a block_frag


(** Emptiness *)
val is_empty: 'a block_frag -> bool
val is_not_empty: 'a block_frag -> bool
val cardinal: 'a block_frag -> int
val map_to_list: 'a block_frag -> (bound * 'a block_entry) list
val elt: 'a block_entry -> 'a (* FBR: move this to the right place *)
val byte_size: 'a block_frag -> int 


(** Functions for accessing an offset *)
(* Get the first bound *)
val first_bound: 'a block_frag -> bound
(* Get the end bound *)
val end_bound: 'a block_frag -> bound
(* Checking for membership *)
val mem: bound -> 'a block_frag -> bool
(* Find: extraction of a points-to edge *)
val find_addr: bound -> 'a block_frag -> 'a
(* Find using a sat function, in case straight access fails *)
val find_addr_sat: (n_cons -> bool) -> bound -> 'a block_frag -> 'a
(* Extraction of a chunk, specified by a lower and an upper bound *)
val extract_chunk_sat: (n_cons -> bool) -> bound -> bound -> 'a block_frag
  -> bound * 'a block_entry
(* Find a chunk, specified by a lower and an upper bound *)
val find_chunk_sat: (n_cons -> bool) -> bound -> bound -> 'a block_frag -> 'a
(* Appends an element at the beginning of a block *)
val append_head: bound -> 'a -> 'a block_frag -> 'a block_frag
(* Appends an element at the end of a block *)
val append_tail:
    ?nochk: bool (* de-activates check that bounds coincide (join) *)
  -> bound -> bound (* begin and end bounds of the zone to add *)
    -> 'a -> 'a block_frag (* element to add and block *)
      -> 'a block_frag (* block partition with additional sub-block appended *)
(* Replacing a field with another one *)
val replace_sat: (n_cons -> bool)
  -> bound -> 'a -> 'a block_frag -> 'a block_frag
(* Splitting of a fragmentation:
 *  - removes one points-to edge;
 *  - adds two points-to edges *)
val split_sat: (n_cons -> bool)
  -> bound -> bound -> bound -> 'a -> 'a -> 'a block_frag -> 'a block_frag


(** Iterators *)

(* Map function, with action on keys and on values *)
val map_bound: (bound -> bound) -> ('a -> 'a) -> 'a block_frag -> 'a block_frag
(* Iter function (over the map structure) *)
val iter_base: (bound -> 'a -> unit) -> 'a block_frag -> unit 
(* Iter function, over the bounds (not the elements) *)
val iter_bound: (bound -> unit) -> 'a block_frag -> unit
(* Fold over the map structure (i.e., not the list structure *)
val fold_base: (bound -> 'a -> 'b -> 'b) -> 'a block_frag -> 'b -> 'b
(* Fold over the list structure, i.e., in the ascending order *)
val fold_list_base: (bound -> 'a -> 'b -> 'b) -> 'a block_frag -> 'b -> 'b
(* Fold over the list structure, i.e., in the ascending order,
 * up to some given depth;
 * it will crash if there are not enough elements in the structure *)
val fold_list_depth: (bound -> 'a -> 'b -> 'b)
  -> int (* depth up to which the traversal will be done *)
    -> 'a block_frag -> 'b -> 'b
(* Fold over the list structure, with two arguments *)
val fold_list2_bound2: (* iterated function applies to two pairs of bounds *)
    (bound * bound -> bound * bound -> 'a -> 'a -> 'b -> 'b)
  -> 'a t -> 'a t -> 'b -> 'b
val fold_list2_bound1: (* iterated function applies to one pair of bounds *)
    (bound -> bound -> 'b -> 'b) -> 'a t -> 'a t -> 'b -> 'b (* incl. end *)
val fold_list2_base: (* iterated function applies to one pair of bases *)
    (bound -> bound -> 'a -> 'a -> 'b -> 'b) -> 'a t -> 'a t -> 'b -> 'b
(* Computation of reach information *)
val reach: (IntSet.t -> 'a -> IntSet.t) -> 'a block_frag -> IntSet.t


(** Second unification attempt *)
(* Note: we should be doing some clean up here *)
val extract_rem_first: 'a block_frag -> (bound * 'a) * 'a block_frag
