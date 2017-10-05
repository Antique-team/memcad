(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_utils.mli
 ** utilities for the simplified list domain
 ** Xavier Rival, 2014/02/24 *)
open Data_structures

open Graph_sig
open Ind_sig
open List_sig
open Nd_sig
open Set_sig
open Sv_sig
open Svenv_sig

open Gen_dom

open Inst_utils

(** Empty memory *)
val lmem_empty: lmem

val lmem_reach: lmem -> IntSet.t -> IntSet.t

(** Pretty-printing *)
val set_equa_2str: set_equa -> string
val l_def_2stri: string -> l_def -> string
val l_call_2stri: string -> l_call -> string
val l_call_2strc: l_call -> string
val l_call_setvars_2str: l_call -> string
val lheap_frag_2stri: string -> nid -> lheap_frag -> string
val lnode_2stri: string -> lnode -> string
val lmem_2stri: ?refcount:bool -> string -> lmem -> string
val get_def: lmem -> l_def 
val get_maya_off: int -> lmem ->int list 
val lseg_2list: int -> lmem -> lmem

(** Sanity checks *)
val sanity_check: string -> lmem -> unit

(** Management of SVs *)
val sve_sync_bot_up: lmem -> lmem * svenv_mod

(** Symbolic variables operations *)
val sv_mem: int -> lmem -> bool
val sv_find: int -> lmem -> lnode
val sv_kind: int -> lmem -> region_kind
val sv_add: ?root:bool -> int -> ntyp -> lmem -> lmem
val sv_add_fresh: ?root:bool -> ntyp -> lmem -> int * lmem
val sv_rem: int -> lmem -> lmem
val sv_col: lmem -> IntSet.t
val sv_is_ind: int -> lmem -> bool
(* Root operations *)
val sv_root:   int -> lmem -> lmem
val sv_unroot: int -> lmem -> lmem

(** Management of set variables *)
val setv_add_fresh: bool -> Set_sig.set_par_type option -> lmem -> int * lmem
val setv_add: bool -> int -> lmem -> lmem
val setv_rem: int -> lmem -> lmem
val setv_type: lmem -> int -> Set_sig.set_par_type option
val setv_is_root: lmem -> int -> bool
val setv_set: lmem -> IntSet.t
val setv_roots: lmem -> IntSet.t

(** Memory block operations *)
(* Existence of a points-to edge *)
val pt_edge_mem: onode -> lmem -> bool
(* Appends a field at the end of a block *)
val pt_edge_block_append: ?nochk: bool -> bnode -> pt_edge -> lmem -> lmem
(* Removal of a points-to block
 *  remrc: says whether refcounts should be killed (by default true) *)
val pt_edge_block_destroy: ?remrc:bool -> int -> lmem -> lmem
(* Try to decide if an offset range is in a single points-to edge
 *  of a fragmentation, and if so, return its destination *)
val pt_edge_find_interval: (n_cons -> bool)
  -> nid (* node representing the base address *)
    -> Offs.t (* minimum offset of the range being looked for *)
      -> int       (* size of the range being looked for *)
        -> lmem -> pt_edge option
(* Replacement of a points-to edge by another *)
val pt_edge_replace: (n_cons -> bool) -> onode -> pt_edge -> lmem -> lmem
(* Extraction of a points to edge: reads, after split if necessary *)
val pt_edge_extract: (n_cons -> bool) -> onode -> int -> lmem -> lmem * pt_edge

(* Addition of a list edge *)
val list_edge_add: int -> l_call -> lmem -> lmem
(* Removal of a list edge *)
val list_edge_rem: int -> lmem -> lmem

(* Addition of a segment edge *)
val lseg_edge_add: int -> int -> l_call -> lmem -> lmem
(* Removal of a segment edge *)
val lseg_edge_rem: int -> lmem -> lmem

(* Number of remaining edges *)
val num_edges: lmem -> int

(** Garbage collection support *)
(* Removal of all nodes not reachable from a set of roots *)
val gc: int Aa_sets.t -> lmem -> lmem * IntSet.t

(** Inductive set parameters construction *)
(* - unfold a seg or an ind edge presented by lc: l_call in the right side
 * - with a new segment
 * - and a new seg or an new ind edge
 * - also returns the set of removed SETVs
 * - and          the set of all new SETVs *)
val gen_ind_setpars: lmem -> l_call
  -> lmem * l_call * l_call * (Set_sig.set_cons list) * IntSet.t * IntSet.t
(* Splitting an inductive predicate into a pair of calls;
 * this function takes care of the parameters and prepares a list of
 * set constraints that should also be taken into account to precisely
 * account for the SETV parameter kinds (const, head, etc) *)
val split_indpredpars: l_call -> lmem -> lmem * l_call * l_call * set_cons list

(** Reduction *)
val lmem_rename_sv: nid -> nid -> lmem -> lmem
val lmem_guard: n_cons -> lmem -> lguard_res

(** Utilities for join *)
(* Initialization of the join graph:
 * returns:
 *  - new shape
 *  - setvs to add in the left (before the join)
 *  - setvs to add in the right (before the join)
 *  - setvs to remove in both sides, after the join *)
val init_from_roots:
    (int * int) IntMap.t -> (int * int) IntMap.t -> lmem -> lmem
      -> lmem * IntSet.t * IntSet.t * IntSet.t
(* Comparison of list descriptors *)
val l_call_compare: l_call -> l_call -> int

(** Inductive definitions *)
(* Global map of list-like inductive definitions *)
val list_ind_defs: l_def StringMap.t ref
(* Experimental code, to try to look for list like inductive defs *)
val exp_search_lists: unit -> unit

(* Utilities needed for list visualization *)
val nodes_of_lmem: lmem -> lnode list
val lnode_reach: lnode -> IntSet.t
