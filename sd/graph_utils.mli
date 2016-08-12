(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_utils.mli
 **       utility functions on graphs
 ** Xavier Rival, 2011/05/21 *)
open Data_structures
open Offs

open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig
open Svenv_sig
open Dom_sig

open Gen_dom

(** Creation *)
(* Takes a set of inductive definitions *)
val graph_empty: StringSet.t -> graph

(** Pretty-printing *)
(* Conversion into strings *)
val nid_2str: nid -> string
val onode_2str: onode -> string
val nalloc_2str: nalloc -> string
val nalloc_2str_short: nalloc -> string
val node_attribute_2str: node_attribute -> string
val pt_edge_2str: bnode -> pt_edge -> string
val ind_args_2str: ind_args -> string
val ind_edge_2str: ind_edge -> string
val block_2stria: string -> int -> pt_edge Block_frag.t -> string -> string
val heap_frag_2stri: string -> nid -> heap_frag -> string
val node_2stri: string -> node -> string
val node_2str: node -> string
val graph_2stri: string -> graph -> string
val graph_2str: graph -> string
(* Compact node output *)
val heap_frag_2strc: heap_frag -> string
(* Algorithms results *)
val is_le_res_2str: is_le_res -> string
(* Hints pretty-printing *)
val hint_ug_2str: hint_ug -> string
val hint_bg_2str: hint_bg -> string
(* Node embedding pretty-printing *)
val node_emb_2str: node_emb -> string


(** Reachability inside the graph *)
(* this function is exported specifically for the list_domain *)
val pt_edge_block_frag_reach: pt_edge Block_frag.t -> IntSet.t

(** Sanity checks *)
val graph_sanity_check: string -> graph -> unit

(** Number of edges (serves as a weak emptiness test) *)
val num_edges: graph -> int

(** Node operations *)
(* Node membership *)
val node_mem: int -> graph -> bool
(* Node accessor *)
val node_find: int -> graph -> node
(* Kind of the memory region attached to an SV *)
val sv_kind: int -> graph -> region_kind
(* Addition of a new node with known id (crashes if already exists) *)
val sv_add: ?attr:node_attribute -> ?root: bool -> int -> ntyp -> nalloc
  -> graph -> graph
(* Addition of a new, fresh node *)
val sv_add_fresh: ?attr:node_attribute -> ?root: bool -> ntyp -> nalloc
  -> graph -> nid * graph
(* Releasing a root *)
val sv_unroot: int -> graph -> graph
(* Removal of a node *)
val sv_rem: int -> graph -> graph
(* Checks whether a node is the root of an inductive *)
val node_is_ind: int -> graph -> bool
(* Get name of inductive attached to node, if any *)
val ind_of_node: node -> string option
(* Checks whether a node has points-to edges *)
val node_is_pt: int -> graph -> bool
(* Checks whether a node is placed in memory *)
val node_is_placed: node -> bool
(* Asserts the node must be placed; crashes otherwise *)
val node_assert_placed: string -> node -> unit
(* Assume a node is placed (when its value is discovered to be an address) *)
val node_assume_placed: int -> graph -> graph

(* Returns the set of all nodes *)
val get_all_nodes: graph -> IntSet.t
(* Returns the predecessors of a node *)
val get_predecessors_of_node: int -> graph -> IntSet.t
(* Collect offsets from a base address *)
val collect_offsets: int -> graph -> OffSet.t -> OffSet.t

(** Points-to edges operations *)
(* Existence of a points-to edge *)
val pt_edge_mem: onode -> graph -> bool
(* Creation of a block points to edge *)
val pt_edge_block_create: nid -> pt_edge -> graph -> graph
(* Appends a field at the end of a block *)
val pt_edge_block_append:
    ?nochk: bool (* de-activates check that bounds coincide (join) *)
  -> bnode -> pt_edge -> graph -> graph
(* Removal of a bunch of points-to edges from a node *)
val pt_edge_block_destroy: nid -> graph -> graph
(* Try to decide if an offset range is in a single points-to edge
 *  of a fragmentation, and if so, return its destination *)
val pt_edge_find_interval: (n_cons -> bool)
  -> nid (* node representing the base address *)
    -> Offs.t (* minimum offset of the range being looked for *)
      -> int       (* size of the range being looked for *)
        -> graph -> pt_edge option
(* Splitting of a points-to edge *)
val pt_edge_split: (n_cons -> bool) -> bnode -> Offs.size -> graph -> graph
(* Retrieval algorithm that encapsulates the search for extract and replace *)
val pt_edge_localize_in_graph:
    (n_cons -> bool) -> onode -> int -> graph -> pt_edge option
(* Replacement of a points-to edge by another *)
val pt_edge_replace:
    (n_cons -> bool) -> onode -> pt_edge -> graph -> graph
(* Extraction of a points to edge: reads, after split if necessary *)
val pt_edge_extract:
    (n_cons -> bool) -> onode -> int -> graph -> graph * pt_edge
(* Extend the search to other nodes, that are equal to another node *)
val pt_edge_localize_in_equal:
    (n_cons -> bool) -> onode -> graph -> PairSet.t

(** Inductive parameters applications *)
(* Empty set of arguments *)
val ind_args_empty: ind_args
(* Making lists of arguments *)
val ind_args_1_make: ntyp -> int -> graph -> nid list * graph
(* Make a new inductive edge with fresh arg nodes *)
val ind_edge_make: string -> nid list -> int -> graph -> ind_edge * graph

(** Inductive edges operations *)
(* Retrieve an inductive edge *)
val ind_edge_find: nid -> graph -> ind_edge
(* Inductive edge addition, removal *)
val ind_edge_add: nid -> ind_edge -> graph -> graph
val ind_edge_rem: nid -> graph -> graph
(* Function extracting *one* *inductive* edge (for is_le) *)
val ind_edge_extract_single: graph -> bool * (int * ind_edge) option

(** Segment edges operations *)
(* This code should be temporary *)
val seg_edge_find: nid -> graph -> seg_edge
(* Addition of a segment edge *)
val seg_edge_add: nid -> seg_edge -> graph -> graph
(* Removal of a segment edge *)
val seg_edge_rem: nid -> graph -> graph
(* find sources of segments to some given node *)
val seg_edge_find_to: nid -> graph -> IntSet.t

(** Inductives and segments *)
(* Extraction + Removal of an inductive or segment edge *)
val ind_or_seg_edge_find_rem: nid -> graph
  -> ind_edge * (nid * ind_args) option * graph
(* Asserting that some inductives have no parameters of a certain kind
 * (useful for weakening rules that do not support parameters yet) *)
val assert_no_ptr_arg: string -> ind_args -> unit
val assert_no_int_arg: string -> ind_args -> unit
val assert_no_arg:     string -> ind_args -> unit

(** Memory management *)
(* Allocation and free of a memory block *)
val mark_alloc: nid -> int -> graph -> graph
val mark_free: nid -> graph -> graph

(** Tests that can be (partly) evaluated in the graphs *)
(* Equalities generated by the knowledge a segment be empty *)
val empty_segment_equalities: int -> seg_edge -> PairSet.t
(* Reduction of a segment known to be empty *)
val red_empty_segment: nid -> graph -> graph * PairSet.t
(* Reduction: merging nodes that denote the same concrete value *)
val graph_merge_eq_nodes:
    (n_cons -> bool) -> PairSet.t -> graph -> graph * int IntMap.t
(* whether a graph + a condition are not compatible
 * (i.e., we should consider _|_) *)
val graph_guard: bool -> n_cons -> graph -> guard_res

(** Sat for conditions that can be partly evaluated in the graphs *)
(* Check if an SV disequality constraint is satisfied in a graph *)
val sat_graph_diseq: graph -> int -> int -> bool

(** Segment splitting, for unfolding *)
val seg_split: nid -> graph -> graph * nid

(** Utilities *)
val node_attribute_lub: node_attribute -> node_attribute -> node_attribute
val get_node: int -> graph -> node
(* For join, creation of a graph with a set of roots, from two graphs *)
val init_graph_from_roots:
    bool -> (int * int) IntMap.t -> graph -> graph -> graph
(* A sub-memory specific utility function:
 * - given a (node,offset) pair, search whether there exist an edge
 *   pointing to it *)
val node_offset_is_referred: graph -> int * Offs.t -> bool

(** Latex output *)
val latex_output: (int, string) PMap.t -> out_channel -> graph -> unit

(** Ensuring consistency with numerical values *)
val sve_sync_bot_up: graph -> graph * svenv_mod

(** Garbage collection support *)
(* Removal of all nodes not reachable from a set of roots *)
val gc_incr: int Aa_sets.t -> graph -> graph
val gc: int Aa_sets.t -> graph -> graph

(** Functions on node injections (for is_le) *)
module Nemb:
    sig
      val empty: node_embedding
      (* To string, compact version *)
      val ne_2str: node_embedding -> string
      (* To string, long version *)
      val ne_full_2stri: string -> node_embedding -> string
      (* Tests membership *)
      val mem: int -> node_embedding -> bool
      (* Find an element in the mapping *)
      val find: int -> node_embedding -> int
      (* Add an element to the mapping *)
      val add: int -> int -> node_embedding -> node_embedding
      (* Initialization *)
      val init: node_emb -> node_embedding
      (* Extraction of siblings information *)
      val siblings: node_embedding -> IntSet.t IntMap.t
    end

(** Functions on node weak injections (for directed weakening) *)
module Nwkinj:
    sig
      val empty: node_wkinj
      (* Verification of existence of a mapping *)
      val mem: node_wkinj -> int * int -> int -> bool
      (* Find function, may raise Not_found *)
      val find: node_wkinj -> int * int -> int
      (* Addition of a mapping *)
      val add: node_wkinj -> int * int -> int -> node_wkinj
      (* To string, long and indented version *)
      val wi_2stri: string -> node_wkinj -> string
    end

(** Functions on node relations (for join) *)
module Nrel:
    sig
      val empty: node_relation
      (* Consistency check *)
      val check: node_relation -> bool
      (* Verification of existence of a mapping *)
      val mem: node_relation -> int * int -> int -> bool
      (* Find function, may raise Not_found *)
      val find: node_relation -> int * int -> int
      (* Find function from out, may raise Not_found *)
      val find_p: node_relation -> int -> int * int
      (* Addition of a mapping *)
      val add: node_relation -> int * int -> int -> node_relation
      (* To string, long and indented version *)
      val nr_2stri: string -> node_relation -> string
      (* To string, compact version *)
      val nr_2strc: node_relation -> string
      (* Collect nodes associated to other side *)
      val siblings: side -> int -> node_relation -> IntSet.t
      (* Search for nodes that have multiple right matches *)
      val mult_bind_candidates: side -> node_relation -> IntSet.t -> IntSet.t
      (* Fold function *)
      val fold: (int -> (int * int) -> 'a -> 'a) -> node_relation -> 'a -> 'a
    end

(** Operations on encoded graph edge components *)
val is_segment: Graph_sig.step -> bool
val is_offset: Graph_sig.step -> bool

(** Operations on abs_graph_arg: helping join *)
(* Check whether a segment extension could be performed *)
val is_bseg_ext: abs_graph_arg option -> int  
  -> abs_graph_arg option -> int -> bool
(* Check whether a segment intro will be performed *)
val is_bseg_intro: abs_graph_arg option -> int  
  -> abs_graph_arg option -> int -> bool

(* choose destination nodes for seg_intro from encode graph *)
val choose_dst: int -> abs_graph_arg option -> IntSet.t -> IntSet.t

(** Operations on "join_arg" type: join with additional arguments *)
(* Translation of join argument *)
val tr_join_arg: (n_cons -> bool) -> graph * join_ele -> graph * join_arg
(* Find end points for segment extension *)
val seg_extension_end: int -> join_arg -> (int * string) option
(* Find a node in encoded graph *)
val encode_node_find: int -> join_arg -> bool
(* Remove node and related edges in encoded graph *)
val remove_node: int -> int -> join_arg -> join_arg
(* Consume pt in encoded graph *)
val encode_pt_pt: onode -> onode -> join_arg -> join_arg

(* Collect all inductive definitions used in a graph *)
val collect_inds: graph -> StringSet.t
