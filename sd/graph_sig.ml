(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_sig.ml
 **       signatures of the main graph data-types
 ** Xavier Rival, 2011/05/19 *)
open Data_structures
open Ind_sig
open Offs
open Nd_sig
open Sv_sig
open Svenv_sig

(** Improvements to consider:
 ** - try to merge "node_wkinj" and "node_relation" (may not be doable)
 ** - try to use Bi_funs as part of these structures
 **   (would reduce the implementation size, and share code)
 **)


(** Sides *)
type side =
  | Lft
  | Rgh

(** Visualization options *)
type visu_option =
  (* 'Connex_component' is incompatible with 'Successors';
   * use one XOR the other *)
  | Connex_component (* only keep the connex components including
                      * the selected (by variable names) nodes *)
  | Successors (* only keep the successors of the selected nodes *)
  | Cut_leaves (* leaves which are not inductive edges are pruned *)


(** Graph node IDs *)
type nid = int (* a node name is an integer *)
type onode = nid * Offs.t (* node with an offset *)
type bnode = nid * Bounds.t (* node with a bound, i.e., a set of offsets *)

(** Arguments for inductives *)
(* Each field denotes a list of nodes *)
type ind_args =
    { ia_ptr:     nid list ;
      ia_int:     nid list }

(** Heap regions: atoms *)
(* Points-to edge *)
type pt_edge =
    { pe_size:    Offs.size ; (* size of the cell (in bytes) *)
      pe_dest:    onode     } (* dest node with offset *)
(* Inductive edge *)
type ind_edge =
    { ie_ind:     ind ;         (* inductive definition *)
      ie_args:    ind_args      (* arguments of the inductive *) }
(* Segment edge *)
type seg_edge = 
    { se_ind:     ind ;         (* inductive definition *)
      se_sargs:   ind_args ;    (* arguments at the source site *)
      se_dargs:   ind_args ;    (* arguments at the destination site *)
      se_dnode:   nid           (* destination node *) }

(** Heap regions: descriptions *)
type heap_frag =
  | Hemp
  | Hpt of pt_edge Block_frag.t
  | Hind of ind_edge
  | Hseg of seg_edge
(* Graphviz convention:
 *      Hemp                 no edge from here
 *      Hpt                  regular edges
 *      Hind                 dangling edge (no destination node)
 *      Hseg                 one segment edge
 *)
type nalloc =
  | Nheap of int option (* heap zone, Some bytes if bytes constant; else None *)
  | Nstack       (* somewhere on the stack *)
  | Nstatic      (* static area *)
  | Nnone        (* not an allocated area *)
  | Nsubmem      (* submem node; no allocation constraint for now *)
(* node specification, characterizes the value it represents, enclosing
 * - the type describing the kind of its value;
 * - the size information (number of bits) *)
type nspec = ntyp * int option
(* node_attribute are hints computed by the analyzer for itself
 *  either none (no information), or some ind_name *)
type node_attribute =
  | Attr_none          (* no attribute *)
  | Attr_ind of string (* has been an inductive of a given name *)
  (* Attribute for an SV that may denote the contents of an array:
   *  - i: stride of a block
   *  - o: list of fields offsets in a block (optional)            *)
  | Attr_array of int (* i *) * int list option (* o *)
type node =
    { n_i:     nid ;          (* index of the current node *)
      n_t:     ntyp ;         (* type of the value represented by the node *)
      n_e:     heap_frag ;    (* heap fragment attached to that node *)
      n_alloc: nalloc ;       (* allocation zone *)
      n_preds: IntSet.t ;     (* nodes pointing to that node *)
      n_attr:  node_attribute (* attribute, e.g., inductive setup *) }
type graph =
    { (* Names of the inductive definitions allowed in the graph *)
      g_inds:   StringSet.t ;
      (* Key allocator *)
      g_nkey:   Keygen.t ;
      (* Graph contents *)
      g_g:      node IntMap.t ; (* Table of nodes, edges *)
      (* Local symbolic variable environment modifications *)
      g_svemod: svenv_mod ;
      (* Roots of the shape graph *)
      g_roots:  IntSet.t ; (* set of root nodes *) }
(* Some sanity rules, regarding to sizes (assuming a 32 bits architecture):
 *  - for now, we assume pointer size to be equal to 4
 *  - address nodes should have size 4
 *  - nodes at origin of points-to edges should be of size 4
 *  - when pt edge destination offset is not null, size should be 4
 *    both for the edge and for the destination node
 *)


(** Node relations, for algorithms manipulating graphs *)

(* Injections for comparison algorithms (is_le...)
 * describes a mapping of the nodes of the right graph
 * into those of the left graph (embedding) *)
type node_emb = (int, int) Aa_maps.t
type node_embedding =
    { n_img: int IntMap.t;     (* direct image *)
      n_pre: IntSet.t IntMap.t (* pre-image, used to detect siblings *) }

(* Relations in double traversal algorithms (for weakening and join) *)
(* Version for weakening *)
type node_wkinj =
    { wi_img:  (int * int) IntMap.t; (* direct image R -> (L,O) *)
      wi_l_r:  IntSet.t IntMap.t;    (* image L -> {R} *)
      wi_lr_o: int PairMap.t;        (* image (L,R) -> O *) }
(* Version for join *)
type node_relation =
    { n_inj: int PairMap.t ;
      n_pi:  (int * int) IntMap.t ;
      n_l2r: IntSet.t IntMap.t ; (* key to sets in other side l->r *)
      n_r2l: IntSet.t IntMap.t ; (* key to sets in other side r->l *) }


(** Algorithms that manipulate graphs *)

(* Outcome of a guard in the graph level *)
type guard_res =
  | Gr_bot                   (* the condition evaluates to _|_ *)
  | Gr_no_info               (* the condition generates no information at all *)
  | Gr_equality of nid * nid (* renaming to do in the graph and numeric *)
  | Gr_emp_seg of nid        (* the segment at that node is actually empty *)
  | Gr_emp_ind of nid        (* the inductive at that node is actually empty *)

(* Outcome of a partial inclusion checking *)
type is_le_res =
  (* the algorithm failed to establish inclusion *)
  | Ilr_not_le
  (* the algorithm succeeds while consuming a sub-graph in the left;
   * it returns various elements used for the join or directed weakening *)
  | Ilr_le_rem of graph     (* the remainder in the left hand side *)
        * IntSet.t          (* nodes removed in the left hand side *)
        * int IntMap.t      (* mapping inferred by the inclusion *)
        * n_expr IntMap.t   (* instantiable constraints *)
  (* remainder in the left reduced to empty
   * corresponds to the syntehsis of an inductive edge
   * (used for weak abstraction) *)
  | Ilr_le_ind of graph
  (* remainder in the left graph is a single inductive edge
   * corresponds to the synthesis of a segment edge
   * (used for weak abstraction) *)
  | Ilr_le_seg of graph * int * ind_edge * int IntMap.t

(* Result of unfold/materialization *)
type unfold_res =
    { ur_g:    graph;
      ur_cons: n_cons list;
      ur_eqs:  PairSet.t; (* equalities, i.e., nodes that can be merged *)
      ur_news: IntSet.t }


(** Exception used to communicate results *)
(* Unfolding direction *)
type unfold_dir =
  | Udir_fwd
  | Udir_bwd
(* Localization of the point to unfold
 *   => we may have to generalize this type *)
type unfold_loc =
  | Uloc_main of nid      (* node *)
  | Uloc_sub of int * nid (* sub-memory contents value and node *)
(* Failure to discover an edge, and request to perform unfolding *)
exception Unfold_request of unfold_loc * unfold_dir
(* Failure to discover an edge, and nothing to be done *)
exception No_edge of string (* message *)

(** Hints for abstract domain operators *)
(* Unary, at Graph level, for local weak abstraction *)
type hint_ug =
    { hug_live: int Aa_sets.t (* set of live nodes *) }
(* Binary, at Graph level, for join and widening:
 * pairs of live nodes can be treated prioritarily for points-to edges
 * addition *)
type hint_bg =
    { hbg_live: (int, int) Aa_maps.t (* set of pairs of live nodes *) }

(* Binary, at Graph level, for join and widening:
 * pairs of dead access can be treated low_priority for points-to edges
 * addition *)
type lint_bg =
    { lbg_dead: (onode, onode) Aa_maps.t }

(** Collapsing and instantiation:
 *  - "collapsings" over blocks of points-to edges
 *  - for nodes synthesized as inductive parameters *)
(* Node collapsing: merging of several contiguous sequences of bits into one *)
type n_collapsing =
    { col_base:   nid; (* node ID for the base address *)
      col_stride: int; (* stride found for the block *)
      col_block:  (Bounds.t * onode * Offs.size) list; (* block structure *)
      col_extptr: OffSet.t (* external pointers to that node *) }
(* Instantiations:
 *  - definition of some nodes using integer expressions;
 *  - ins_fold: set of collapsings (for sub-memories)
 *  - ins_new_off:
 *     function to decide admissible sub-memory offsets,
 *     i.e., sub-memory environment offsets to preserve *)
type n_instantiation =
    { ins_expr:    n_expr IntMap.t; (* nid -> expr *)
      ins_fold:    n_collapsing IntMap.t; (* added IDs -> collapse *)
      (* when a pair of offsets cannot be unified, we may create a special
       * offset, that may be used to make a relation, e.g., with sub-memory
       * contents list of elements of the form:
       *       (old offset, new node, new offset) *)
      ins_new_off: (Offs.t * int * Offs.t) list }


(** Encoded graphs *)

(* Naming for graph_visu *)
type namer = int -> string * int (* node_id -> var_name * var_uid *)
(* Atoms of paths of encoded graph (used as labels) *)
type step =
  (* offset followed exactly once *)
  | Offset of Offs.t
  (* segment followed 0 or more times *)
  | Segment of string * Offs.t list (* (seg_name, allowed_offsets) *)
  (* A baby segment may become a segment in the future,
   * widening of encoded graphs can give birth to baby segments *)
  | Baby_segment of Offs.t list (* allowed_offsets *)

(* A 'renamed_path' is an edge of the encoded graph.
 * It consists in a triple: (src_node, steps, dst_node).
 *
 * A src/dst_node is a PairSet.
 * Each pair in this set is made of an offset and a node_id.
 * It means the pointer at given offset in the given node was
 * followed to reach the current node.
 * I.e. a node is renamed according to all it direct predecessors
 * which are roots of the graph. *)
type renamed_path = PairSet.t * step list * PairSet.t
(* Encoded grahs *)
type abs_graph =
    renamed_path list (* edges *)
  * PairSetSet.t      (* nodes *)
  * int               (* disj. number *)

(** Groups of abs graphs elected to be merged together *)
(* Each group has a representation graph and elements list inside *)
type 'a group = abs_graph * ((abs_graph * 'a) list)
(* Groups *)
type 'a groups = ('a group) list
(* List of encoded graphs *)
type 'a graph_list = (abs_graph * 'a) list

(* Path with a node id [XR? what are the meanings of these fields] *)
type path_arg =
    { sc:     onode;     (* source node *)
      dt:     onode;     (* dest node   *)
      pth:    step list; (* path        *) }
(* Encoded graph, as a list of nodes
 * [XR? would it not be more efficient as a map] *)
type abs_graph_arg = path_arg list
(* Graph together with encoded graph *)
type join_arg =
    { (* the encoding of the input graph *)
      abs_gi:   abs_graph_arg option;
      (* the join result of the encodings of two input graphs *)
      abs_go:   abs_graph_arg option; }

