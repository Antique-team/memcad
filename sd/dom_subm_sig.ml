(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_subm_sig.ml
 **       interface for submemory domains
 ** Xavier Rival, 2016/07/14 *)
open Data_structures
open Lib
open Offs

open Graph_sig
open Nd_sig


(** To improve:
 *  - the low-level interface sv_add_address, sv_add_contents might be replaced
 *    with something more elegant *)


(** Interface describing abstractions of one sub-memory:
 **  - it is lifted to a value domain in dom_val_subm *)
module type SUBMEM_SIG =
  sig
    include INTROSPECT
    (* Sub-memory abstraction: description of one sub-memory *)
    type t

    (** Utilities *)
    val up_n_cons: t -> n_cons -> n_cons

    (** Sanity checks *)
    (* Sanity property:
     *  - t_index should be well-formed
     *  - nodes in the sub graph should correspond to indexes *)
    val sanity_check: string -> t -> unit

    (** Valid inductive definitions *)
    val init_inductives: Keygen.t -> StringSet.t -> Keygen.t

    (** Construction of an (empty) abstract value *)
    (* Creation of an empty sub-memory (cells are not there yet
     *  args give address SV, content SV, stride, low and high bounds *)
    val empty: int -> int -> int -> Bounds.t -> Bounds.t -> t
    (* Post-build: reduces / recomputes the delta-offsets *)
    val post_build: t -> t

    (** Filling fields *)
    val update_max: Bounds.t -> int -> t -> t
    val get_addr: t -> int
    val get_cont: t -> int
    val get_omin: t -> Bounds.t
    val get_omax: t -> Bounds.t
    val get_env: t -> (Offs.t, int) Bi_fun.t
    val get_off_ds: t -> int OffMap.t

    (** Check if it may be impacted by a glo SV numeric write/removal *)
    val may_impact_sv_mod: int -> t -> bool

    (** Low-level interface
     ** may be quite specific to current abstraction of sub-memories *)
    (* Exporting of keys of local graph *)
    val get_keys: t -> IntSet.t
    (* Discarding of the add and rem fields of the local graph *)
    val discard_addrem: t -> t
    (* Synchronization of add_rem fields *)
    val sync_addrem: t -> t * IntSet.t * IntSet.t

    (** Pretty-printing *)
    val t_2stri: string -> t -> string

    (** Environment *)
    (* check if an offset is in the env, add it, find it*)
    val env_mem: Offs.t -> t -> bool
    val env_add: Offs.t -> int -> t -> t
    val env_find: Offs.t -> t -> int
    (* looks for a decomposition of an offset as off(in env)+k where
     * k is smaller than the stride (i.e., search of a block field) *)
    val env_localize: (Offs.t -> Offs.t) -> Offs.t -> t -> (int * Offs.t) option
    (* Computation of a lower bound on the size of a block in sub-memory *)
    val env_get_block_size_lower_bound: int -> t -> int

    (** Low-level interface to the sub-memory, to register SVs and cells *)
    val sv_add_address:  int -> t -> nid * t
    val sv_add_contents: int -> t -> nid * t
    val add_cell: nid -> Bounds.t -> Offs.size -> nid -> t -> t
    val register_node: int -> int -> t -> t
    val node_assume_placed: int -> t -> t

    (** Constraints satisfaction check *)
    val make_sat: (n_cons -> bool) -> t -> n_cons -> bool

    (** Reading functions *)
    val read_sub_base_off:
        (Offs.t -> Offs.t) (* simplifier *)
      -> Offs.t -> int -> t -> onode
    val read_sub_internal: nid -> Offs.t -> int -> t -> onode

    (** Localization of a node as an address *)
    val localize_offset_of_node: int -> t -> Offs.t option
    val localize_node_in_block: int -> t -> bool

    (** Delegated unfolding *)
    (* Each list entry contains:
     *  (a) unfolded graph, (b) removed nodes, (c) renaming, (d) predicates. *)
    val unfold: (n_cons -> bool)
      -> nid -> unfold_dir -> t
        -> (t * int IntMap.t * n_cons list) list

    (** Renaming using a node mapping *)
    val symvars_srename:
        (Offs.t * int) OffMap.t -> Offs.t node_mapping -> t -> t * n_cons list

    (** Upper bounds *)
    (* Implementation of upper bounds *)
    val upper_bnd: int (* negative int allocator, main mem *)
      -> node_relation (* relation accumulator, main mem *)
        -> (int * int) IntMap.t (* localization accumulator, main mem *)
          -> int * int (* base and content SVs *)
            -> (n_cons -> bool) -> t
              -> (n_cons -> bool) -> t
                -> t * node_relation * (int * int) IntMap.t * int

    (** Inclusion check *)
    val is_le: (n_cons -> bool) -> t -> t -> bool

    (** Regression testing *)
    val ind_check: (n_cons -> bool) -> Offs.t -> string -> t -> bool

    (** Write inside the sub-memory *)
    val write: (n_cons -> bool) -> int * Offs.t -> n_expr -> t -> t

    (** Guard inside the sub-memory *)
    val guard: n_cons -> t -> t
  end
