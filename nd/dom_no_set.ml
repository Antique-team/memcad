(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_no_set.ml
 **       Lift functor from value domain to domain for value + sets
 **       => this module adds no set information, does almost nothing
 ** Xavier Rival, 2014/08/12 *)
open Data_structures
open Dom_sig
open Graph_sig
open Lib
open Nd_sig
open Offs
open Svenv_sig
open Set_sig


(** Error handling *)
module Log =
  Logger.Make(struct let section = "d_nset__" and level = Log_level.DEBUG end)


module DBuild = functor
  ( M: DOM_VALUE ) ->
  (struct
    (** Type of abstract values *)
    type t = M.t

    (** Domain initialization *)
    (* Domain initialization to a set of inductive definitions *)
    let init_inductives: Keygen.t -> StringSet.t -> Keygen.t = M.init_inductives

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t = M.bot
    let is_bot: t -> bool = M.is_bot
    (* Top element *)
    let top: t = M.top
    (* Pretty-printing *)
    let t_2stri: string IntMap.t -> string -> t -> string = M.t_2stri

    (** Management of symbolic variables *)
    (* For sanity check *)
    let check_nodes: IntSet.t -> t -> bool = M.check_nodes
    (* symbolic variables *)
    let sv_add ?(mark: bool = true) (i: int) (t: t): t =
      if mark then M.add_node i t
      else t
    let sv_rem: int -> t -> t = M.rem_node
    (* set variables *)
    let setv_add_fresh ?(root: bool = false) 
        ?(kind: set_par_type option = None) 
        ?(name: string option = None) (_: t): int * t =
      Log.fatal_exn "setv_add_fresh (no set support)"
    let setv_add ?(root: bool = true) 
        ?(kind: set_par_type option = None)
        ?(name: string option = None) (_: int) (_: t): t = 
      Log.fatal_exn "setv_add (no set support)"
    let setv_rem (_: int) (_: t): t =
      Log.fatal_exn "setv_rem (no set support)"
    let setv_col_root (_: t): IntSet.t =
      IntSet.empty
    let setv_is_root _ =
      Log.fatal_exn "is_sev_root (no set support)"
    (* The signatures of the functions below is likely to change with sets *)
    (* Renaming (e.g., post join) *)
    let symvars_srename
        ?(mark: bool = true)
        (o: (Offs.t * int) OffMap.t)
        (nm: (int * Offs.t) node_mapping)
        (setv_map: setv_mapping option)
        (t: t): t = 
      if mark then M.symvars_srename o nm t
      else t
    (* Synchronization of the SV environment *)
    let sve_sync_top_down: svenv_mod -> t -> t = M.sve_sync_top_down
    (* Check the symbolic vars correspond exactly to given set *)
    let symvars_check: IntSet.t -> t -> bool = M.symvars_check
    (* Removes all symbolic vars that are not in a given set *)
    let symvars_filter (s: IntSet.t) ?(set_vars: IntSet.t = IntSet.empty)
        (t: t): t = M.symvars_filter s t
    (* Merging into a new variable, arguments:
     *  . the stride of the structure being treated
     *  . node serving as a base address of a block;
     *  . node serving as a new block abstraction (as a sequence of bits)
     *  . old contents of the block, that is getting merged
     *  . offsets of external pointers into the block to build an
     *    environment *)
    let symvars_merge: int -> int -> int -> (Bounds.t * onode * Offs.size) list
      -> OffSet.t -> t -> t = M.symvars_merge

    (** Comparison and join operators *)
    (* Comparison *)
    let is_le: t -> t -> (int -> int-> bool) -> bool = M.is_le
    (* Upper bound: serves as join and widening *)
    let upper_bnd: join_kind -> t -> t -> t = M.upper_bnd

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat: t -> n_cons -> bool = M.sat

    (** Set satisfiability *)
    let set_sat (_: set_cons) (_: t): bool =
      Log.fatal_exn "set_sat (no set support)"

    (** Condition test *)
    let guard: bool -> n_cons -> t -> t = M.guard

    (** Set condition test *)
    let set_guard (_: set_cons) (_: t): t =
      Log.fatal_exn "set_guard (no set support)"

    (** Assignment *)
    let assign: int -> n_expr -> t -> t = M.assign
    (* Assignment inside a sub-memory *)
    let write_sub: sub_dest -> int -> n_rval -> t -> t = M.write_sub

    (** Utilities for the abstract domain *)
    let simplify_n_expr: t -> n_expr -> n_expr = M.simplify_n_expr

    (** Array domain specifc functions  *)
    (* Add an array content node  *)
    let sv_array_add: int -> int -> int list -> t -> t = M.add_array_node
    (* Add an array address node  *)
    let sv_array_address_add: int -> t -> t = M.add_array_address
    (* Checks wheter this node is the address of an array node *)
    let is_array_address: int -> t -> bool = M.is_array_address
    (* Dereference an array cell in experision,
     * this function may cause disjunction *)
    let sv_array_deref: int -> Offs.t -> t -> (t * int) list =
      M.array_node_deref
    (* Dereference an array cell in l-value,
     * no disjunction is created since it merges groups *)
    let sv_array_materialize: int -> Offs.t -> t -> t * int =
      M.array_materialize

    (** Sub-memory specific functions *)
    (* Checks whether a node is of sub-memory type *)
    let is_submem_address: int -> t -> bool = M.is_submem_address
    let is_submem_content: int -> t -> bool = M.is_submem_content
    (* Read of a value inside a submemory block *)
    let submem_read: (n_cons -> bool) -> int -> Offs.t -> int -> t -> onode =
      M.submem_read
    let submem_deref: (n_cons -> bool) -> int -> Offs.t -> int -> t -> onode =
      M.submem_deref
    (* Localization of a node in a sub-memory *)
    let submem_localize: int -> t -> sub_localize = M.submem_localize
    (* Binding of an offset in a sub-memory *)
    let submem_bind: int -> int -> Offs.t -> t -> t * onode = M.submem_bind
    (* Unfolding *)
    let unfold: int -> nid -> unfold_dir -> t -> (int IntMap.t * t) list =
      M.unfold
    (* Check predicates on array *)
    let assume (op: Opd0.assume_operand): t -> t = 
      M.assume op
    let check (op: Opd0.check_operand): t -> bool =
      M.check op
  end: DOM_VALSET)
