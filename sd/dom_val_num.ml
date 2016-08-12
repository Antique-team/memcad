(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_val_num.ml
 **       lifting of a numerical domain into a value domain
 ** Xavier Rival, Pascal Sotin, 2012/04/17 *)
open Data_structures
open Lib
open Offs

open Dom_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Svenv_sig

open Dom_utils

(* Possible improvements:
 *  - introduce node types and manage them at this level
 *)

(** Error report *)
module Log =
  Logger.Make(struct let section = "dv_num__" and level = Log_level.DEBUG end)

(** Lift functor *)
module Make_val_num = functor (Dn: DOM_NUM) ->
  (struct
    (** Type of abstract values *)
    type t = Dn.t

    (** Domain initialization *)
    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (g: Keygen.t) (_: StringSet.t): Keygen.t =
      g (* this domain generates no keys *)

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t = Dn.bot
    let is_bot: t -> bool = Dn.is_bot
    (* Top element *)
    let top: t = Dn.top
    (* Pretty-printing *)
    let t_2stri: sv_namer -> string -> t -> string = Dn.t_2stri
    
    (** Management of symbolic variables *)
    (* For sanity check *)
    let check_nodes (s: IntSet.t) (x: t): bool = Dn.check_nodes s x
    (* Node addition and removal *)
    let add_node (id: int) (t: t): t =
      Dn.add_node id t
    let rem_node: int -> t -> t = Dn.rem_node
    (* Renaming (e.g., post join) *)
    let symvars_srename (_: (Offs.t * int) OffMap.t)
        : 'a node_mapping -> t -> t =
      Dn.vars_srename
    (* Synchronization of the SV environment *)
    let sve_sync_top_down (svm: svenv_mod) (t: t): t =
      svenv_mod_doit (fun i _ -> add_node i) rem_node
        (fun i -> Log.fatal_exn "mod: %d" i) svm t
    (* Check the symbolic vars correspond exactly to given set *)
    let symvars_check: IntSet.t -> t -> bool = Dn.check_nodes
    (* Removes all symbolic vars that are not in a given set *)
    let symvars_filter: IntSet.t -> t -> t = Dn.nodes_filter
    (* Merging two SVs into a new SV; ignored here (returns top)
     *  Arguments:
     *  . the stride of the structure being treated
     *  . node serving as a base address of a block;
     *  . node serving as a new block abstraction (as a sequence of bits)
     *  . old contents of the block, that is getting merged
     *  . offsets of external pointers into the block to build an
     *    environment *)
    let symvars_merge (_: int) (_: int) (sv: int)
        (_: (Bounds.t * onode * Offs.size) list) (_: OffSet.t) (x: t): t =
      add_node sv x

    (** Comparison and join operators *)
    (* Comparison *)
    let is_le: t -> t -> (int -> int -> bool) -> bool = Dn.is_le
    (* Upper bound: serves as join and widening *)
    let upper_bnd: join_kind -> t -> t -> t = function
      | Jjoin -> Dn.join
      | Jwiden -> Dn.widen
      | Jdweak -> Log.fatal_exn "no directed weakening"

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (x: t) (c: n_cons): bool = Dn.sat c x

    (** Condition test *)
    let guard: bool -> n_cons -> t -> t = Dn.guard

    (** Assignment *)
    let assign: int -> n_expr -> t -> t = Dn.assign
    let write_sub _ _ _ _ = Log.fatal_exn "dom_val_num: assign"

    (** Utilities for the abstract domain *)
    let simplify_n_expr: t -> n_expr -> n_expr = Dn.simplify_n_expr

    (** Array domain specific *)
    (* Add an array content node  *)
    let add_array_node _ _ _ x = x
    (* Add an array address node  *)
    let add_array_address _ x = x
    (* Checks wheter this node is the address of an array node *)
    let is_array_address _ _ = false
    (* Dereference an array cell in experision,
     * this function may cause disjunction *)
    let array_node_deref _ _ _ = []
    (* Dereference an array cell in l-value,
     * no disjunction is created since it merges groups *)
    let array_materialize _ _ x = x, -1
    (* Summarizing dimensions related oprations
     * expand the constraints on one dimension to another  *)
    let expand = Dn.expand
    (* Upper bound of the constraits of two dimensions *)
    let compact = Dn.compact
    (* Meet: a lattice operation  *)
    let meet = Dn.meet
    (* Forget the information on a dimension *)
    let forget = Dn.forget
    (** Export of range information *)
    let bound_variable = Dn.bound_variable
    (** Sub-memory specific functions *)
    (* Checks whether a node is of sub-memory type *)
    let is_submem_address (_: int) (_: t): bool = false
    let is_submem_content (_: int) (_: t): bool = false
    (* Read of a value inside a submemory block *)
    let submem_read _ _ _ _ _: onode =
      Log.fatal_exn "submem_read (no sub-mem dom)"
    let submem_deref _ _ _ _ _: onode =
      Log.fatal_exn "submem_deref (no sub-mem dom)"
    (* Localization of a node in a sub-memory *)
    let submem_localize _ = Log.fatal_exn "submem_localize (no sub-mem dom)"
    let submem_bind _ = Log.fatal_exn "submem_bind (no sub-mem dom)"
    (* Unfolding *)
    let unfold (_: int) (_: nid) (_: unfold_dir) (_: t)
        : (int IntMap.t * t) list =
      Log.fatal_exn "unfold (no sub-mem dom)"
    let check (op: Opd0.check_operand) (x: t): bool = 
      match op with
      | Opd0.SL_array -> Log.fatal_exn "array_check (no array dom)"
      | Opd0.SL_ind (ind, i, name) ->
          (* Regression testing support, inside sub-memories *)
          false
    let assume (op: Opd0.assume_operand) (x: t): t = 
      match op with
      | Opd0.SL_array -> Log.fatal_exn "array assume (no array dom)"
  end: DOM_VALUE)


(** Timer instance of the value domain (act as a functor on top
 ** of the domain itself) *)
module Dom_val_timing = functor (Dv: DOM_VALUE) ->
  (struct
    module T = Timer.Timer_Mod( struct let name = "Val" end )
    type t = Dv.t
    let init_inductives = T.app2 "init_inductives" Dv.init_inductives
    let bot = Dv.bot
    let is_bot = T.app1 "is_bot" Dv.is_bot
    let top = Dv.top
    let t_2stri = T.app3 "t_2stri" Dv.t_2stri
    let check_nodes = T.app2 "check_nodes" Dv.check_nodes
    let add_node = T.app2 "add_node" Dv.add_node
    let rem_node = T.app2 "rem_node" Dv.rem_node
    let sve_sync_top_down = T.app2 "sve_sync_top_down" Dv.sve_sync_top_down
    let symvars_srename = T.app3 "symvars_srename" Dv.symvars_srename
    let symvars_check = T.app2 "symvars_check" Dv.symvars_check
    let symvars_filter = T.app2 "symvars_filter" Dv.symvars_filter
    let symvars_merge = T.app6 "symvars_merge" Dv.symvars_merge
    let is_le = T.app2 "is_le" Dv.is_le
    let upper_bnd = T.app3 "upper_bnd" Dv.upper_bnd
    let sat = T.app2 "sat" Dv.sat
    let guard = T.app3 "guard" Dv.guard
    let assign = T.app3 "assign" Dv.assign
    let write_sub = T.app4 "write_sub" Dv.write_sub
    let simplify_n_expr = T.app2 "simplify_n_expr" Dv.simplify_n_expr
    let is_submem_address = T.app2 "is_submem_address" Dv.is_submem_address
    let is_submem_content = T.app2 "is_submem_content" Dv.is_submem_content
    let submem_read = T.app5 "submem_read" Dv.submem_read
    let submem_deref = T.app5 "submem_deref" Dv.submem_deref
    let submem_localize = T.app2 "submem_localize" Dv.submem_localize
    let submem_bind = T.app4 "submem_bind" Dv.submem_bind
    let check = T.app2 "check" Dv.check
    let unfold = T.app4 "unfold" Dv.unfold
    let add_array_node  = T.app4 "add_array_node" Dv.add_array_node
    let add_array_address  = T.app2 "add_array_address" Dv.add_array_address
    let is_array_address  = T.app2 "is_array_address" Dv.is_array_address
    let array_node_deref  = T.app3 "array_node_deref" Dv.array_node_deref
    let array_materialize  = T.app3 "array_materialize" Dv.array_materialize
    let expand = T.app3 "expand" Dv.expand
    let compact = T.app3 "compact" Dv.compact
    let meet = T.app2 "meet" Dv.meet
    let forget = T.app2 "forget" Dv.forget
    let bound_variable = T.app2 "bound_variable" Dv.bound_variable
    let assume = T.app2 "assume" Dv.assume
  end: DOM_VALUE)
