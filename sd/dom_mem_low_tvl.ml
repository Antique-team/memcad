(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_mem_low_tvl.ml
 **       a memory domain based on Three Valued Logic
 ** Xavier Rival and Sixiao Zhu, started 2017/04/27 *)
open Data_structures
open Flags
open Lib

open Dom_sig
open Graph_sig
open Nd_sig
open Sv_sig
open Svenv_sig

open Dom_utils

(* Notes:
 *  - consider preparing useful data structures in other module *)


(** Error report *)
module Log =
  Logger.Make(struct let section = "dm_tvl_" and level = Log_level.DEBUG end)

(** Main module *)
module DBuild = functor (Dv: DOM_VALSET) ->
  (struct
    (** Module name *)
    let module_name = "[tvl]"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name Dv.module_name (Dv.config_2str ())

    (** Type of abstract values *)
    type t = unit (* TODO: fix this type *)

    (** Domain initialization to a set of inductive definitions *)

    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (_: Keygen.t) (_: StringSet.t): _ =
      Log.todo_exn "init_inductives: useless for now"
    let inductive_is_allowed (_: string): bool =
      Log.todo_exn "inductive_is_allowed"

    (** Fixing sets of keys *)
    let sve_sync_bot_up (x: t): t * svenv_mod =
      Log.todo "sve_sync_bot_up";
      x, svenv_empty

    (* Sanity check *)
    let sanity_sv (_: IntSet.t) (x: t): bool =
      Log.todo "sanity_sv: unimp";
      true

    (** Lattice elements *)

    (* Bottom element *)
    let bot: t = ( )
    let is_bot (x: t): bool =
      Log.todo "is_bot: unimp";
      false

    (* Top element, with empty set of roots *)
    let top (): t =
      Log.todo "top: unimp";
      ( )

    (* Pretty-printing *)
    let t_2stri (ind: string) (x: t): string =
      Log.todo_exn "todo: t_2stri"
    let t_2str: t -> string = t_2stri ""

    (* External output *)
    let ext_output (_: output_format) (_: string) (_: namer) (_: t): unit =
      Log.todo_exn "todo: ext_output"


    (** Management of symbolic variables *)

    (* Will that symb. var. creation be allowed by the domain? *)
    let sv_is_allowed ?(attr: node_attribute = Attr_none) (nt: ntyp)
        (na: nalloc) (x: t): bool =
      Log.todo_exn "todo: sv_is_allowed"

    (* Add a symbolic variable, with a newly generated id
     *  (by default, not considered root by the underlying domain) *)
    let sv_add_fresh
        ?(attr: node_attribute = Attr_none) ?(root: bool = false)
        (t: ntyp) (na: nalloc) (x: t): int * t =
      Log.todo_exn "sv_add_fresh"

    (* Recover information about a symbolic variable *)
    (* For now, only nalloc and ntyp *)
    let sv_get_info (i: int) (x: t): nalloc option * ntyp option =
      Log.todo_exn "sv_get_info"

    (* Garbage collection *)
    let gc (roots: int uni_table) (x: t): t =
      x (* nothing to do for GC in this module (!!! for now !!!) *)

    (* graph encode *)
    let encode (disj: int) (n: namer) (x: t)
        : renamed_path list * PairSetSet.t * int =
      (* no need for encode in this module *)
      Log.todo_exn "encode"


    (** Comparison and Join operators *)

    (* Checks if the left argument is included in the right one *)
    let is_le (roots_rel: int bin_table) (_: int bin_table)
        (xl: t) (xr: t): svenv_upd option =
      Log.todo "is_le";
      None

    (* Generic comparison (does both join and widening) *)
    let join (j: join_kind) (hso: int hint_bs option)
        (lso: (onode lint_bs) option)
        (roots_rel: int tri_table) (setroots_rel: int tri_table)
        ((xl, jl): t * join_ele) ((xr, jr): t * join_ele)
        : t * svenv_upd * svenv_upd =
      Log.todo_exn "join"

    (* Directed weakening; over-approximates only the right element *)
    let directed_weakening _ = Log.todo_exn "dw"

    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    let local_abstract (ho: int hint_us option) (x: t): t =
      Log.todo_exn "local_abstract"


    (** Cell operations *)

    (* Creation *)
    let cell_create ?(attr:node_attribute = Attr_none) 
        ((si, so): onode) (sz: Offs.size) (nt: ntyp) (x: t): t = 
      Log.todo_exn "cell_create"

    (* Deletion *)
    let cell_delete ?(free:bool = true) ?(root:bool = false)
        (i: int) (x: t): t =
      Log.todo_exn "cell_delete"

    (* Read the content of a cell *)
    let cell_read
        (is_resolve: bool) (* whether call from cell-resolve  *)
        (src: onode)       (* address of the cell to read *)
        (sz: int)          (* size of the cell to read *)
        (x: t)             (* abstract memory input *)
        : (t * onode * onode option) list =
      Log.todo_exn "cell_read"

    (* Resolve a cell, i.e., materialization *)
    let cell_resolve
        (src: onode) (* address of the cell to resolve *)
        (size: int)  (* size *)
        (x: t)       (* abstract memory input *)
        : (t * onode * bool) list =
      Log.todo_exn "cell_resolve"

    (* Write a cell *)
    let cell_write
        (ntyp: ntyp) (* type of the value being assigned *)
        (dst: onode) (* address of the cell to over-write *)
        (size: int)  (* size of the chunk to write into the memory *)
        (ne: n_expr) (* right hand side as an expression over SVs *)
        (x: t)       (* input abstract memory state *)
        : t (* output abstract memory *) =
      Log.todo_exn "cell_write"


    (** Transfer functions for the analysis *)

    (* Condition test *)
    let guard (c: n_cons) (x: t): t =
      Log.todo_exn "guard"

    (* Checking that a constraint is satisfied *)
    let sat (c: n_cons) (x: t): bool =
      Log.todo_exn "sat"


    (** Set domain *)

    (* Adding / removing set variables *)
    let setv_add_fresh (_: bool) (_: string) (_: t): int * t =
      Log.todo_exn "setv_add_fresh"
    let setv_delete (_: int) (_: t): t =
      Log.todo_exn "setv_delete"

    (* Assume construction *)
    let assume (op: meml_log_form) (t: t): t =
      Log.todo_exn "assume"

    (* Check construction, that an inductive be there *)
    let check (op: meml_log_form) (t: t): bool =
      Log.todo_exn "check"

    (** Unfolding, assuming and checking inductive edges *)

    (* Unfold *)
    let ind_unfold (u: unfold_dir) (lv: onode) (t: t): t list =
      Log.todo_exn "ind_unfold (no support for inductives)"
  end: DOM_MEM_LOW)
