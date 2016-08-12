(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_dump.ml
 **       Dumping the activity of the set domain
 ** Xavier Rival, 2015/05/27 *)
open Data_structures
open Offs

open Nd_sig
open Set_sig
open Svenv_sig

(** Error handling *)
module Log =
  Logger.Make(struct let section = "s_dump__" and level = Log_level.DEBUG end)

(** Logging facility *)
let opt_chan: out_channel option ref = ref None
let log_open ( ): out_channel =
  let filename = "log.log" in
  let file =
    Unix.openfile filename
      [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  let chan = Unix.out_channel_of_descr file in
  opt_chan := Some chan;
  chan
let log_str (str: string): unit =
  let chan =
    match !opt_chan with
    | None -> log_open ( )
    | Some chan -> chan in
  Printf.fprintf chan "%s" str


(** Abstract domain functor *)

(* This functor attempts to dump a log of the operations performed
 * in the set domain:
 *  - it gives an ID to each set abstract value generated
 *  - it produces an ML program doing the same operations
 *    assuming set abstract values are represented in a module D
 *)

module Make = functor (D: DOMSET) ->
  (struct
    (** Type of abstract values *)
    type t =
        { t_idx:  int; (* the index of the abstract value *)
          t_u:    D.t; (* the real abstract value *) }

    (** Indexing *)
    (* Default: x(0) is bot; x(1) is top *)
    let indexer: Keygen.t ref = ref Keygen.empty
    let make str u =
      let kg, idx = Keygen.gen_key !indexer in
      log_str (Printf.sprintf "let x%d = %s\n" idx str);
      indexer := kg;
      { t_idx = idx;
        t_u   = u }

    (** Basic lattice functions *)
    (* Bottom element (empty context) *)
    let bot: t = make "D.bot" D.bot
    let is_bot (x: t): bool =
      D.is_bot x.t_u
    (* Top element (empty context) *)
    let top: t = make "D.top" D.top
    (* Pretty-printing, with indentation *)
    let t_2stri (sn: string IntMap.t) (ind: string) (x: t): string =
      D.t_2stri sn ind x.t_u

    (** Management of symbolic variables *)
    (* For sanity check *)

    let check_nodes (s: IntSet.t) (x: t): bool = (* not indexed *)
      D.check_nodes s x.t_u

    (* Symbolic variables *)
    let sv_add (i: int) (x: t): int * t =
      let j, u1 = D.sv_add i x.t_u in
      let str = Printf.sprintf "D.sv_add %d x%d" i x.t_idx in
      j, make str u1
    let sv_rem (i: int) (x: t): t =
      let str = Printf.sprintf "D.sv_rem %d x%d" i x.t_idx in
      make str (D.sv_rem i x.t_u)

    (* check if a set var root *)
    let setv_is_root (i: int) (x: t): bool = (* not indexed *)
      D.setv_is_root i x.t_u
    (* collect root set variables *)
    let setv_col_root (x: t): IntSet.t = (* not indexed *)
      D.setv_col_root x.t_u

    (* Set variables *)
    let setv_add ?(root: bool = false) ?(kind: set_par_type option = None)
      ?(name: string option = None) (setv: int) (x: t): t =
      let str = Printf.sprintf "D.setv_add %d x%d" setv x.t_idx in
      make str (D.setv_add ~root:root ~kind:kind ~name:name setv x.t_u)
    let setv_rem (i: int) (x: t): t =
      let str = Printf.sprintf "D.setv_rem %d x%d" i x.t_idx in
      make str (D.setv_rem i x.t_u)

    (** Comparison and join operators *)
    (* Comparison *)
    let is_le (x0: t) (x1: t): bool =
      let b = D.is_le x0.t_u x1.t_u in
      log_str (Printf.sprintf
                 "let _ = assert (D.is_le x%d x%d || not %b)\n"
                 x0.t_idx x1.t_idx b);
      b
    (* Weak bound: serves as widening *)
    let weak_bnd (x0: t) (x1: t): t =
      let str = Printf.sprintf "D.weak_bnd x%d x%d" x0.t_idx x1.t_idx in
      make str (D.weak_bnd x0.t_u x1.t_u)
    (* Upper bound: serves as join and widening *)
    let upper_bnd (x0: t) (x1: t): t =
      let str = Printf.sprintf "D.upper_bnd x%d x%d" x0.t_idx x1.t_idx in
      make str (D.upper_bnd x0.t_u x1.t_u)

    (** Set satisfiability *)
    let set_sat (c: set_cons) (x: t): bool =
      let b = D.set_sat c x.t_u in
      log_str (Printf.sprintf
                 "let _ = assert (D.set_sat ? x%d || not %b)\n"
                 x.t_idx b);
      b

    (** Set condition test *)
    let set_guard (sc: set_cons) (x: t): t =
      let str = Printf.sprintf "D.set_guard ? x%d" x.t_idx in
      make str (D.set_guard sc x.t_u)

    (** Forget (if the meaning of the sv changes) *)
    let forget (i: int) (x: t): t =
      let str = Printf.sprintf "D.forget %d x%d" i x.t_idx in
      make str (D.forget i x.t_u)

    (** Renaming (e.g., post join) *)
    let symvars_srename
        (nm: (Offs.t * int) OffMap.t)
        (svm: (int * Offs.t) node_mapping)
        (setvm: setv_mapping option) (x: t): t =
      let str = Printf.sprintf "D.symvars_srename ? ? ? x%d" x.t_idx in
      make str (D.symvars_srename nm svm setvm x.t_u)

    (* Synchronization of the SV environment*)
    let sve_sync_top_down (svm: svenv_mod) (x: t): t =
      let str = Printf.sprintf "D.sve_sync_top_down ? x%d" x.t_idx in
      make str (D.sve_sync_top_down svm x.t_u)

    (* Removes all symbolic vars that are not in a given set *)
    (* may change a little bit *)
    let symvars_filter (skeep: IntSet.t) (setvkeep: IntSet.t) (x: t): t =
      let str = Printf.sprintf "D.symvars_filter ? ? x%d" x.t_idx in
      make str (D.symvars_filter skeep setvkeep x.t_u)
  end: DOMSET)
