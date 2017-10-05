(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_quicr.ml
 **       Functor to integrate QUICr into MemCAD
 ** Huisong Li and Xavier Rival, 2015/05/28 *)
open Data_structures
open Lib
open Offs

open Dom_sig
open Nd_sig
open Set_sig
open Svenv_sig

open Set_utils

module Log =
  Logger.Make(struct let section = "s_quicr_" and level = Log_level.DEBUG end)

(** QUICr internal names *)
module L = SETr.SymSing.Logic
module R = SETr.Rename


(** Converting SVs and SETVs into a single type, using offsets *)
(* QUICr assumes a unique pool of symbolic variables, whereas MemCAD
 * has two distinct pools for SVs and SETVs; thus, the code below
 * maps SVs and SETVs to a single int type, using an offset
 * (if too many SVs or SETVs are generated, it will crash) *)
type sym = int
type setv = int
type v =
  | V_sv of sv
  | V_setv of setv
let max_sv   = 1000000
let max_setv = 1000000
let sv_2sym (i: sv): sym = assert (0 <= i && i < max_sv); i
let setv_2sym (i: setv): sym = assert (0 <= i && i < max_setv); i + max_sv
let sym_2v (i: sym): v =
  assert (0 <= i);
  if i < max_sv then V_sv i
  else V_setv (i - max_sv)
let pp_sym (form: Format.formatter) (i: sym): unit =
  match sym_2v i with
  | V_sv i   -> Format.fprintf form "N[%d]" i
  | V_setv i -> Format.fprintf form "S[%d]" i

(** Translation functions *)
let rec tr_set_expr: set_expr -> int L.e = function
  | S_empty -> L.Empty
  | S_var i -> L.Var (setv_2sym i)
  | S_node i -> L.Sing (sv_2sym i)
  | S_uplus (e0, e1) -> L.DisjUnion (tr_set_expr e0, tr_set_expr e1)
  | S_union (e0, e1) -> L.Union (tr_set_expr e0, tr_set_expr e1)
let tr_set_cons: set_cons -> int L.t = function
  | S_eq (e0, e1) -> L.Eq (tr_set_expr e0, tr_set_expr e1)
  | S_subset (e0, e1) -> L.SubEq (tr_set_expr e0, tr_set_expr e1)
  | S_mem (i, e) -> L.In (sv_2sym i, tr_set_expr e)

(** The type of QUICr module used in MemCAD *)
module type SDomain =
  sig
    include (SETr.Domain
            with type ctx = unit
            and  type sym = int
            and  type cnstr = int L.t)
  end

(** Abstract domain functor *)
module Make = functor (D: SDomain) ->
  (struct
    (** Type of abstract values *)
    let module_name = "set_quicr"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n"
        module_name "sdomain"

    type t =
        { t_u: D.t;          (* a QUICr value *)
          t_roots: IntSet.t; (* set of root set variables *) }
    let lift f x = { x with t_u = f x.t_u }

    (** Basic lattice functions *)

    (* Bottom element (empty context) *)
    let bot: t = { t_u = D.bottom ( ); t_roots = IntSet.empty }
    let is_bot (x: t): bool = D.is_bottom () x.t_u
    (* Top element (empty context) *)
    let top: t = { t_u = D.top ( ); t_roots = IntSet.empty }
    (* Pretty-printing, with indentation *)
    let t_2stri (_: string IntMap.t) (ind: string) (x: t): string =
      let buf = Buffer.create 1 in
      let form = Format.formatter_of_buffer buf in
      Format.fprintf form "%s@[%a@]@?" ind (D.pp_print () pp_sym) x.t_u;
      Buffer.contents buf

    (** Management of symbolic variables *)
    (* Internal forget function *)
    let forget_syms (l: sym list) (x: t): t =
      lift (D.forget () l) x

    (* For sanity check *)
    let check_nodes (s: IntSet.t) (x: t): bool =
      failwith "check_nodes"

    (* Symbolic variables *)
    let sv_add (sv: int) (x: t): int * t = sv, x
    let sv_rem (i: int) (x: t): t = forget_syms [ sv_2sym i ] x

    (* check if a set var root *)
    let setv_is_root (setv: sv) (t: t): bool =
      IntSet.mem setv t.t_roots
    (* collect root set variables *)
    let setv_col_root (x: t): IntSet.t = x.t_roots

    (* Set variables *)
    let setv_add ?(root: bool = false) ?(kind: set_par_type option = None)
      ?(name: string option = None) (setv: int) (x: t): t =
      { x with
        t_roots = if root then IntSet.add setv x.t_roots else x.t_roots }
    let setv_rem (i: int) (x: t): t =
      forget_syms [ setv_2sym i ] x

    (** Forget (if the meaning of the sv changes) *)
    let sv_forget (i: int) (x: t): t =
      forget_syms [ sv_2sym i ] x

    (** Comparison and join operators *)

    (* Comparison *)
    let is_le (x0: t) (x1: t): bool =
      D.le () x0.t_u x1.t_u

    (* Weak bound: serves as widening *)
    let weak_bnd (x0: t) (x1: t): t =
      { x0 with t_u = D.widening () x0.t_u x1.t_u }

    (* Upper bound: serves as join and widening *)
    let upper_bnd (x0: t) (x1: t): t =
      { x0 with t_u = D.join () x0.t_u x1.t_u }

    (** Set satisfiability *)
    let set_sat (sc: set_cons) (x: t): bool =
      D.sat () x.t_u (tr_set_cons sc)

    (** Set condition test *)
    let set_guard (sc: set_cons) (x: t): t =
      lift (D.constrain () (tr_set_cons sc)) x

    (** Renaming (e.g., post join) *)
    let symvars_srename
        (nm: (Offs.t * int) OffMap.t)
        (svm: (int * Offs.t) node_mapping)
        (setvm: setv_mapping option) (x: t): t =
      (* 1. remove SVs values that were removed *)
      let x = forget_syms (IntSet.fold (fun i a -> i :: a) svm.nm_rem [ ]) x in
      (* 2. build renamer structure *)
      let aux f m l = IntMap.fold (fun i (j, _) l -> (f i, f j) :: l) m l in
      let l = aux sv_2sym svm.nm_map [ ] in
      let l =
        match setvm with
        | None -> l
        | Some m -> aux setv_2sym m.sm_map l in
      let r = R.of_assoc_list l in
      (* 3. do the rename *)
      let x = { x with t_u = D.rename_symbols () r x.t_u } in
      (* Note: we do not duplicate symbols ! *)
      x

    (* Synchronization of the SV environment*)
    let sve_sync_top_down (svm: svenv_mod) (x: t): t =
      let l =
        PSet.fold (fun i a -> sv_2sym i :: a) svm.svm_rem
          (PSet.fold (fun i a -> sv_2sym i :: a) svm.svm_mod [ ]) in
      forget_syms l x

    (* Removes all symbolic vars that are not in a given set *)
    (* may change a little bit *)
    let symvars_filter (skeep: IntSet.t) (setvkeep: IntSet.t) (x: t): t =
      Log.info "filtering";
      let syms = D.symbols () x.t_u in
      let f_sym sym =
        match sym_2v sym with
        | V_sv i   -> not (IntSet.mem i skeep)
        | V_setv i ->
            not (IntSet.mem i setvkeep) && not (IntSet.mem i x.t_roots) in
      let remove = List.filter f_sym syms in
      forget_syms remove x

  end: DOMSET)
