(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_sig.ml
 **       set domain interface
 ** Xavier Rival, 2017/02/28 *)
open Data_structures
open Lib

open Nd_sig
open Set_sig
open Svenv_sig

open Set_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "setr___" and level = Log_level.DEBUG end)
let debug_module = false

(** SETr shortcuts *)
module S = SETr
module L = S.SymSing.Logic

(** Helper functions *)
(* Key conversions *)
let setv_to_i (setv: int): int =
  if setv < 0 then Log.fatal_exn "negative SETV";
  - 1 - setv
let sv_to_i (sv: int): int =
  if sv < 0 then Log.fatal_exn "negative SV";
  sv
let i_to_setv (i: int) = - 1 - i
let i_to_sv (i: int) = i
let i_is_sv (i: int): bool = i >= 0
(* Translations of expressions and constraints *)
let rec set_expr_2e: set_expr -> int L.e = function
  | S_empty -> L.Empty
  | S_var setv -> L.Var (setv_to_i setv)
  | S_node sv -> L.Var (sv_to_i sv)
  | S_uplus (se0, se1) -> L.DisjUnion (set_expr_2e se0, set_expr_2e se1)
  | S_union (se0, se1) -> L.Union (set_expr_2e se0, set_expr_2e se1)
let set_cons_2t: set_cons -> int L.t = function
  | S_eq (se0, se1) -> L.Eq (set_expr_2e se0, set_expr_2e se1)
  | S_mem (sv, se1) -> L.In (sv_to_i sv, set_expr_2e se1)
  | S_subset (se0, se1) -> L.SubEq (set_expr_2e se0, set_expr_2e se1)
(* Pretty-printing *)
let rec le_2str (e: int L.e): string =
  match e with
  | L.Empty -> "empty"
  | L.Universe -> "all"
  | L.DisjUnion (e0, e1) ->
      Printf.sprintf "(%s + %s)" (le_2str e0) (le_2str e1)
  | L.Union (e0, e1) ->
      Printf.sprintf "(%s U %s)" (le_2str e0) (le_2str e1)
  | L.Inter (e0, e1) ->
      Printf.sprintf "(%s /\\ %s)" (le_2str e0) (le_2str e1)
  | L.Diff (e0, e1) ->
      Printf.sprintf "(%s \\ %s)" (le_2str e0) (le_2str e1)
  | L.Comp e0 ->
      Printf.sprintf "(all \\ %s)" (le_2str e0)
  | L.Var i ->
      if i < 0 then Printf.sprintf "S[%d]" (i_to_setv i)
      else Printf.sprintf "N[%d]" (i_to_sv i)
  | L.Sing i ->
      if i < 0 then Log.fatal_exn "negative SV"
      else Printf.sprintf "{ N[%d] }" (i_to_sv i)
let lt_2stri (ind: string) (c: int L.t): string =
  let rec aux_1 = function
    | L.True  -> "true"
    | L.False -> "false"
    | L.Eq (e0, e1) ->
        Printf.sprintf "%s = %s" (le_2str e0) (le_2str e1)
    | L.SubEq (e0, e1) ->
        Printf.sprintf "%s <= %s" (le_2str e0) (le_2str e1)
    | L.In (i, e1) ->
        Printf.sprintf "S[%d] <- %s" (i_to_sv i) (le_2str e1)
    | c -> aux_0 c
  and aux_0 c =
    match c with
    | L.And (c0, c1) ->
        Printf.sprintf "%s   %s\n%s/\\ %s" ind (aux_1 c0) ind (aux_1 c1)
    | L.Not c0 ->
        Printf.sprintf "%s NEG (%s)" ind (aux_1 c0)
    | L.True | L.False | L.Eq (_,_) | L.SubEq (_,_) | L.In (_,_) ->
        Printf.sprintf "%s   %s" ind (aux_1 c) in
  aux_0 c

module type PRE_DOMSET =
  sig
    val name: string
    module D:
        (S.Domain with
         type sym = int
         and type cnstr  = int L.t
         and type output = int L.t )
    val ctx: D.ctx
  end

module Make = functor (P: PRE_DOMSET) ->
  (struct
    (** Module configuration *)
    let module_name = Printf.sprintf "setr[%s]" P.name
    let config_2str (): string = module_name
    (** Quick access to SETr *)
    module D = P.D
    let ctx = P.ctx
    (** Type of abstract values *)
    type t = { t_u:     D.t;     (* Underlying SETr abstract value *)
               t_roots: IntSet.t (* Set of roots *) }
    (* Bottom element (empty context) *)
    let bot: t = { t_u     = D.bottom ctx;
                   t_roots = IntSet.empty; }
    let is_bot (x: t): bool = D.is_bottom ctx x.t_u
    (* Top element (empty context) *)
    let top: t = { t_u     = D.top ctx;
                   t_roots = IntSet.empty }
    (* Pretty-printing, with indentation *)
    let t_2stri (_: string IntMap.t) (ind: string) (x: t): string =
      let out = D.serialize ctx x.t_u in
      lt_2stri ind out
    (** Management of symbolic variables *)
    (* Some internal functions *)
    let drop_svs (l: int list) (x: t): t =
      { x with t_u = D.forget ctx (List.map sv_to_i l) x.t_u }
    let drop_setvs (l: int list) (x: t): t =
      { x with t_u = D.forget ctx (List.map setv_to_i l) x.t_u }
    (* For sanity check *)
    let check_nodes (_: IntSet.t) (_: t): bool =
      Log.todo_exn "todo: check_nodes"
    (* Symbolic variables *)
    let sv_add (sv: int) (x: t): int * t =
      sv, x
    let sv_rem (sv: int) (x: t): t =
      drop_svs [ sv ] x
    (* check if a set var root *)
    let setv_is_root (setv: int) (t: t): bool =
      IntSet.mem setv t.t_roots
    (* collect root set variables *)
    let setv_col_root (t: t): IntSet.t = t.t_roots
    (* Set variables *)
    let setv_add ?(root: bool = false) ?(kind: set_par_type option = None)
        ?(name: string option = None) (setv: int) (x: t): t =
      { x with
        t_roots = if root then IntSet.add setv x.t_roots else x.t_roots }
    let setv_rem (setv: int) (x: t): t =
      let x = drop_setvs [ setv ] x in
      { x with t_roots = IntSet.remove setv x.t_roots }
    (** Comparison and join operators *)
    (* Comparison *)
    let is_le (x0: t) (x1: t): bool = D.le ctx x0.t_u x1.t_u
    (* Weak bound: serves as widening *)
    let weak_bnd (x0: t) (x1: t): t =
      { x0 with t_u = D.widening ctx x0.t_u x1.t_u }
    (* Upper bound: serves as join and widening *)
    let upper_bnd (x0: t) (x1: t): t =
      (* TODO: distinguish widen and join, SETr may do more precise join *)
      { x0 with t_u = D.widening ctx x0.t_u x1.t_u }
    (** Set satisfiability *)
    let set_sat (c: set_cons) (x: t): bool =
      Log.debug "set_sat %s\n%s" (set_cons_2str c)
        (t_2stri IntMap.empty "  " x);
      D.sat ctx x.t_u (set_cons_2t c)
    (** Set condition test *)
    let set_guard (c: set_cons) (x: t): t =
      { x with t_u = D.constrain ctx (set_cons_2t c) x.t_u }
    (** Forget (if the meaning of the sv changes) *)
    let sv_forget (sv: int) (x: t): t =
      drop_svs [ sv ] x
    (** Renaming (e.g., post join) *)
    let symvars_srename
        (om: (Offs.t * int) Offs.OffMap.t)
        (nm: (int * Offs.t) node_mapping)
        (svmo: setv_mapping option)
        (x: t)
        : t =
      let optmap fs x =
        match svmo with
        | None -> x
        | Some svm -> fs svm x in
      (* Initial status *)
      if debug_module then
        Log.debug "begin:\n%s" (t_2stri IntMap.empty "  " x); 
      if om != Offs.OffMap.empty then
        Log.fatal_exn "rename: should get empty OffMap";
      (* Roots should never be modified; fail if they do *)
      let do_setv setv =
        let f m i = try fst (IntMap.find i m.sm_map) with Not_found -> i in
        optmap f setv in
      IntSet.iter
        (fun setv ->
          if do_setv setv != setv then
            Log.fatal_exn "rename should not modify SETV root"
        ) x.t_roots;
      (* Remove SVs and SETVs that need to be *)
      let x =
        let x = drop_svs (IntSet.to_list nm.nm_rem) x in
        optmap (fun svm -> drop_setvs (IntSet.to_list svm.sm_rem)) x in
      (* Prepare map for renaming *)
      let ren =
        let make_l k_to_i =
          IntMap.fold (fun k0 (k1, _) acc -> (k_to_i k0, k_to_i k1) :: acc) in
        let ren = make_l sv_to_i nm.nm_map [ ] in
        let f svm ren = make_l setv_to_i svm.sm_map ren in
        let ren = optmap f ren in
        SETr_Rename.of_assoc_list ren in
      (* Renaming in SETr *)
      let u = D.rename_symbols ctx ren x.t_u in
      (* Addition of equalities *)
      let u =
        let fold k_to_i k_map acc =
          IntMap.fold
            (fun _ (k0, s) acc ->
              IntSet.fold
                (fun k1 ->
                  D.constrain ctx (L.Eq (L.Var (k_to_i k0), L.Var (k_to_i k1)))
              ) s acc
          ) k_map acc in
        let u = fold sv_to_i nm.nm_map u in
        let u = optmap (fun svm -> fold setv_to_i svm.sm_map) u in
        u in
      { x with t_u = u }
    (* Synchronization of the SV environment*)
    let sve_sync_top_down (sve: svenv_mod) (x: t): t =
      let l = PSet.fold (fun i acc -> i :: acc) sve.svm_mod [ ] in
      let l = PSet.fold (fun i acc -> i :: acc) sve.svm_rem l in
      drop_svs l x
    (* Removes all symbolic vars that are not in a given set *)
    (* may change a little bit *)
    let symvars_filter (skeep: IntSet.t) (setvkeep: IntSet.t) (x: t): t =
      let svs, setvs =
        List.fold_left
          (fun ((acc_sv, acc_setvs) as acc) i ->
            if i_is_sv i then
              let sv = i_to_sv i in
              if IntSet.mem sv skeep then acc
              else sv :: acc_sv, acc_setvs
            else
              let setv = i_to_setv i in
              if IntSet.mem setv setvkeep then acc
              else acc_sv, setv :: acc_setvs
          ) ([ ], [ ]) (D.symbols ctx x.t_u) in
      drop_svs svs (drop_setvs setvs x)
  end: DOMSET)
