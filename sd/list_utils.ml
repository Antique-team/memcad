(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_utils.ml
 **       utilities for the simplified list domain
 ** Xavier Rival, 2014/02/24 *)
open Data_structures
open Flags
open Graph
open Lib

open Graph_sig
open Ind_sig
open List_sig
open Nd_sig
open Sv_sig
open Svenv_sig
open Set_sig

open Gen_dom

open Dom_utils
open Graph_utils
open Ind_utils
open Inst_utils
open Set_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "l_uts___" and level = Log_level.DEBUG end)

let debug_module = false

(** Empty memory *)
let lmem_empty: lmem =
  { lm_mem       = IntMap.empty;
    lm_nkey      = Keygen.empty;
    lm_roots     = IntSet.empty;
    lm_svemod    = svenv_empty;
    lm_dangle    = IntSet.empty;
    lm_setvkey   = Keygen.empty;
    lm_setvroots = IntSet.empty;
    lm_setvkind  = IntMap.empty;
    lm_refcnt    = IntMap.empty; }

(** Pretty-printing *)
(* ldesc: full pretty-printer, to troubleshoot the list inductive contents
 *        (for other purposes, the shorter pretty-printer should be used) *)
let set_elt_2str: set_elt -> string = function
  | Se_this    -> "this"
  | Se_field i -> Printf.sprintf "[fld:%d]" i
let set_var_2str: set_var -> string = function
  | Sv_actual i      -> Printf.sprintf "[act:%d]" i
  | Sv_nextpar i     -> Printf.sprintf "[next:%d]" i
  | Sv_subpar (i, j) -> Printf.sprintf "[sub:(%d,%d)]" i j
let set_def_2str: set_def -> string = function
  | Sd_var s -> set_var_2str s
  | Sd_uplus (e, s) ->
      Printf.sprintf "{ %s } + %s" (set_elt_2str e) (set_var_2str s)
  | Sd_eunion (e, s) ->
      Printf.sprintf "{ %s } $u %s" (set_elt_2str e) (set_var_2str s)
  | Sd_union (s0, s1) ->
      Printf.sprintf " %s $u %s" (set_var_2str s0) (set_var_2str s1)
let set_equa_2str: set_equa -> string = function
  | Se_mem (e, s) ->
      Printf.sprintf "%s $in %s" (set_elt_2str e) (set_def_2str s)
  | Se_eq (s0, s1) ->
      Printf.sprintf "%s $eq %s" (set_var_2str s0) (set_def_2str s1)
let seti_2str (si: seti): string =
  let add j s0 s1 = if s0 = "" then s1 else s0^j^s1 in
  let folder f j s l = List.fold_left (fun acc x -> add j acc (f x)) s l in
  let pars = folder set_par_type_2str ", " "" si.s_params in
  let lp = Printf.sprintf "[%s]" pars in
  folder (fun p -> Printf.sprintf "(%s)" (set_equa_2str p)) " & " lp si.s_equas
let rec l_def_2stri (i: string) (def: l_def): string =
  let s = Printf.sprintf "%sList{0-%d;n@%d}\n" i def.ld_size def.ld_nextoff in
  let ni = "  "^i in
  let s =
    List.fold_left
      (fun acc (o, ld0) ->
        Printf.sprintf "%s%s@%d:\n%s" acc i o (l_def_2stri ni ld0)
      ) s def.ld_onexts in
  match def.ld_set with
  | None -> s
  | Some cons -> Printf.sprintf "%s%s%s\n" s i (seti_2str cons)
let l_call_2stri (i: string) (lc: l_call): string =
  let s =
    List.fold_left
      (fun acc f -> Printf.sprintf "%s%spar at: %d\n" acc i f) "" lc.lc_args in
  Printf.sprintf "Call to\n%s%s" (l_def_2stri i lc.lc_def) s
(* ldesc: compact pretty printer
 *        (to use when displaying abstract values) *)
let l_call_2strc (lc: l_call): string =
  let sargs =
    List.fold_left (fun acc i -> Printf.sprintf "%s%d;" acc i) "" lc.lc_args in
  match lc.lc_def.ld_name with
  | None ->
      Printf.sprintf "list{0-%d;n@%d;args:%s}" lc.lc_def.ld_size 
        lc.lc_def.ld_nextoff sargs
  | Some s  ->
      Printf.sprintf "%s{args:%s}" s sargs
let lheap_frag_2stri (ind: string) (is: nid): lheap_frag -> string = function
  | Lhemp -> ""
  | Lhpt pte -> block_2stria ind is pte ""
  | Lhlist l ->
      Printf.sprintf "%s%s ==#list%s==>\n" ind (nid_2str is) (l_call_2strc l)
  | Lhlseg (l, d) ->
      Printf.sprintf "%s%s ==#list%s==> %s\n" ind (nid_2str is) (l_call_2strc l)
        (nid_2str d)
let lnode_2stri (ind: string) (n: lnode): string =
  lheap_frag_2stri ind n.ln_i n.ln_e
let lmem_2stri ?(refcount: bool = false) (ind: string) (x: lmem): string =
  let s =
    Printf.sprintf "%ssetvs: %s\n%ssetv-roots:%s\n" ind
      (intset_2str (Keygen.get_nodes x.lm_setvkey)) ind
      (intset_2str x.lm_setvroots) in
  let s =
    if !Flags.flag_debug_list_dom then
      Printf.sprintf "%s%sroots: { %s }\n%sdangling: { %s }\n" s
        ind (IntSet.t_2str ", " x.lm_roots) ind (IntSet.t_2str ", " x.lm_dangle)
    else "" in
  let s =
    IntMap.fold
      (fun _ (n: lnode) (acc: string) ->
        let s0 =
          if !Flags.flag_debug_list_dom then
            let prevs =
              IntMap.find_err "lmem_2stri: broken RC" n.ln_i x.lm_refcnt in
            Printf.sprintf "%spredecessors of node %d: { %s }\n"
              ind n.ln_i (IntMap.t_2str ", " string_of_int prevs)
          else "" in
        Printf.sprintf "%s%s%s" acc s0 (lnode_2stri ind n)
      ) x.lm_mem s in
  let s =
    if refcount then
      IntMap.fold
        (fun i set acc ->
          Printf.sprintf "%s%s%d => { %s }\n" acc ind i
            (IntMap.t_2str ", " string_of_int set)
        ) x.lm_refcnt s
    else s in
  if flag_sanity_env_pp then
    Printf.sprintf "%s%s" s (svenv_2stri ind x.lm_svemod)
  else s
let lmem_2str: lmem -> string = lmem_2stri "  "

(** Reachability information in the graph: SVs that are used in a graph *)
let lnode_reach (ln: lnode): IntSet.t =
  match ln.ln_e with
  | Lhemp    -> IntSet.empty
  | Lhpt mc  -> Graph_utils.pt_edge_block_frag_reach mc
  | Lhlist _ -> IntSet.empty
  | Lhlseg (_, n) -> IntSet.singleton n
let lmem_reach (m: lmem) (start: IntSet.t): IntSet.t =
  let rec aux (acc_done, to_follow) =
    if to_follow = IntSet.empty then acc_done
    else
      let c = IntSet.choose to_follow in
      let ln = IntMap.find_err "lmem_reach" c m.lm_mem in
      let to_follow =
        IntSet.fold
          (fun i acc_to_follow ->
            if IntSet.mem i acc_done then acc_to_follow
            else IntSet.add i acc_to_follow
          ) (lnode_reach ln) to_follow in
      aux (IntSet.add c acc_done, IntSet.remove c to_follow) in
  aux (IntSet.empty, start)

(** Sanity checks *)
(* - all references should belong to the graph
 * - consistency between prevs, refcount, and edges
 * - all offsets should be integers
 *)
let sanity_check (loc: string) (x: lmem): unit =
  if Flags.flag_sanity_ldom then
    (* auxilliary functions *)
    let abort () =
      Log.fatal_exn "sanity_check: failed (%s): %s"
        loc (lmem_2stri ~refcount:true "  " x) in
    let check_successor (d: int): unit =
      if not (IntMap.mem d x.lm_mem) then
        begin
          Log.error "successor not in the graph %d" d;
          abort ()
        end in
    let check_bound (bnd: Bounds.t): unit =
      if not (Bounds.t_is_const bnd) then
        Log.fatal_exn "non constant bound: %s" (Bounds.t_2str bnd) in
    let check_offset (off: Offs.t): unit =
      if not (Offs.t_is_const off) then
        Log.fatal_exn "non constant offset: %s" (Offs.t_2str off) in
    (* - lm_refcnt and lm_mem should have the same numbers of elements *)
    if IntMap.cardinal x.lm_refcnt != IntMap.cardinal x.lm_mem then
      Log.fatal_exn "refcount and abstract memory mismatch";
    (* - all references to successors should belong to the graph *)
    let prevs, setvs =
      let f i j a =
        let om = IntMap.find_val IntMap.empty i a in
        let ov = IntMap.find_val 0 j om in
        IntMap.add i (IntMap.add j (ov + 1) om) a in
      let f_l_call (lc: l_call) (s: IntSet.t): IntSet.t =
        List.fold_left (fun s i -> IntSet.add i s) s lc.lc_args in
      IntMap.fold
        (fun i ln (accp, accsetvs) ->
          match ln.ln_e with
          | Lhemp -> (accp, accsetvs)
          | Lhpt mc ->
              Block_frag.iter_bound check_bound mc;
              let accp =
                Block_frag.fold_base
                  (fun _ pe acc ->
                    check_offset (Offs.of_size pe.pe_size);
                    check_offset (snd pe.pe_dest);
                    f (fst pe.pe_dest) i acc
                  ) mc accp in
              accp, accsetvs
          | Lhlist c -> accp, f_l_call c accsetvs
          | Lhlseg (c, d) -> check_successor d; f d i accp, f_l_call c accsetvs
        ) x.lm_mem (IntMap.empty, IntSet.empty) in
    (* - consistency of the SETVs *)
    Keygen.sanity_check "SETV occurrences" setvs x.lm_setvkey;
    (* - consistency between prevs and refcount, and edges *)
    IntMap.iter
      (fun i p ->
        let cp = IntMap.find_val IntMap.empty i prevs in
        IntMap.iter
          (fun j n ->
            let cn = IntMap.find_val 0 j cp in
            if cn != n then Log.fatal_exn "refcount set mismatch"
          ) p
      ) x.lm_refcnt;
    (* - consistency of dangle: should contain exactly non reachable SVs *)
    let reach = lmem_reach x x.lm_roots in
    if IntSet.inter reach x.lm_dangle != IntSet.empty then
      Log.fatal_exn "reachable SVs have been moved into dangle";
    let n_c = IntSet.cardinal reach + IntSet.cardinal x.lm_dangle
    and n_e = IntMap.cardinal x.lm_mem in
    if n_c < n_e then Log.fatal_exn "dangle: some SVs must be missing";
    if n_c > n_e then Log.fatal_exn "dangle: some SVs must be unbound";
    ( )

(** Management of SVs *)
let sve_sync_bot_up (m: lmem): lmem * svenv_mod =
  { m with lm_svemod = Dom_utils.svenv_empty }, m.lm_svemod

(** Symbolic variables operations *)
(* Membership and find *)
let sv_mem (i: int) (x: lmem): bool = IntMap.mem i x.lm_mem
let sv_find (i: nid) (x: lmem): lnode =
  try IntMap.find i x.lm_mem
  with
  | Not_found ->
      Log.info "sv_find %d fails:\n%s" i (lmem_2stri "  " x);
      Log.fatal_exn "node %d not found" i
(* Making an SV dangling (i.e., could be quickly removed) *)
let rec sv_dangle_add (i: int) (x: lmem): lmem =
  if IntSet.mem i x.lm_dangle then x
  else
    let x = { x with lm_dangle = IntSet.add i x.lm_dangle } in
    let r = lnode_reach (sv_find i x) in
    IntSet.fold sv_dangle_add_check r x
and sv_dangle_add_check (i: int) (x: lmem): lmem =
  if IntSet.mem i x.lm_roots then x
  else
    let old_prevs =
      try IntMap.find i x.lm_refcnt
      with Not_found -> Log.fatal_exn "NF in move_dangle %d" i in
    if debug_module then
      Log.debug "old_prevs: {%s}"
        (IntMap.t_2str ", " string_of_int old_prevs);
    let b_subset =
      IntMap.fold
        (fun i _ acc -> acc && IntSet.mem i x.lm_dangle) old_prevs true in
    if b_subset then sv_dangle_add i x (* i is dangling *)
    else x
(* Removing an SV from dangling (i.e., should be preserved) *)
let rec sv_dangle_rem (i: int) (x: lmem): lmem =
  if IntSet.mem i x.lm_dangle then
    let x = { x with lm_dangle = IntSet.remove i x.lm_dangle } in
    let r = lnode_reach (sv_find i x) in
    IntSet.fold sv_dangle_rem r x (* also move successors out of dangling *)
  else x
(* Information extraction *)
let sv_kind (i: int) (x: lmem): region_kind =
  match (sv_find i x).ln_e with
  | Lhemp    -> Kemp
  | Lhpt _   -> Kpt
  | Lhlist _ -> Kind
  | Lhlseg _ -> Kseg
(* Addition *)
let sv_add ?(root:bool = false) (i: nid) (nt: ntyp) (x: lmem): lmem =
  assert (not (IntMap.mem i x.lm_mem));
  let lnode_empty = { ln_i     = i;
                      ln_e     = Lhemp;
                      ln_typ   = nt;
                      ln_odesc = None } in
  let svm = { x.lm_svemod with svm_add = PMap.add i nt x.lm_svemod.svm_add } in
  { x with
    lm_nkey   = Keygen.use_key x.lm_nkey i;
    lm_mem    = IntMap.add i lnode_empty x.lm_mem;
    lm_svemod = svm;
    lm_refcnt = IntMap.add i IntMap.empty x.lm_refcnt;
    lm_dangle = if root then x.lm_dangle else IntSet.add i x.lm_dangle;
    lm_roots  = if root then IntSet.add i x.lm_roots else x.lm_roots; }
let sv_add_fresh ?(root:bool = false) (nt: ntyp) (x: lmem): int * lmem =
  let _, i = Keygen.gen_key x.lm_nkey in
  i, sv_add ~root:root i nt x
let sv_rem (i: int) (x: lmem): lmem =
  if debug_module then
    Log.debug "sv_rem: %d" i;
  if IntSet.mem i x.lm_roots then Log.fatal_exn "sv_rem called on root node";
  let n = sv_find i x in
  match n.ln_e with
  | Lhemp -> { x with
               lm_mem    = IntMap.remove i x.lm_mem;
               lm_nkey   = Keygen.release_key x.lm_nkey i;
               lm_dangle = IntSet.remove i x.lm_dangle;
               lm_refcnt = IntMap.remove i x.lm_refcnt;
               lm_svemod = svenv_rem i x.lm_svemod }
  | _ -> Log.fatal_exn "sv_rem: SV region is non empty"
(* Collects all SVs *)
let sv_col (x: lmem): IntSet.t =
  IntMap.fold (fun i _ acc -> IntSet.add i acc) x.lm_mem IntSet.empty
(* Check whether SV is the address of an inductive or segment predicate *)
let sv_is_ind (i: int) (x: lmem): bool =
  match (sv_find i x).ln_e with
  | Lhemp | Lhpt _ -> false
  | Lhlist _ | Lhlseg _ -> true
(* Operations on roots *)
let sv_root (i: int) (x: lmem): lmem =
  sv_dangle_rem i { x with lm_roots = IntSet.remove i x.lm_roots }
let sv_unroot (i: int) (x: lmem): lmem =
  if not (IntSet.mem i x.lm_roots) then
     Log.fatal_exn "sv_unroot not called on root";
  sv_dangle_add_check i { x with lm_roots = IntSet.remove i x.lm_roots }

(** Management of SETVs *)
let setv_add_fresh (root: bool) (ko: set_par_type option) (x: lmem)
    : int * lmem =
  let kg, setv = Keygen.gen_key x.lm_setvkey in
  let x = { x with lm_setvkey = kg } in
  let x =
    if root then { x with lm_setvroots = IntSet.add setv x.lm_setvroots }
    else x in
  let x =
    match ko with
    | None -> x
    | Some k -> { x with lm_setvkind = IntMap.add setv k x.lm_setvkind } in
  setv, x
let setv_add (root: bool) (setv: int) (x: lmem): lmem =
  let x =
    if root then { x with lm_setvroots = IntSet.add setv x.lm_setvroots }
    else x in
  { x with lm_setvkey = Keygen.use_key x.lm_setvkey setv }
let setv_rem (setv: int) (x: lmem): lmem =
  { x with
    lm_setvkey  = Keygen.release_key x.lm_setvkey setv;
    lm_setvkind = IntMap.remove setv x.lm_setvkind }
let setv_type (lm: lmem) (setv: int): set_par_type option =
  try Some (IntMap.find setv lm.lm_setvkind) with Not_found -> None
let setv_is_root (lm: lmem) (setv: int): bool =
  IntSet.mem setv lm.lm_setvroots
let setv_set (lm: lmem): IntSet.t = Keygen.get_nodes lm.lm_setvkey
let setv_roots (lm: lmem): IntSet.t = lm.lm_setvroots

(** Management of reference counts and back pointers *)
(* Effect of adding a predicate on prev, involving next *)
let add_refcount (prev: int) (next: int) (x: lmem): lmem =
  let old_prevs =
    try IntMap.find next x.lm_refcnt
    with
    | Not_found ->
        Log.info "shape:\n%s" (lmem_2stri "  " x);
        Log.fatal_exn "NF in add_refcount %d" next in
  let old_count = try IntMap.find prev old_prevs with Not_found -> 0 in
  let new_count = old_count + 1 in
  let new_prevs = IntMap.add prev new_count old_prevs in
  let x = { x with lm_refcnt = IntMap.add next new_prevs x.lm_refcnt; } in
  if IntSet.mem prev x.lm_dangle then x
  else sv_dangle_rem next x
(* Effect of removing a predicate on prev, involving next *)
let rem_refcount (prev: int) (next: int) (x: lmem): lmem =
  if debug_module then
    Log.debug "destroying: %d -> %d" prev next;
  let old_prevs =
    try IntMap.find next x.lm_refcnt
    with Not_found ->
      Log.info "rem_rc: %d,%d\n%s" prev next (lmem_2stri "  " x);
      Log.fatal_exn "NF in rem_refcount %d" next in
  let old_count = IntMap.find_val 0 prev old_prevs in
  let new_count = old_count - 1 in
  let new_prevs =
    if new_count <= 0 then IntMap.remove prev old_prevs
    else IntMap.add prev new_count old_prevs in
  let x = { x with lm_refcnt = IntMap.add next new_prevs x.lm_refcnt } in
  if new_prevs = IntMap.empty
      && (not (IntSet.mem next x.lm_roots)) then sv_dangle_add next x
  else sv_dangle_add_check next x
(* Effect of a series of predicate removals *)
let rem_refcounts (prev: int) (nexts: IntSet.t) (x: lmem): lmem =
  IntSet.fold (fun next -> rem_refcount prev next) nexts x

(** Memory block operations *)

(* Existence of a points-to edge *)
let pt_edge_mem ((i,o): onode) (x: lmem): bool =
  let nsrc = sv_find i x in
  match nsrc.ln_e with
  | Lhemp | Lhlist _ | Lhlseg _ -> false
  | Lhpt mc -> Block_frag.mem (Bounds.of_offs o) mc

(* Finding a pt_edge, for internal use (no size used, so cannot be used to
 *  dereference an edge) *)
let pt_edge_find
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,os): onode) (x: lmem): pt_edge =
  let nsrc = sv_find is x in
  let bnd = Bounds.of_offs os in
  if nsrc.ln_typ != Ntaddr then
    Log.info "Issue in pt_edge_find; type of src is %s"
      (Ind_utils.ntyp_2str nsrc.ln_typ);
  match nsrc.ln_e with
  | Lhemp | Lhlist _ | Lhlseg _ ->
      Log.fatal_exn "pt_edge_find: does not exist (1)"
  | Lhpt mc ->
      try Block_frag.find_addr_sat sat bnd mc
      with Not_found -> Log.fatal_exn "pt_edge_find: does not exist (2)"

(* Splitting, appending points-to edges *)
let pt_edge_split (sat: n_cons -> bool) ((is,os): bnode)
    (mid_point: Offs.size) (x: lmem): lmem =
  if debug_module then
    Log.debug "call to pt_edge_split\n - (%d,%s)\n - %s\n%s" is
      (Bounds.t_2str os) (Offs.size_2str mid_point) (lmem_2stri "   " x);
  let old_pt = pt_edge_find sat (is, Bounds.to_offs os) x in
  assert (Offs.size_leq sat mid_point old_pt.pe_size);
  let old_src = sv_find (fst old_pt.pe_dest) x in
  let sz0 = mid_point
  and sz1 = Offs.size_sub_size old_pt.pe_size mid_point in
  let n0, x = sv_add_fresh old_src.ln_typ x in
  let n1, x = sv_add_fresh old_src.ln_typ x in
  let pe_0 = { pe_size = sz0 ; pe_dest = n0, Offs.zero }
  and pe_1 = { pe_size = sz1 ; pe_dest = n1, Offs.zero } in
  let nsrc = sv_find is x in
  (* node_assert_placed ? *)
  let bndmid = Bounds.add_size os mid_point in
  let bndhi  = Bounds.add_size os old_pt.pe_size in
  if debug_module then
    Log.debug "pt_edge_split:\n - pos %s\n - siz %s\n - res %s"
      (Bounds.t_2str os) (Offs.size_2str old_pt.pe_size) (Bounds.t_2str bndhi);
  let nblock =
    let oblock =
      match nsrc.ln_e with
      | Lhemp -> Block_frag.create_empty os
      | Lhpt block -> block
      | _ -> Log.fatal_exn "pt_edge_split: improper edge" in
    Block_frag.split_sat sat os bndmid bndhi pe_0 pe_1 oblock in
  let nsrc = { nsrc with ln_e = Lhpt nblock } in
  let x =
    rem_refcount is (fst old_pt.pe_dest)
      (add_refcount is n0
         (add_refcount is n1
            { x with lm_mem = IntMap.add is nsrc x.lm_mem })) in
  x
let pt_edge_block_append
    ?(nochk: bool = false) (* de-activates check that bounds coincide (join) *)
    ((is, bnd): bnode) (pe: pt_edge) (x: lmem): lmem =
  assert (Bounds.t_is_const bnd);
  sanity_check "before-append" x;
  let nsrc = sv_find is x in
  let oblock =
    match nsrc.ln_e with
    | Lhemp -> Block_frag.create_empty bnd
    | Lhpt block -> block
    | _ -> Log.fatal_exn "pt_edge_block_append: improper edge" in
  let nblock =
    Block_frag.append_tail ~nochk: nochk bnd
      (Bounds.add_size bnd pe.pe_size) pe oblock in
  let nsrc = { nsrc with ln_e = Lhpt nblock } in
  let x = { x with lm_mem = IntMap.add is nsrc x.lm_mem } in
  let x = add_refcount is (fst pe.pe_dest) x in
  sanity_check "after-append" x;
  x
(* Removal of a bunch of points-to edges from a node *)
let pt_edge_block_destroy ?(remrc: bool = true) (is: nid) (x: lmem): lmem =
  sanity_check "block_destroy,before" x;
  let n = sv_find is x in
  match n.ln_e with
  | Lhpt _ ->
      let nn = { n with ln_e = Lhemp } in
      let posts = lnode_reach n in
      if debug_module then
        Log.debug "before block_destroy %d: { %s }\n%s" is
          (IntSet.t_2str ";" posts) (lmem_2stri ~refcount: true "  " x);
      let x = { x with lm_mem = IntMap.add is nn x.lm_mem } in
      let x = if remrc then rem_refcounts is posts x else x in
      if debug_module then
        Log.debug "after block_destroy %d: { %s }\n%s" is
          (IntSet.t_2str ";" posts) (lmem_2stri ~refcount: true "  " x);
      sanity_check "block_destroy,after" x;
      x
  | _ -> Log.fatal_exn "pt_edge_block_destroy: not a points-to edge"
(* Try to decide if an offset range is in a single points-to edge
 *  of a fragmentation, and if so, return its destination *)
let pt_edge_find_interval
    (sat: n_cons -> bool)
    (is: nid) (* node representing the base address *)
    (min_off: Offs.t) (* minimum offset of the range being looked for *)
    (size: int)       (* size of the range being looked for *)
    (x: lmem): pt_edge option =
  assert (Offs.t_is_const min_off);
  match (sv_find is x).ln_e with
  | Lhemp | Lhlist _ | Lhlseg _ -> None
  | Lhpt mc ->
      let bnd_low = Bounds.of_offs min_off in
      let bnd_hi  = Bounds.of_offs (Offs.add_int min_off size) in
      try Some (Block_frag.find_chunk_sat sat bnd_low bnd_hi mc)
      with Not_found -> None
(* Retrieval algorithm that encapsulates the search for extract and replace *)
let pt_edge_retrieve
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,bnd): bnode) (mc: pt_edge Block_frag.t) (old_sz: Offs.size)
    : pt_edge =
  assert (Bounds.t_is_const bnd);
  try Block_frag.find_addr_sat sat bnd mc
  with Not_found -> Log.fatal_exn "NF in pt_edge_retrieve"
(* Replacement of a points-to edge by another *)
let pt_edge_replace
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,os): onode) (pte: pt_edge): lmem -> lmem =
  assert (Offs.t_is_const os);
  let bnd = Bounds.of_offs os in
  let rec aux (x: lmem): lmem =
    sanity_check "before-replace" x;
    let n = sv_find is x in
    match n.ln_e with
    | Lhemp -> Log.fatal_exn "pt_edge_repace: empty"
    | Lhpt mc ->
        begin
          let old_pe = pt_edge_retrieve sat (is,bnd) mc pte.pe_size in 
          match Offs.size_order sat pte.pe_size old_pe.pe_size with
          | Some c ->
              if c = 0 then (* i.e., pte.pe_size = old_pe.pe_size *)
                (* the edges found matches exactly the region to overwrite *)
                let nmc = Block_frag.replace_sat sat bnd pte mc in
                let nn = { n with ln_e = Lhpt nmc } in
                add_refcount is (fst pte.pe_dest)
                  (rem_refcount is (fst old_pe.pe_dest)
                     { x with lm_mem = IntMap.add is nn x.lm_mem })
              else if c < 0 then (* i.e., pte.pe_size < old_pe.pe_size then *)
                (* only part of the edge needs be overwritten;
                 * we should split it *)
                aux (pt_edge_split sat (is,bnd) pte.pe_size x)
              else (* c > 0, i.e., pte.pe_size > old_pe.pe_size *)
                (* we would have to merging edges together... *)
                Log.fatal_exn "pt_edge_replace: edges merging unsupported"
          | None ->
              if Offs.size_leq sat pte.pe_size old_pe.pe_size then
                aux (pt_edge_split sat (is,bnd) pte.pe_size x)
              else Log.fatal_exn "incomparable sizes"
        end
    | Lhlist _ -> raise (Unfold_request (Uloc_main is, Udir_fwd))
    | Lhlseg _ -> raise (Unfold_request (Uloc_main is, Udir_fwd)) in
  fun x ->
    let x = aux x in
    sanity_check "after-replace" x;
    x
(* Extraction of a points to edge: reads, after split if necessary *)
let pt_edge_extract
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,os): onode) (isz: int): lmem -> lmem * pt_edge =
  assert (Offs.t_is_const os);
  let bnd = Bounds.of_offs os in
  let sz = Offs.size_of_int isz in
  let rec aux (x: lmem): lmem * pt_edge =
    sanity_check "before-extract" x;
    let n = sv_find is x in
    if !flag_debug_graph_blocks && false then
      Log.force "Call to pt_edge_extract.aux:  (%d,%s)"
        is (Offs.t_2str os);
    match n.ln_e with
    | Lhemp -> raise (No_edge "pt_edge_extract: empty")
    | Lhpt mc ->
        begin
          let pte = pt_edge_retrieve sat (is,bnd) mc sz in
          match Offs.size_order sat pte.pe_size sz with
          | Some c ->
              if c = 0 then (* equality, pte.pe_size = sz *)
                (* the edge found matches the size of the deref cell *)
                x, pte
              else if c > 0 then (* pte.pe_size > sz *)
                (* only part of the edge should be read; we should split *)
                begin
                  aux (pt_edge_split sat (is,bnd) sz x)
                end
              else (* c < 0, i.e., pte.pe_size < sz *)
                Log.fatal_exn "size mismatch"
          | None -> Log.fatal_exn "incomparable sizes"
        end
    | Lhlist _ -> raise (Unfold_request (Uloc_main is, Udir_fwd))
    | Lhlseg _ -> raise (Unfold_request (Uloc_main is, Udir_fwd)) in
  aux

(* Addition of a list edge *)
let list_edge_add (i: int) (ld: l_call) (x: lmem): lmem =
  let ln = sv_find i x in
  match ln.ln_e with
  | Lhemp ->
      let ln = { ln with
                 ln_e     = Lhlist ld;
                 ln_odesc = Some ld.lc_def } in
      { x with lm_mem = IntMap.add i ln x.lm_mem }
  | Lhpt _ | Lhlist _ | Lhlseg _ -> Log.fatal_exn "list_edge_add"
(* Removal of a list edge *)
let list_edge_rem (i: int) (x: lmem): lmem =
  let ln = sv_find i x in
  match ln.ln_e with
  | Lhlist _ ->
      let ln = { ln with ln_e = Lhemp } in
      { x with lm_mem = IntMap.add i ln x.lm_mem }
  | Lhemp | Lhpt _ | Lhlseg _ -> Log.fatal_exn "list_edge_rem"

(* Addition of a segment edge *)
let lseg_edge_add (src: int) (dst: int) (lc: l_call) (x: lmem): lmem =
  let ln = sv_find src x in
  match ln.ln_e with
  | Lhemp ->
      let ln = { ln with
                 ln_e     = Lhlseg (lc, dst);
                 ln_odesc = Some lc.lc_def; } in
      add_refcount src dst { x with lm_mem = IntMap.add src ln x.lm_mem }
  | Lhpt _ | Lhlist _ | Lhlseg _ -> Log.fatal_exn "lseg_edge_add"
(* Removal of a segment edge *)
let lseg_edge_rem (i: int) (x: lmem): lmem =
  let ln = sv_find i x in
  match ln.ln_e with
  | Lhlseg (_, dst) ->
      let ln = { ln with ln_e = Lhemp } in
      rem_refcount i dst { x with lm_mem = IntMap.add i ln x.lm_mem }
  | Lhemp | Lhpt _ | Lhlist _ -> Log.fatal_exn "lseg_edge_rem"

(* Number of remaining edges *)
let num_edges (x: lmem): int =
  IntMap.fold
    (fun _ ln acc ->
      match ln.ln_e with
      | Lhemp -> acc
      | Lhpt _ | Lhlist _ | Lhlseg _ -> 1 + acc
    ) x.lm_mem 0

(** Garbage collection support *)
(* Removal of all nodes not reachable from a set of roots
 * Returns the new memory state and the set of removed setv *)
let gc (roots: int Aa_sets.t) (x: lmem): lmem * IntSet.t =
  let do_full_gc = false in
  sanity_check "before-gc" x;
  let l_call_col_setv (lc: l_call): IntSet.t =
    List.fold_left (fun acc i -> IntSet.add i acc) IntSet.empty lc.lc_args in
  (* internal function to dispose a node *)
  let sv_dispose (increm: bool) (i: int) (x: lmem)
      : lmem * IntSet.t =
    if increm then incr Statistics.gc_stat_incr_rem
    else incr Statistics.gc_stat_full_rem;
    let x, s =
      match (sv_find i x).ln_e with
      | Lhemp -> x, IntSet.empty
      | Lhpt _ -> pt_edge_block_destroy i x, IntSet.empty
      | Lhlist lc ->
          list_edge_rem i x, l_call_col_setv lc
      | Lhlseg (lc, _) -> 
          lseg_edge_rem i x, l_call_col_setv lc in
    sv_rem i x, s in
  (* internal dispose function that makes no sanity check;
   *  (it is good for the removal of many svs in one shot)
   * it also returns the sets of svs,setvs that are not used anymore *)
  let sv_dispose_series (increm: bool) (i: int) (lm: lmem)
      : lmem * IntSet.t * IntSet.t =
    if increm then incr Statistics.gc_stat_incr_rem
    else incr Statistics.gc_stat_full_rem;
    let n = sv_find i lm in
    let svs = lnode_reach n in
    let setvs =
      match n.ln_e with
      | Lhemp | Lhpt _ -> IntSet.empty
      | Lhlist lc | Lhlseg (lc, _) -> l_call_col_setv lc in
    let svemod =
      if IntSet.mem i lm.lm_roots then lm.lm_svemod
      else svenv_rem i lm.lm_svemod in
    let lm =
      { lm with
        lm_nkey   = Keygen.release_key lm.lm_nkey i;
        lm_mem    = IntMap.remove i lm.lm_mem;
        lm_dangle = IntSet.remove i lm.lm_dangle;
        lm_svemod = svemod;
        lm_refcnt = IntMap.remove i lm.lm_refcnt} in
    lm, svs, setvs in
  (* Incremental GC *)
  let incr_gc x =
    if debug_module then
      Log.debug "doing incr-GC";
    incr Statistics.gc_stat_incr_num;
    let x, svs, setvs =
      IntSet.fold
        (fun i (x, asvs, asetvs) ->
          let x, svs, setvs = sv_dispose_series true i x in
          x, IntMap.add i svs asvs, IntSet.union setvs asetvs
        ) x.lm_dangle (x, IntMap.empty, IntSet.empty) in
    if debug_module then Log.debug "middle of incr-GC";
    IntMap.fold
      (fun prev nexts ->
        IntSet.fold
          (fun next x ->
            try
              let old_prevs = IntMap.find next x.lm_refcnt in
              let old_count = IntMap.find_val 0 prev old_prevs in
              if old_count <= 0 then Log.fatal_exn "reached 0";
              let new_count = old_count - 1 in
              let new_prevs =
                if new_count <= 0 then IntMap.remove prev old_prevs
                else IntMap.add prev new_count old_prevs in
              { x with lm_refcnt = IntMap.add next new_prevs x.lm_refcnt }
            with Not_found -> x
          ) nexts
      ) svs x, setvs in
  (* Full GC *)
  let full_gc x =
    if debug_module then Log.debug "doing full-GC";
    incr Statistics.gc_stat_full_num;
    (* Compute reachability *)
    let reach =
      let r = ref IntSet.empty
      and todos = ref roots in
      while !todos != Aa_sets.empty do
        let i = Aa_sets.min_elt !todos in
        r := IntSet.add i !r;
        todos := Aa_sets.remove i !todos;
        let ln = IntMap.find_err "List GC" i x.lm_mem in
        IntSet.iter
          (fun i ->
            if not (IntSet.mem i !r) then todos := Aa_sets.add i !todos)
          (lnode_reach ln)
      done;
      !r in
    (* Remove unreachable nodes *)
    let nremoved =
      IntMap.fold
        (fun i _ acc ->
          if IntSet.mem i reach then acc else IntSet.add i acc
        ) x.lm_mem IntSet.empty in
    let x, s = 
      IntSet.fold 
        (fun i (x, s_acc) -> 
          let x, s = sv_dispose false i x in
          x, IntSet.union s s_acc
        ) nremoved (x, IntSet.empty) in
    sanity_check "after-gc" x; (* to do for set *)
    x, s in
  let x, s = incr_gc x in
  if debug_module then Log.debug "incr-GC done";
  if do_full_gc then 
    let x, s1 = full_gc x in
    x, IntSet.union s s1
  else x, s

(** Inductive set parameters construction *)
(* - unfold a seg or an ind edge presented by lc: l_call in the right side 
 * - with a new segment
 * - and a new seg or an new ind edge
 * - also returns the set of removed SETVs
 * - and          the set of all new SETVs *)
let gen_ind_setpars (lm: lmem) (lc: l_call)
    : lmem * l_call * l_call * (set_cons list) * IntSet.t * IntSet.t =
  let l_paras = 
    match lc.lc_def.ld_set with
    | None -> []
    | Some si -> si.s_params in
  let lm, lseg_args, l_args, c, setvs_rem, setvs_add =
    List.fold_left2
      (fun (lm, lseg_args, l_args, c, acc_rem, acc_add) a k ->
        let seg_arg, lm = setv_add_fresh false (Some k) lm in
        let l_arg, lm   = setv_add_fresh false (Some k) lm in
        let c = 
          if k.st_const then
            let c = S_eq (S_var l_arg, S_var a) :: c in
            S_eq (S_var seg_arg, S_var a) :: c
          else if k.st_head then
            S_eq (S_var a, S_uplus (S_var seg_arg, S_var l_arg)) :: c 
          else Log.todo_exn "unhandled kind" in
        (lm, seg_arg :: lseg_args, l_arg :: l_args, c,
         IntSet.add a acc_rem,
         IntSet.add seg_arg (IntSet.add l_arg acc_add))
      )
      (lm, [ ], [ ], [ ], IntSet.empty, IntSet.empty)
      (List.rev lc.lc_args)
      (List.rev l_paras) in
  lm, { lc with lc_args = lseg_args }, { lc with lc_args = l_args }, c,
  setvs_rem, setvs_add

(* Splitting an inductive predicate into a pair of calls;
 * this function takes care of the parameters and prepares a list of
 * set constraints that should also be taken into account to precisely
 * account for the SETV parameter kinds (const, head, etc) *)
let split_indpredpars (lc: l_call) (lm: lmem)
    : lmem * l_call * l_call * set_cons list =
  let params =
    match lc.lc_def.ld_set with
    | None -> []
    | Some si -> si.s_params in
  let lm, l0, l1, sc =
    let rec aux ((lm, call0, call1, cons) as acc) lcl params =
      match lcl, params with
      | [ ], [ ] -> acc
      | i :: lcl0, k :: params0 ->
          (* generate two keys in the right *)
          let i0, lm = setv_add_fresh false (Some k) lm in (* mapped to il *)
          let i1, lm = setv_add_fresh false (Some k) lm in (* remaining par *)
          let setctr =
            if k.st_const then
              [ S_eq (S_var i, S_var i0) ; S_eq (S_var i, S_var i1) ]
            else if k.st_add || k.st_head then
              [ S_eq (S_var i, S_uplus (S_var i0, S_var i1)) ]
            else Log.todo_exn "unhandled kind-0" in
          aux (lm, i0 :: call0, i1 :: call1, setctr @ cons) lcl0 params0
      | _, _ -> Log.fatal_exn "split_indpredpars: pars of distinct lengths" in
    aux (lm, [ ], [ ], [ ]) lc.lc_args params in
  lm, { lc with lc_args = List.rev l0 }, { lc with lc_args = List.rev l1 }, sc


(** Utilities for join *)
(* Initialization of the join algorithm
 * - both inputs should have the same root SETVs
 * - returns the initial join graph,
 *   the SETVs to add to the left,
 *   the SETVs to add to the right,
 *   the SETVs to remove from both at the end (all introduced SETV except the
 *   roots *)
let init_from_roots (msv: (int * int) IntMap.t) (msetv: (int * int) IntMap.t)
    (xl: lmem) (xr: lmem): lmem * IntSet.t * IntSet.t * IntSet.t =
  (* 1. setting up the SVs *)
  let lm =
    IntMap.fold
      (fun ii (il, ir) acc ->
        let nl = sv_find il xl and _ = sv_find ir xr in
        sv_add ~root:true ii nl.ln_typ acc
      ) msv lmem_empty in
  (* 2. setting up the SETVs *)
  let roots =
    let roots_l = setv_roots xl in
    assert (IntSet.equal roots_l (setv_roots xr));
    roots_l in
  let setvl = setv_set xl and setvr = setv_set xr in
  let toadd_l = IntSet.diff setvr setvl and toadd_r = IntSet.diff setvl setvr in
  let all_setv = IntSet.union setvl setvr in
  let all_non_roots = IntSet.diff all_setv roots in
  if debug_module then
    Log.debug "init_from_roots:\n%s\n%s\n%s\n%s\n%s\n%s"
      (intset_2str setvl) (intset_2str setvr)
      (intset_2str toadd_l) (intset_2str toadd_r)
      (intset_2str all_setv) (intset_2str all_non_roots);
  let lm =
    IntSet.fold
      (fun i acc ->
        if Keygen.key_is_used acc.lm_setvkey i then acc
        else setv_add (setv_is_root xl i) i acc
      ) all_setv lm in
  lm, toadd_l, toadd_r, all_non_roots

(* Comparison of list descriptors *)
let l_call_compare (lc0: l_call) (lc1: l_call): int =
  (* Huisong: maybe extend to check other fields *)
  (* here we only compare the name when both have name*)
  let b = match lc0.lc_def.ld_name, lc1.lc_def.ld_name with
  | Some n0, Some n1 -> n0 = n1
  | _, _ -> false in
  if b then 0
  else 
    begin
      assert (lc0.lc_def.ld_set = lc1.lc_def.ld_set
                && lc0.lc_def.ld_onexts = lc1.lc_def.ld_onexts);
      let c = lc0.lc_def.ld_size - lc1.lc_def.ld_size in
      if c = 0 then lc0.lc_def.ld_nextoff - lc1.lc_def.ld_nextoff
      else c
    end


(** Inductive definitions *)
(* Global map of list-like inductive definitions *)
let list_ind_defs: l_def StringMap.t ref = ref StringMap.empty
(* Experimental code, to try to look for list like inductive defs *)
let exp_search_lists ( ): unit =
  let module M = struct exception Stop of string end in (* local bail out *)
  (* Reinitiliazes the global map of list like inductive definitions *)
  list_ind_defs := StringMap.empty;
  let name_2ldef name =
    try StringMap.find name !list_ind_defs
    with Not_found -> raise (M.Stop (Printf.sprintf "%s not found" name)) in
  let aux_rule (iname: string) (ind: ind) (r: irule): l_def =
    let m_subinds, m_fieldsoff, m_idxoff, m_fieldsrev =
      List.fold_left
        (fun (accsubs, accfo, accio, accfr) -> function
          | Hacell cell ->
              begin
                match cell.ic_dest, Offs.to_int_opt cell.ic_off with
                | `Fa_var_new i, Some o ->
                    ( accsubs, IntMap.add o cell accfo,
                      IntMap.add i o accio, IntMap.add i cell accfr )
                | _, _ -> raise (M.Stop "field")
              end
          | Haind icall ->
              begin
                match icall.ii_maina with
                | `Fa_this -> raise (M.Stop "main field")
                | `Fa_var_new i ->
                    IntMap.add i icall accsubs, accfo, accio, accfr
              end
        ) (IntMap.empty, IntMap.empty, IntMap.empty, IntMap.empty) r.ir_heap in
    let idx_2off idx =
      try IntMap.find idx m_idxoff
      with Not_found -> Log.fatal_exn "symvar %d at no offset" idx in
    (* Extracting a single next field, and tail inductive predicate *)
    let onext, callnext, others =
      let self, others =
        IntMap.fold
          (fun i call (self, others) ->
            if String.compare call.ii_ind iname = 0 then
              (idx_2off i, call) :: self, IntMap.remove i others
            else self, others
          ) m_subinds ([ ], m_subinds) in
      match self with
      | [ ] -> raise (M.Stop "no next field")
      | _ :: _ :: _ -> raise (M.Stop "several next fields")
      | [ inext, callnext ] -> inext, callnext, others in
    (* Extracting calls corresponding to nested structures, and the set
     *   parameters of the recursive calls (to construct equalities) *)
    let nest_calls, nest_call_setpars =
      IntMap.fold
        (fun i ic (c, sp) ->
          (idx_2off i, name_2ldef ic.ii_ind) :: c, ic.ii_args :: sp)
        others ([ ], [ ]) in
    (* Make a dicho of new SETv formal variables *)
    let subcall_pars =
      List.fold_lefti
        (fun i r -> function
          | `Fa_var_new j ->
              if IntMap.mem j r then
                raise (M.Stop "one new var => several sub-pars")
              else IntMap.add j (Sv_nextpar i) r
          | _ -> r
        ) IntMap.empty callnext.ii_args in
    (* Set predicates *)
    let set_predicates =
      let tr_formal_arith_arg = function
        | `Fa_this -> Se_this
        | `Fa_var_new i -> Se_field (idx_2off i)
        | _ -> raise (M.Stop "tr_formal_arith_arg: not translateable") in
      let tr_formal_set_arg = function
        | `Fa_var_new i ->
            IntMap.find_comp (fun ( ) -> raise (M.Stop "`Fa_var_new"))
              i subcall_pars
        | `Fa_par_set i -> Sv_actual i in
      let tr_sexpr = function
        | Se_var sv -> Sd_var (tr_formal_set_arg sv)
        | Se_uplus (set, elt) ->
            Sd_uplus (tr_formal_arith_arg elt, tr_formal_set_arg set) in
      let tr_sform = function
        | Sf_mem (elt, set) ->
            Se_mem (tr_formal_arith_arg elt, Sd_var (tr_formal_set_arg set))
        | Sf_equal (set, sexpr) ->
            Se_eq (tr_formal_set_arg set, tr_sexpr sexpr)
        | _ -> raise (M.Stop "tr_sform: not translateable") in
      List.fold_left
        (fun acc -> function
          | Pf_alloc _ | Pf_arith _ -> acc
          | Pf_set sf -> tr_sform sf :: acc
        ) [ ] r.ir_pure in
    (* Equalities induced by parameter definitions *)
    let set_predicates =
      let add_call_par f icall acc =
        List.fold_lefti
          (fun ipar acc -> function
            | `Fa_var_new _ -> acc
            | `Fa_par_set i -> Se_eq (Sv_actual i, Sd_var (f ipar)) :: acc
          ) acc icall in
      List.fold_lefti
        (fun j acc icall -> add_call_par (fun k -> Sv_subpar (j, k)) icall acc)
        (add_call_par (fun j -> Sv_nextpar j) callnext.ii_args set_predicates)
        nest_call_setpars in
    (* Set parameters *)
    let set_pars =
      let l = IntMap.fold (fun i p a -> (i, p) :: a) ind.i_pkind.pr_set [] in
      let l = List.sort (fun (i0,_) (i1,_) -> i0 - i1) l in
      List.map snd l in
    (* Set component of the definition *)
    let setpr =
      let ufseg =
        List.fold_lefti (fun i acc k -> if k.st_head then Some i else acc)
          None set_pars in
      match set_predicates, set_pars with
      | [ ], [ ] -> None
      | _, _ -> Some { s_params = set_pars;
                       s_uf_seg = ufseg;
                       s_equas  = set_predicates } in
    (* Searching for the size *)
    let size =
      let acc =
        List.fold_left
          (fun acc -> function
            | Pf_alloc s ->
                if acc != None then raise (M.Stop "two sizes"); Some s
            | _ -> acc
          ) None r.ir_pure in
      match acc with
      | None -> raise (M.Stop "no size")
      | Some s -> s in
    (* Produce result *)
    { ld_name    = Some ind.i_name;
      ld_nextoff = onext;
      ld_size    = size;
      ld_onexts  = nest_calls;
      ld_set     = setpr } in
  Log.info "searching list defs\n";
  (* Construction of the dependence graph of inductive definitions *)
  let depgraph =
    StringMap.fold
      (fun name ind acc ->
        List.fold_left
          (fun acc rule ->
            List.fold_left
              (fun acc -> function
                | Hacell _ -> acc
                | Haind ic -> StringGraph.edge_add name ic.ii_ind acc
              ) acc rule.ir_heap
          ) acc ind.i_rules
      ) !Ind_utils.ind_defs StringGraph.empty in
  (* Topological sort; components with two elements or more should not
   *  be considered (the list domain does not handle cyclic definitions) *)
  let components =
    List.filter (fun s -> StringSet.cardinal s <= 1)
      (StringGraph.tarjan depgraph) in
  let ind_candidates =
    List.fold_left (fun acc s -> StringSet.min_elt s :: acc) [ ] components in
  (* Iteration over the inductive definitions candidate to conversion *)
  List.iter
    (fun name ->
      Log.info "looking at inductive definition %s" name;
      let ind =
        try StringMap.find name !Ind_utils.ind_defs
        with Not_found -> Log.fatal_exn "ind def %s not found" name in
      if ind.i_mt_rule && List.length ind.i_rules = 2 then
        let rule =
          match ind.i_rules with
          | [ r0 ; r1 ] ->
              if r0.ir_kind = Ik_empz then r1
              else if r1.ir_kind = Ik_empz then r0
              else Log.fatal_exn "contradicting rules structure"
          | _ -> Log.fatal_exn "contradicting number of rules" in
        try
          let lc = aux_rule name ind rule in
          Log.info "\nDefinition %s converted into:\n%s\n" name
            (l_def_2stri "    " lc);
          list_ind_defs := StringMap.add name lc !list_ind_defs
        with
        | M.Stop s -> Log.info "%s not a list like ind def (%s)\n" name s
      else Log.info "%s not list like ind def (rule #)" name
    ) ind_candidates
