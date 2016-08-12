(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_join.ml
 **       Join for the list domain
 ** Xavier Rival, 2014/03/04 *)
open Data_structures
open Lib

open Graph_sig (* for graph relation *)
open Ind_sig
open Inst_sig
open List_sig
open Nd_sig
open Set_sig
open Sv_sig

open Gen_join

open Ind_utils
open Inst_utils
open List_utils
open Set_utils

(** Improvements to consider:
 *  - move out do_setconses;
 *  - share code between it and the prune function in set_utils *)

(** Error report *)
module Log =
    Logger.Make(struct let section = "l_join__" and level = Log_level.DEBUG end)

let debug_module = false

(** Aborting a rule *)
exception Abort_rule of string

(** Join algorithm state *)
type join_config =
    { (** Iteration strategy *)
      (* Rules that could be applied right away *)
      j_rules:      rules;
      (** Arguments *)
      (* Arguments (left and right) *)
      j_inl:        lmem;
      j_inr:        lmem;
      (* Satisfaction of (value|set) predicates for (left|right) argument *)
      j_satl:       (n_cons -> bool);
      j_setsatl:    (set_cons -> bool);
      j_satr:       (n_cons -> bool);
      j_setsatr:    (set_cons -> bool);
      (** Relations among arguments *)
      (* Relation between arguments/output nodes *)
      j_rel:        node_relation;
      (* Hint: nodes that should be treated in priority *)
      j_hint:       (int * int -> bool);
      (* instantiation constraints, following from is_le facts *)
      j_instset_l:  setv_inst;
      j_instset_r:  setv_inst;
      (** Outputs *)
      j_out:        lmem; (* join result *)
    }

(** Instantiation obtained from a pair of calls
 *   (maintains the set parameters associated to the call) *)
let l_call_inst
    (lc_i: l_call) (* call from the join input *)
    (lc_o: l_call) (* call from the join output being constructed *)
    (inst: setv_inst) (* instantiation being constructed *)
    : setv_inst =
  assert (List.length lc_i.lc_args = List.length lc_o.lc_args);
  List.fold_left2
    (fun acc ii io ->
      setv_inst_bind io (S_var ii) (Inst_utils.add_setv io acc)
    ) inst lc_i.lc_args lc_o.lc_args
let l_call_add
    (lc: l_call)
    (inst: setv_inst)
    : setv_inst =
  List.fold_left (fun acc io -> Inst_utils.add_setv io acc) inst lc.lc_args
let l_call_rem
    (lc: l_call)
    (inst: setv_inst)
    : setv_inst =
  List.fold_left (fun acc io -> Inst_utils.rem_setv io acc) inst lc.lc_args

(** Generation of set parameters to build an inductive predicate *)
let build_set_args (ld: l_def) (lm: lmem): lmem * l_call =
  match ld.ld_set with
  | None -> lm, { lc_def = ld ; lc_args = [ ] }
  | Some si ->
      let lm, largs =
        List.fold_left
          (fun (lm, args) k ->
            let i, lm = setv_add_fresh false (Some k) lm in
            lm, i :: args
          ) (lm, [ ]) (List.rev si.s_params) in
      lm, { lc_def = ld ; lc_args = largs }

(** Operations on configurations and mappings *)
(* Searches for a pair (sv_l, sv_r) in the configuration; adds it if needed *)
let find_in_config (p: int * int) (j: join_config): join_config * int =
  try j, Graph_utils.Nrel.find j.j_rel p
  with Not_found ->
    let nl = sv_find (fst p) j.j_inl in
    let nr = sv_find (snd p) j.j_inr in
    let t  = ntyp_merge nl.ln_typ nr.ln_typ in
    let ni, nout = sv_add_fresh t j.j_out in
    let ln_odesc =
      match nl.ln_odesc, nr.ln_odesc with
      | None  , None   -> None
      | None  , Some _ -> nr.ln_odesc
      | Some _, None   -> nl.ln_odesc
      | Some l, Some r ->
          if l = r then Some l
          else Log.fatal_exn "find_in_config: ln_odesc not match" in
    let nout = 
      let no = sv_find ni nout in
      { nout with
        lm_mem = IntMap.add ni { no with ln_odesc = ln_odesc } nout.lm_mem } in
    let nrel = Graph_utils.Nrel.add j.j_rel p ni in
    { j with
      j_out = nout;
      j_rel = nrel; }, ni

(** Management of applicable rules *)
(* General function *)
let collect_rules_node_gen
    (is_prio: int * int -> bool) (* whether pt rules are prioritary (init) *)
    (il: int) (ir: int) (* nodes in both inputs *)
    (jc: join_config): join_config =
  let jr =
    collect_rules_sv_gen is_prio false false jc.j_rel
      il (sv_kind il jc.j_inl) ir (sv_kind ir jc.j_inr) jc.j_rules in
  { jc with j_rules = jr }
(* Node collection at some point in the algorithm *)
let collect_rules_node (il: int) (ir: int) (jc: join_config)
    : join_config =
  collect_rules_node_gen (fun _ -> false) il ir jc
(* Computes the set of rules at initialization *)
let init_rules (jc: join_config): join_config =
  PairMap.fold
    (fun (il, ir) _ ->
      collect_rules_node_gen jc.j_hint il ir
    ) jc.j_rel.n_inj jc

(** Unification functions *)
(* We keep the format of the unification functions, to avoid too much
 * divergence from graph_join, but these should be a lot simpler here
 * as all offsets, bounds and sizes are supposed to be constant. *)
let gen_unify (f_is_const: 'a -> bool) (f_eq: 'a -> 'a -> bool)
    (bl: 'a) (br: 'a) (j: join_config): join_config * 'a =
  assert (f_is_const bl && f_is_const br);
  if f_eq bl br then j, bl else raise Stop
let unify_bounds bl br j = gen_unify Bounds.t_is_const Bounds.eq bl br j
let unify_offsets bl br j = gen_unify Offs.t_is_const Offs.eq bl br j
let unify_sizes bl br j = gen_unify Offs.size_is_const Offs.size_eq bl br j

(** Interface over inclusion checking *)
(* For full inductive predicates *)
let n_is_le_ind
    (ld: l_def)                 (* definition to be used *)
    (x: lmem)                   (* shape to compare and weaken *)
    (is: int)                   (* source *)
    (sat: n_cons -> bool)       (* constraint verification *)
    (setsat: set_cons -> bool)  (* set constraint verification *)
    : is_le_weaken_check * l_call =
  let xw = sv_add is Ntaddr lmem_empty in
  let xw = { xw with
             lm_nkey    = x.lm_nkey ;
             lm_setvkey = x.lm_setvkey } in
  let xw, lc = build_set_args ld xw in
  let xw = list_edge_add is lc xw in
  let inj = Aa_maps.singleton is is in
  let r =
    List_is_le.is_le_weaken_check x IntSet.empty sat setsat xw inj
      Aa_maps.empty in
  r, lc
(* For segment predicates *)
let n_is_le_lseg
    (ld: l_def)                 (* definition to be used *)
    (x: lmem)                   (* shape to compare and weaken *)
    (is: int) (id: int)         (* source and destination *)
    (sat: n_cons -> bool)       (* constraint verification *)
    (setsat: set_cons -> bool)  (* set constraint verification *)
    : is_le_weaken_check * l_call =
  let xw = sv_add is Ntaddr (sv_add id Ntaddr lmem_empty) in
  let xw = { xw with
             lm_nkey    = x.lm_nkey ;
             lm_setvkey = x.lm_setvkey } in
  let xw, lc = build_set_args ld xw in
  let xw = lseg_edge_add is id lc xw in
  let inj = Aa_maps.add id id (Aa_maps.singleton is is) in
  let r =
    List_is_le.is_le_weaken_check x IntSet.empty sat setsat xw inj
      Aa_maps.empty in
  r, lc

(** Auxilliary functions supporting graph rewrites *)
(* seperate an inductive into a segment and an inductive edge in the out *)
let sep_ind_out (is: int) (id: int) (j: join_config): join_config =
  let n_is = sv_find is j.j_out in
  let n_id = sv_find id j.j_out in
  let aux lc lm =
    let lm, lseg, lind, scons = split_indpredpars lc lm in
    let fix inst =
      let i = l_call_rem lc (l_call_add lseg (l_call_add lind inst)) in
      { i with setvi_props = scons @ i.setvi_props } in
    { j with
      j_out       = lseg_edge_add is id lseg lm;
      j_instset_l = fix j.j_instset_l;
      j_instset_r = fix j.j_instset_r; }, lind in
  match n_is.ln_e, n_id.ln_e with
  | Lhlist lc, Lhemp ->
      let j, lind = aux lc (list_edge_rem is j.j_out) in
      { j with j_out = list_edge_add id lind j.j_out }
  | Lhlseg (lc, d), Lhemp ->
      let j, lind = aux lc (lseg_edge_rem is j.j_out) in
      { j with j_out = lseg_edge_add id d lind j.j_out }
  | _ -> j

(** Instantiation heuristics *)
(* Try to guess some instantiation constraints for const set parameters
 * when a segment or an inductive edge is introduced, using an edge nearby
 * (other segment or full inductive predicate with the same inductive kind) *)
(* [XR]: check this instantiation scheme later *)
let l_call_const_inst (is: int) (lc: l_call) (lm: lmem) (inst_set: setv_inst)
  : setv_inst =   
  let args =
    match lc.lc_def.ld_set with
    | None -> [ ]
    | Some e -> e.s_params in
  try
    let lnode = IntMap.find_err "l_call_const_inst" is lm.lm_mem in
    let lc_extract =
      match lnode.ln_e with
      | Lhlist l_c -> l_c
      | Lhlseg (l_c, nid) -> l_c
      | Lhemp | Lhpt _ -> raise Not_found in
    assert (l_call_compare lc lc_extract = 0);
    let _, _, inst_set =
      List.fold_left
        (fun (lc_args, lc_ex_args, inst_set) par_kind ->
          let inst_set =
            if par_kind.st_add || par_kind.st_head then inst_set
            else if par_kind.st_const then
              let l, r = List.hd lc_args, List.hd lc_ex_args in
              let inst_set =
                if IntSet.mem l inst_set.setvi_none && 
                  IntMap.mem r inst_set.setvi_eqs then
                  let c =
                    IntMap.find_err "eq_const:over" r inst_set.setvi_eqs in
                  Log.warn "zorb,eq_const: over_bind: %d, %d" l r;
                  setv_inst_over_bind l c inst_set
                else inst_set in
              inst_set
            else Log.todo_exn "unhandled kind-1" in
          List.tl lc_args, List.tl lc_ex_args, inst_set          
        ) (lc.lc_args, lc_extract.lc_args, inst_set) args in
    inst_set
  with Not_found ->
    inst_set
(* Apply l_const_inst exhaustively to compute as many instantiation constraints,
 * as post-analysis step *)
let full_const_inst (lm: lmem) (inst_set: setv_inst): setv_inst = 
  IntMap.fold
    (fun key ele acc ->
      match ele.ln_e with
      | Lhlseg (lc, eid) -> l_call_const_inst eid lc lm acc
      | Lhpt _ | Lhemp | Lhlist _  -> acc 
    ) lm.lm_mem inst_set

(** Approximate candidate selection:
 *   - tries to find information in the nearby inductive predicates
 *   - if none is available, tries to guess a set of solutions from pt fields;
 *   - fails for empty
 *  Limitation: will not generate any set constraint at this point
 *  (doing so would require guessing conditions, which is not easy at this
 *   stage; this problem would occur in the case of the construction of
 *   structures) *)
let select_list_candidate (i: int) (lm: List_sig.lmem): l_call list =
  let nl = sv_find i lm in
  let do_ld ld = [ { lc_def  = ld;
                     lc_args = [] } ] in
  match nl.ln_odesc with
  | Some ld -> do_ld ld
  | None ->
      match nl.ln_e with
      | Lhlist lc -> do_ld lc.lc_def
      | Lhlseg (lc, _) -> do_ld lc.lc_def
      | Lhpt mc ->
          let lc_of_i i = { ld_name    = None;
                            ld_nextoff = i;
                            ld_size    =  Block_frag.byte_size mc;
                            ld_onexts  = [ ];
                            ld_set     = None; } in
          let ld_of_i i = { lc_def  = lc_of_i i;
                            lc_args = [ ] } in
          let l1 = List.map fst (Block_frag.map_to_list mc) in
          let loffs = List.map (fun b -> Offs.to_int (Bounds.to_offs b)) l1 in
          List.map ld_of_i loffs
      | Lhemp ->
          [ ] (* no solution *)
   
(** Join rules *)
(* pt-pt *)
let apply_pt_pt
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let nl = sv_find isl j.j_inl in
  let nr = sv_find isr j.j_inr in
  assert (nl.ln_odesc = nr.ln_odesc);
  match nl.ln_e, nr.ln_e with
  | Lhpt mcl, Lhpt mcr ->
      let sz_l = Block_frag.cardinal mcl and sz_r = Block_frag.cardinal mcr in
      let j =
        if sz_l != sz_r then Log.todo_exn "pt-pt; !="
        else
          Block_frag.fold_list2_base
            (fun osl osr (pl: pt_edge) (pr: pt_edge) j ->
              let j, u_os = unify_bounds osl osr j in
              let j, u_size = unify_sizes pl.pe_size pr.pe_size j in
              let dl_n, dl_o = pl.pe_dest
              and dr_n, dr_o = pr.pe_dest in
              let j, dd_o = unify_offsets dl_o dr_o j in
              let j, id = find_in_config (dl_n, dr_n) j in
              let pe = { pe_size = u_size ;
                         pe_dest = id, dd_o } in
              collect_rules_node dl_n dr_n
                { j with
                  j_out = pt_edge_block_append (is, u_os) pe j.j_out }
            ) mcl mcr j in
      let vrules = invalidate_rules isl isr Ipt Ipt j.j_rules in
      { j with
        j_inl   = pt_edge_block_destroy ~remrc:true isl j.j_inl;
        j_inr   = pt_edge_block_destroy ~remrc:true isr j.j_inr;
        j_rules = vrules; }
  | _, _ -> Log.fatal_exn "pt-pt: improper case"

(* ind-ind [par ptr OK, par int OK]
 *   consume edges and produce a matching one *)
let apply_ind_ind
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let nl = sv_find isl j.j_inl in
  let nr = sv_find isr j.j_inr in
  match nl.ln_e, nr.ln_e with
  | Lhlist ldl, Lhlist ldr ->
      if l_call_compare ldl ldr = 0 then
        let out, ldo = build_set_args ldl.lc_def j.j_out in
        let vrules = invalidate_rules isl isr Iind Iind j.j_rules in
        { j with
          j_rules     = vrules;
          j_inl       = list_edge_rem isl j.j_inl;
          j_inr       = list_edge_rem isr j.j_inr;
          j_out       = list_edge_add is ldo out;
          j_instset_l = l_call_inst ldl ldo j.j_instset_l;
          j_instset_r = l_call_inst ldr ldo j.j_instset_r;
        }
      else Log.fatal_exn "join: inductive edges fails"
  | _, _ -> Log.fatal_exn "ind-ind: improper case"

(* ind-weak: weakening the right side to match an inductive in the left side
 * weak-ind: weakening the left side to match an inductive in the right side *)
let apply_gen_ind_weak
    (side: side) (* side of the rule (side being weakened) *)
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  (* "s": side argument used as a guide
   * "o": other argument being weakened *)
  let rname = Graph_algos.sel_side side ("ind-weak", "weak-ind") in
  let iso, iss = Graph_algos.get_sides side (isl, isr) in
  let ino, ins = Graph_algos.get_sides side (j.j_inl, j.j_inr) in
  (* r -> side; l -> other side *)
  let ns = sv_find iss ins in
  match ns.ln_e with
  | Lhlist lds ->
      let out, lcout = build_set_args lds.lc_def j.j_out in
      let sato, sats = Graph_algos.get_sides side (j.j_satl, j.j_satr) in
      let setsato, setsats =
        Graph_algos.get_sides side (j.j_setsatl, j.j_setsatr) in
      let insto, _ = Graph_algos.get_sides side (j.j_instset_l, j.j_instset_r) in
      let le_res, lcwk = n_is_le_ind lds.lc_def ino iso sato setsato in
      begin
        match le_res with
        | `Ilr_le_rem (grem, removed, rel, srel, setcons) ->
            (* the rule succeeds; perform the weakening *)
            let cons_o =
              List_inst.do_setconses
                (setv_type ino) lcwk lcout rel srel setcons insto in
            let j =
              match side with
              | Lft ->
                  let vrules =
                    invalidate_rules isl isr (Iblob (IntSet.singleton isl))
                      (Iblob removed) j.j_rules in
                  { j with
                    j_rules     = vrules;
                    j_inl       = list_edge_rem isl j.j_inl;
                    j_inr       = grem;
                    j_instset_l = l_call_inst lds lcout j.j_instset_l;
                    j_instset_r = cons_o; }
              | Rgh ->
                  let vrules =
                    invalidate_rules isl isr (Iblob removed)
                      (Iblob (IntSet.singleton isr)) j.j_rules in
                  { j with
                    j_rules     = vrules;
                    j_inl       = grem;
                    j_inr       = list_edge_rem isr j.j_inr;
                    j_instset_l = cons_o;
                    j_instset_r = l_call_inst lds lcout j.j_instset_r; } in
            { j with j_out       = list_edge_add is lcout out; }
        | `Ilr_not_le -> (* rule application failed *)
            if Flags.flag_join_bypass_fail_rules then j (* Rule by-pass *)
            else Log.fatal_exn "%s: fails" rname
      end
  | _ -> j
let apply_weak_ind is isl isr j = apply_gen_ind_weak Rgh is isl isr j
let apply_ind_weak is isl isr j = apply_gen_ind_weak Lft is isl isr j

(* seg-intro *)
let apply_gen_seg_intro
    (side: side) (* side of the rule, i.e., where the empty chunk is found *)
    (is: int)  (* source SV in the target graph *)
    (isl: int) (* source SV in the left graph *)
    (isr: int) (* source SV in the right graph *)
    (j: join_config): join_config =
  (* "s": empty segment introduced
   * "o": weakens a chunk of a graph into a segment *)
  let rname    = Graph_algos.sel_side side ("seg-intro-l", "seg-intro-r") in
  let iso, iss = Graph_algos.get_sides side (isl, isr) in
  let cho, chs = Graph_algos.get_sides side ('l', 'r') in
  let ino, ins = Graph_algos.get_sides side (j.j_inl, j.j_inr) in
  let sato, sats = Graph_algos.get_sides side (j.j_satl, j.j_satr) in
  let setsato, setsats =
    Graph_algos.get_sides side (j.j_setsatl, j.j_setsatr) in
  (* rule abortion procedure *)
  let rule_abort (j: join_config): join_config =
    match side with (* add facility to split rules *)
    | Lft -> { j with j_rules = rules_add_splitind_l (isl, isr) j.j_rules }
    | Rgh -> { j with j_rules = rules_add_splitind_r (isl, isr) j.j_rules } in
  (* extract other siblings *)
  let allsibl = Graph_algos.sel_side side (j.j_rel.n_l2r, j.j_rel.n_r2l) in
  let siblings = IntMap.find_err "siblings incons, seg_intro" iss allsibl in
  assert (IntSet.mem iso siblings);
  let siblings = IntSet.remove iso siblings in
  (* destination node in the other side *)
  let ido =
    let card = IntSet.cardinal siblings in
    if card = 0 then Log.fatal_exn "no sibling";
    let n = IntSet.min_elt siblings in
    if card > 1 then
      Log.warn "%s found too many siblings: %s ; picking %d\n"
        rname (intset_2str siblings) n;
    n in
  if !Flags.flag_debug_join_list then
    Log.force "%s attempt: S%c:%d -> (S%c:%d,D%c:%d)" rname
      chs iss cho iso cho ido;
  (* destination node in the result *)
  let id =
    let pd = Graph_algos.get_sides side (ido, iss) in
    PairMap.find_err "seg_intro:pair" pd j.j_rel.n_inj in
  let lds = select_list_candidate iss ins in
  (* tries to apply the rule using a given list description *)
  let do_ld ld =
    if !Flags.flag_debug_join_list then
      Log.force "%s_inductive_definition: %s" rname
        (match ld.lc_def.ld_name with None -> "list" | Some s -> s);
    let out, lcout = build_set_args ld.lc_def j.j_out in
    (* check the segment inclusion for the "other" side *)
    let insto, _ = Graph_algos.get_sides side (j.j_instset_l, j.j_instset_r) in
    let le_res_o, lcwk = n_is_le_lseg ld.lc_def ino iso ido sato setsato in
    (* for the other side, we generate a segment edge, and set the additive
     * set parameters to empty, this keeps the soundness (sinfo def. below) *)
    match le_res_o with
    | `Ilr_le_rem (lm_remaino, sv_delo, injo, sinjo, setcons) ->
        let vrules =
          match side with
          | Lft ->
              invalidate_rules isl isr Isiblings Inone
                (invalidate_rules isl ido Inone (Iblob sv_delo) j.j_rules)
          | Rgh ->
              invalidate_rules isl isr Inone Isiblings
                (invalidate_rules ido isr (Iblob sv_delo) Inone j.j_rules) in
        let cons_o =
          List_inst.do_setconses
            (setv_type ino) lcwk lcout injo sinjo setcons insto in
        let j =
          match side with
          | Lft ->
              { j with
                j_inr        = lm_remaino;
                j_instset_r  = cons_o;
                j_instset_l  = List_inst.l_call_empty lcout j.j_instset_l }
          | Rgh ->
              { j with
                j_inl        = lm_remaino;
                j_instset_l  = cons_o;
                j_instset_r  = List_inst.l_call_empty lcout j.j_instset_r } in
        let fi = l_call_const_inst id lcout j.j_out in (* guess inst neighb. *)
        { j with
          j_rules = vrules;
          j_out   = lseg_edge_add is id lcout out;
          j_instset_r  = fi j.j_instset_r;
          j_instset_l  = fi j.j_instset_l; }
    | _ -> rule_abort j in
  let rec do_lds = function
    | [ ] -> rule_abort j
    | ld :: lds -> let jj = do_ld ld in if j == jj then do_lds lds else jj in
  do_lds lds
let apply_seg_intro_l is isl isr j = apply_gen_seg_intro Lft is isl isr j
let apply_seg_intro_r is isl isr j = apply_gen_seg_intro Rgh is isl isr j

(* seg-ext *)
let apply_seg_ext
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let nl = sv_find isl j.j_inl in
  match nl.ln_e with
  | Lhlseg (ldl, idl) ->
      (* extract a "tentative" destination in the right side *)
      let idr, guessed =
        let s = IntMap.find_val IntSet.empty idl j.j_rel.n_l2r in
        if !Flags.flag_debug_join_shape then
          Log.force "set found: %s" (intset_2str s);
        let card = IntSet.cardinal s in
        if card = 1 then IntSet.min_elt s, false
        else
          (* Backup solution:
           * - if card > 1,
           *    see if there is a segment in the right side, and if so
           *    look if its destination works as well
           * - if card = 0,
           *    see if there is a segment in the right side and use it... *)
          let nr = sv_find isr j.j_inr in
          match nr.ln_e with
          | Lhlseg (ldr, idr) ->
              if IntSet.mem idr s then idr, false
              else if card = 0 then
                begin (* no other solution anyway *)
                  Log.warn
                    "seg-ext takes next segment (not sure about end-point)";
                  idr, true
                end
              else Log.fatal_exn "seg-ext backup failed (seg)"
          | _ -> Log.fatal_exn "seg-ext backup failed (other)" in
      begin
        let out, lcout = build_set_args ldl.lc_def j.j_out in
        let j, id = find_in_config (idl, idr) { j with j_out = out } in
        let is_le, lcwk =
          n_is_le_lseg ldl.lc_def j.j_inr isr idr j.j_satr j.j_setsatr in
        match is_le with
        | `Ilr_le_rem (lm_remain, sv_del, inj, sinj, setcons) ->
            let cons_r =
              List_inst.do_setconses
                (setv_type j.j_inr) lcwk lcout inj sinj setcons j.j_instset_r in
            let j =
              if guessed then collect_rules_node idl idr j
              else j in
            let vrules =
              invalidate_rules isl isr
                (Iblob (IntSet.singleton isl)) (Iblob sv_del) j.j_rules in
            let fi = l_call_const_inst id lcout j.j_out in (* guess inst *)
            { j with
              j_rules      = vrules;
              j_inl        = lseg_edge_rem isl j.j_inl;
              j_inr        = lm_remain;
              j_out        = lseg_edge_add is id lcout j.j_out;
              j_instset_l  = fi (l_call_inst ldl lcout j.j_instset_l);
              j_instset_r  = fi cons_r; }
        | `Ilr_not_le ->
            let np_r =
              match lcout.lc_def.ld_set with
              | None ->
                  Log.fatal_exn "seg_ext fails"
              | Some set_r ->
                  begin 
                    match set_r.s_uf_seg  with 
                    | None -> Log.fatal_exn "seg_ext fails"
                    | Some uf ->
                        try
                          List.nth lcout.lc_args uf
                        with 
                        | _ -> Log.fatal_exn "seg_ext: uf_find"
                  end in
            (* if is_le_seg fails, we attempt to weaken chunks to segments in
             * both sides of the join, and to continue with remainders in both
             * sides; this means that we let inclusion check guess the end
             * point of segments *)
            let is_le_l, lcwkl =
              n_is_le_ind ldl.lc_def j.j_inl isl j.j_satl j.j_setsatl in
            let is_le_r, lcwkr =
              n_is_le_ind ldl.lc_def j.j_inr isr j.j_satr j.j_setsatr in
            begin
              match is_le_l, is_le_r with
              | (`Ilr_le_rem (lm_l, sv_del_l, inj_l, sinj_l, setcons_l),
                 `Ilr_le_rem (lm_r, sv_del_r, inj_r, sinj_r, setcons_r)
                ) ->
                  let cons_l =
                    List_inst.do_setconses
                      (setv_type j.j_inl) lcwkl lcout inj_l sinj_l
                      setcons_l j.j_instset_l in
                  let cons_r =
                    List_inst.do_setconses
                      (setv_type j.j_inr) lcwkr lcout inj_r sinj_r
                      setcons_r j.j_instset_r in
                  let vrules =
                    invalidate_rules isl isr (Iblob (IntSet.singleton isl))
                      (Iblob sv_del_r) j.j_rules in
                  let fi = l_call_const_inst id lcout j.j_out in (* guess inst *)
                  let j =
                    { j with
                      j_rules     = vrules;
                      j_inl       = lm_l;
                      j_inr       = lm_r;
                      j_out       = list_edge_add is lcout out;
                      j_instset_l = fi cons_l;
                      j_instset_r = fi cons_r; } in 
                  let j =
                    (* [XR]: should this be done only with some specific
                     *       parameter kinds or set relations ?
                     *  (I fear a loss of precision otherwise) *)
                    let c0 = Nc_cons (Apron.Tcons1.EQ, Ne_csti 0, Ne_var idr) in
                    if j.j_satr c0 then j
                    else
                      let cmem = S_mem (idr, S_var np_r) in
                      let instr =
                        { j.j_instset_r with
                          setvi_prove = cmem :: j.j_instset_r.setvi_prove } in
                      { j with j_instset_r = instr } in
                  sep_ind_out is id j
              | _ -> Log.fatal_exn "seg_ext fails"
            end
      end
  | _ -> (* we may check the rule was not invalidated ? *)
      Log.fatal_exn "seg-ext: improper case"

(* list-intro *)
let apply_list_intro
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let nl = sv_find isl j.j_inl in
  let nr = sv_find isr j.j_inr in
  match nl.ln_e, nr.ln_e with
  | Lhemp, Lhpt mcr ->
      (* 1. search for candidate inductive definitions *)
      let lds = select_list_candidate isr j.j_inr in
      (* 2. verify that inclusion holds in both sides *)
      let do_ld ld =
        if !Flags.flag_debug_join_list then
          Log.force "list-intro_inductive_definition: %s"
            (Option.get_default "list" ld.lc_def.ld_name);
        let out, lcout = build_set_args ld.lc_def j.j_out in
        let le_res_r, lcwk_r =
          n_is_le_ind ld.lc_def j.j_inr isr j.j_satr j.j_setsatr in
        let le_res_l, lcwk_l =
          n_is_le_ind ld.lc_def j.j_inl isl j.j_satl j.j_setsatl in
        match le_res_r,  le_res_l with
        | ((`Ilr_le_rem (grem_r, removed_r, rel_r, srel_r, setcons_r),
            `Ilr_le_rem (grem_l, removed_l, rel_l, srel_l, setcons_l))
          ) ->
            let cons_l =
              List_inst.do_setconses (setv_type j.j_inl) lcwk_l lcout
                rel_l srel_l setcons_l j.j_instset_l in
            let cons_r =
              List_inst.do_setconses (setv_type j.j_inl) lcwk_r lcout
                rel_r srel_r setcons_r j.j_instset_r in
            let vrules =
              invalidate_rules isl isr
                (Iblob (IntSet.singleton isl)) (Iblob removed_r) j.j_rules in
            { j with
              j_rules      = vrules;
              j_inr        = grem_r;
              j_inl        = grem_l;
              j_out        = list_edge_add is lcout out;
              j_instset_l  = cons_l;
              j_instset_r  = cons_r; }
        | _ ->
            Log.warn "list-intro: verification of inclusion failed\n";
            j in
      let rec do_lds = function
        | [ ] -> j
        | ind :: inds ->
            let jj = do_ld ind in if j == jj then do_lds inds else jj in
      do_lds lds
  | Lhemp, Lhemp ->
      j (* another rule was applied before, we can abort that one *)
  | _, _ ->
      Log.fatal_exn "indintro: improper case"

(* seperate inductive edge into a segment and an inductive edge *)
let apply_gen_sep_ind (side: side) (is: int) (isl: int) (isr: int)
    (j: join_config): join_config =
  (* [XR]: while reading this rule again, I cannot understand it well
   *  - what are the roles of "s" (side) and "o" (other side) ?
   *  - inl, and inr are not modified;
   *  - but the satisfaction function "sato" is called...
   *)
  (* side resolution:
   *  - "l" -> "s"
   *  - "r" -> "o" *)
  Log.info "Strange rule called";
  let iso, iss = Graph_algos.get_sides side (isl, isr) in
  let cho, chs = Graph_algos.get_sides side ('l', 'r') in
  let sato, sats = Graph_algos.get_sides side (j.j_satl, j.j_satr) in
  (* extract other siblings *)
  let allsibl = Graph_algos.sel_side side (j.j_rel.n_l2r, j.j_rel.n_r2l) in
  let siblings =
    IntMap.find_err "siblings inconsistency in sep_ind" iss allsibl in
  assert (IntSet.mem iso siblings);
  let siblings = IntSet.remove iso siblings in
  (* destination node in the other side *)
  let ido =
    let card = IntSet.cardinal siblings in
    if card = 0 then Log.fatal_exn "no sibling";
    let n = IntSet.min_elt siblings in
    if card > 1 then
      Log.info "sep-ind found too many siblings: %s ; picking %d"
        (intset_2str siblings) n;
    n in
  if !Flags.flag_debug_join_list then
    Log.force "sep-ind attempt: S%c:%d -> (S%c:%d,D%c:%d)"
      chs iss cho iso cho ido;
  (* destination node in the result *)
  let id =
    let pd = Graph_algos.get_sides side (ido, iss) in
    PairMap.find_err "sep_ind:pair" pd j.j_rel.n_inj in
  let nl_id, nl_is = sv_find id j.j_out, sv_find is j.j_out in
  match nl_id.ln_e, nl_is.ln_e with
  | Lhemp, Lhlist l_call ->
      (* having inductive edge from source node *)
      begin
        match l_call.lc_def.ld_set with
        | None -> j
        | Some set ->
            match set.s_uf_seg with
            | None -> j
            | Some n ->
                try
                  let np = List.nth l_call.lc_args n in
                  let c = Nc_cons (Apron.Tcons1.EQ, Ne_csti 0, Ne_var ido) in
                  if sato c then
                    (* [XR]: I do not understand this case *)
                    sep_ind_out is id j
                  else
                    let f inst =
                      let inst =
                        match side with
                        | Lft -> j.j_instset_r
                        | Rgh -> j.j_instset_l in
                      try
                        let c = S_mem (ido, IntMap.find np inst.setvi_eqs) in
                        { inst with setvi_prove = c :: inst.setvi_prove }
                      with
                      | Not_found -> inst in
                    let j =
                      match side with
                      | Lft -> { j with j_instset_r = f j.j_instset_r }
                      | Rgh -> { j with j_instset_l = f j.j_instset_l } in
                    (* [XR]: I think there is an issue with using "guard" here;
                     * it should be sat instead *)
                    (*let j =
                      match side with
                      | Lft ->
                      { j with
                      j_sout_r = j.j_set_guard
                      (S_mem (ido, S_var np)) j.j_sout_r; }
                      | Rgh ->
                      { j with
                      j_sout_l = j.j_set_guard
                      (S_mem (ido, S_var np)) j.j_sout_l; } in*)
                    sep_ind_out is id j
                with Invalid_argument _ ->
                  Log.fatal_exn "gen_sep_ind: parameter does not match in ind"
      end
  | _, _ -> j

let apply_sep_ind_l is isl isr j = apply_gen_sep_ind Lft is isl isr j
let apply_sep_ind_r is isl isr j = apply_gen_sep_ind Rgh is isl isr j

(** The recursive join function *)
let rec rec_join (jc: join_config): join_config =
  let ppi = lmem_2stri "  " in 
  (* Find the next rule to apply, and trigger it *)
  match rules_next jc.j_rules with
  | None -> (* there is no more rule to apply, so we return current config *)
      if !Flags.flag_debug_join_list then
        Log.force "no more rule applies;\n%s" (rules_2str jc.j_rules);
      jc
  | Some (k, (il, ir), rem_rules) ->
      if !Flags.flag_debug_join_list then
        begin
          Log.force
            "----------------\nJ-Situation:\n- L:\n%s- R:\n%s- O:\n%s- M:\n%s"
            (ppi jc.j_inl) (ppi jc.j_inr) (ppi jc.j_out)
            (Graph_utils.Nrel.nr_2stri "  " jc.j_rel);
          Log.force "- Set instantiation left:\n%s"
            (setv_inst_2stri "   " jc.j_instset_l);
          Log.force "- Set instantiation right:\n%s"
            (setv_inst_2stri "   " jc.j_instset_r);
          if !Flags.flag_debug_join_strategy then
            Log.force "%s----------------" (rules_2str jc.j_rules)
        end;
      let jc = { jc with j_rules = rem_rules } in
      let is = PairMap.find_err "rec_join:pair" (il, ir) jc.j_rel.n_inj in
      if !Flags.flag_debug_join_list then
        Log.force "join-Treating (%d,%d) (%s)\n" il ir (kind_2str k);
      let nj =
        try
          match k with
          | Rpp           -> apply_pt_pt       is il ir jc
          | Rii           -> apply_ind_ind     is il ir jc 
          | Rweaki        -> apply_weak_ind    is il ir jc
          | Riweak        -> apply_ind_weak    is il ir jc 
          | Rsegext       -> apply_seg_ext     is il ir jc 
          | Rsegintro Lft -> apply_seg_intro_l is il ir jc  
          | Rsegintro Rgh -> apply_seg_intro_r is il ir jc
          | Rindintro     -> apply_list_intro  is il ir jc
          | Rsplitind Lft -> apply_sep_ind_l   is il ir jc
          | Rsplitind Rgh -> apply_sep_ind_r   is il ir jc
          | Rsegext_ext   -> Log.todo_exn "Seg-ext rule"
        with
        | Abort_rule _ -> jc in
      rec_join nj
 
(** The main list join function *)
let join
    (xl: lmem)                (* left graph *)
    (satl: n_cons -> bool)    (* left sat function *)
    (setsatl: set_cons -> bool) (* left set sat function *)
    (xr: lmem)                (* right graph *)
    (satr: n_cons -> bool)    (* right sat function *) 
    (setsatr: set_cons -> bool) (* right set sat function *)
    (ho: hint_bg option)      (* optional hint *)
    (r: node_relation)        (* initial node relation *)
    (srel: node_relation)     (* initial set var relation *)
    (noprio: bool)            (* whether to NOT make roots prioretary *)
    (xo: lmem)                (* pre-constructed output *)
    : join_output =
  let h =
    match noprio, ho with
    | true, _ -> fun _ -> false
    | false, None -> fun _ -> true
    | false, Some s ->
        fun (i, j) ->
          try Aa_maps.find j s.hbg_live = i
          with Not_found -> false in
  let jc = init_rules { j_rules     = empty_rules;
                        j_inl       = xl;
                        j_satl      = satl;
                        j_setsatl   = setsatl;
                        j_inr       = xr;
                        j_satr      = satr;
                        j_setsatr   = setsatr;
                        j_rel       = r;
                        j_hint      = h;
                        j_instset_l = setv_inst_empty;
                        j_instset_r = setv_inst_empty;
                        j_out       = xo; } in
  let out = rec_join jc in
  let out = { out with
              j_instset_l = full_const_inst out.j_out out.j_instset_l;
              j_instset_r = full_const_inst out.j_out out.j_instset_r; } in
  (* Display, if verbose mode or if join not perfect *)
  let ind = "     " in
  let ppi = lmem_2stri ind in
  let nl = num_edges out.j_inl and nr = num_edges out.j_inr in
  if !Flags.flag_debug_join_shape || nl != 0 || nr != 0 then
    begin
      Log.force
        "\n\nFinal [%d,%d]:\n- Left shape:\n%s- Right shape:\n%s- Out:\n%s"
        nl nr (ppi out.j_inl) (ppi out.j_inr) (ppi out.j_out);
      Log.force "- Rel:\n%s" (Graph_utils.Nrel.nr_2stri ind out.j_rel);
      Log.force "- Inst-set-l:\n%s" (setv_inst_2stri "   " out.j_instset_l);
      Log.force "- Inst-set-r:\n%s" (setv_inst_2stri "   " out.j_instset_r);
    end;
  { out    = out.j_out;
    rel    = out.j_rel;
    instset_l = out.j_instset_l;
    instset_r = out.j_instset_r; }
