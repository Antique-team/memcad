(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_is_le.ml
 **       Inclusion checking for the list domain
 ** Xavier Rival, 2014/03/07 *)
open Data_structures
open Flags
open Lib

open Ind_sig
open List_sig
open Nd_sig
open Set_sig
open Sv_sig

open Gen_dom
open Gen_is_le

open List_utils
open Set_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "l_isle__" and level = Log_level.DEBUG end)

let debug_module = false

(** State of the inclusion checking algorithm *)
type le_state =
    { (** Arguments and mappings from right to left *)
      (* Arguments configurations *)
      ls_cur_l:     lmem ;
      ls_cur_r:     lmem ;
      (* Mapping from right SVs into left SVs *)
      ls_cur_i:     Graph_sig.node_embedding;
      (* Mapping from right SETVs into left SETVs *)
      ls_cur_si:    Set_sig.setv_embedding; 
      (** Iteration strategy *)
      (* Pending rules (given as pairs of node names) *)
      ls_rules:     rules ; (* instances of rules pending application *)
      (* Nodes that were removed in the left argument (helps join) *)
      ls_rem_l:     IntSet.t ;
      (** Underlying domain constraints *)
      (* Satisfiability *)
      ls_sat_l:     (n_cons -> bool) ;
      ls_setsat_l:  (set_cons -> bool) ;
      (* Accumulation of right constraints to translate and discharge in
       * the left at a later stage (needed to prove inclusion) *)
      ls_ctr_r:     n_cons list ;
      ls_setctr_r:  set_cons list ;
      (* Set-variables created by unfolding, during inclusion check *)
      ls_newsetv_r: IntSet.t;
      (** Termination of the inclusion checking *)
      (* Whether we need to empty both graphs or only the left graph *)
      ls_emp_both:  bool ;
      (* Whether a success configuration has been reached *)
      ls_success:   bool ;
      (** Hints *)
      (* Hint on the left argument: nodes not to split *)
      ls_stop_l:    int Aa_sets.t option ;
      (* Right remainder, excluded due to hint => left *)
      ls_excl_l:    l_call IntMap.t ;
      (* Optional "no empty unfold SVs", to inhibit unfold non empty *)
      ls_no_unf0:   IntSet.t ;
      (* Optional "end of segment SVs", to inhibit rules from these SVs *)
      ls_end_seg:   IntSet.t ; }
(* Pretty-printing of a configuration *)
let pp_le_state (ls: le_state): string =
  let config_sep: string = "------------------------------------------\n" in
  Printf.sprintf
    "%sLeft:\n%s\nRight:\n%sInjection:\n%sSet Inj:\n%s\n\nSet_cons:\n%s\n%s"
    config_sep (lmem_2stri " " ls.ls_cur_l) (lmem_2stri " " ls.ls_cur_r)
    (Graph_utils.Nemb.ne_full_2stri "  " ls.ls_cur_i)
    (Set_utils.Semb.ne_full_2stri "  " ls.ls_cur_si)
    (gen_list_2str "" Set_utils.set_cons_2str ";" ls.ls_setctr_r)
    config_sep

(** Utilities *)

(* Generate a fresh right node, to be mapped with some given node *)
let gen_map_id (nt: ntyp) (il: int) (ls: le_state): int * (le_state) =
  let ir, g = sv_add_fresh nt ls.ls_cur_r in
  ir, { ls with
        ls_cur_r = g ;
        ls_cur_i = Graph_utils.Nemb.add ir il ls.ls_cur_i }

(* Map the set arguments of right ind call into the set arguments of right
 * ind call, in the case where two edges are consumed in the same time:
 *  -> parameters are matched exactly *) 
let mapdir_ind_setpars (lcl: l_call) (lcr: l_call) (ls: le_state): le_state =
  assert (l_call_compare lcl lcr = 0);
  try
    List.fold_left2
      (fun ls r l ->
        { ls with
          ls_cur_si = Set_utils.Semb.add r l ls.ls_cur_si; }
      ) ls lcr.lc_args lcl.lc_args
  with Invalid_argument _ ->
    Log.fatal_exn "mapdir_ind_setpars: arguments not match"

(* Map the set arguments of right ind call into the set arguments of right
 * ind call, in the case where the right edge is split
 *  -> parameters are adjusted, depending on their properties *) 
let mapsplit_ind_setpars (lcl: l_call) (lcr: l_call) (ls: le_state)
    : le_state * l_call =
  assert (l_call_compare lcl lcr = 0);
  let params = 
    match lcl.lc_def.ld_set with
    | None -> []
    | Some si -> si.s_params in
  let ls, l =
    let rec aux ((ls, acc_call) as acc) lcl lcr params =
      match lcl, lcr, params with
      | [ ], [ ], [ ] -> acc
      | il :: lcl0, ir :: lcr0, k :: params0 ->
          (* generate two keys in the right for the split edges *)
          let ir0, lmr = (* map to il *)
            setv_add_fresh false (Some k) ls.ls_cur_r in
          let ir1, lmr = (* remaining par *)
            setv_add_fresh false (Some k) lmr in
          let setctr =
            if k.st_const then
              [ S_eq (S_var ir, S_var ir0) ; S_eq (S_var ir, S_var ir1) ]
            else if k.st_add || k.st_head then
              [ S_eq (S_var ir, S_uplus (S_var ir0, S_var ir1)) ]
            else Log.todo_exn "unhandled kind" in
          let acc =
            { ls with
              ls_cur_r    = lmr;
              ls_cur_si   = Set_utils.Semb.add ir0 il ls.ls_cur_si;
              ls_setctr_r = setctr @ ls.ls_setctr_r }, ir1 :: acc_call in
          aux acc lcl0 lcr0 params0
      | _, _, _ ->
          Log.fatal_exn "mapsplit_ind_setpars: pars of distinct lengths" in
    aux (ls, [ ]) lcl.lc_args lcr.lc_args params in
  ls, { lcl with lc_args = List.rev l }


(** Management of the set of applicable rules *)
(* Collecting applicable rules from a given SV *)
let collect_rules_node_gen =
  let sv_seg_ind i g =
    match (sv_find i g).ln_e with
    | Lhlseg (_, d) -> Some d
    | Lhemp | Lhpt _ | Lhlist _ -> None in
  collect_rules_sv_gen sv_kind sv_seg_ind
let collect_rules_node = collect_rules_node_gen false None
let collect_rules_node_st (il: int) (ir: int) (ls: le_state): le_state =
  let nr =
    collect_rules_node_gen false ls.ls_stop_l ls.ls_end_seg ls.ls_cur_i
      ls.ls_cur_l ls.ls_cur_r il ir ls.ls_rules in
  { ls with ls_rules = nr }
(* Initialization: makes prioretary points-to rules *)
let rules_init
    (prio: bool) (* whether available pt-edges should be treated in priority *)
    (es: IntSet.t) (* end of segment(s), if any *)
    (ni: Graph_sig.node_embedding)
    (xl: lmem) (xr: lmem) 
    (r: Graph_sig.node_emb)
    : rules =
  if !Flags.flag_debug_is_le_list then
    Log.force "isle init,l:\n%s\nisle init,-r:\n%s"
      (lmem_2stri "  " xl) (lmem_2stri "  " xr);
  let r =
    Aa_maps.fold
      (fun ir il acc ->
        if !Flags.flag_debug_is_le_list then
          Log.force "collecting at %d,%d" il ir;
        collect_rules_node_gen prio None es ni xl xr il ir acc
      ) r empty_rules in
  r


(** Individual rules *)
(* Unfolding rules that do not appear here (part of unfold):
 *    emp - ind
 *    pt - ind
 *    pt - seg *)
(* Rule pt - pt *)
let apply_pt_pt (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = sv_find isl ls.ls_cur_l in
  let nr = sv_find isr ls.ls_cur_r in
  match nl.ln_e, nr.ln_e with
  | Lhpt mcl, Lhpt mcr ->
      (* check alloc to add again *)
      (* check that the blocks are compatible *)
      let ls =
        Block_frag.fold_base
          (fun os pl ls ->
            let pr =
              try Block_frag.find_addr os mcr
              with _ -> Log.fatal_exn "NF in apply_pt_pt" in
            (* destination offsets *)
            let dl = pl.Graph_sig.pe_dest and dr = pr.Graph_sig.pe_dest in
            let odl = snd dl and odr = snd dr in
            if not (Offs.t_is_const odl && Offs.t_is_const odr
                      && Offs.compare odl odr = 0) then
              raise (Le_false "incompatible destination offsets");
            (* destination fields *)
            let idl = fst dl and idr = fst dr in
            let b_fail_dest =
              try Graph_utils.Nemb.find idr ls.ls_cur_i != idl
              with Not_found -> false in
            if b_fail_dest then raise (Le_false "pt-pt");
            collect_rules_node_st idl idr
              { ls with
                ls_cur_i = Graph_utils.Nemb.add idr idl ls.ls_cur_i;
                ls_rem_l = IntSet.add isl ls.ls_rem_l; }
          ) mcl ls in
      let vrules = invalidate_rules isl isr Kpt Kpt ls.ls_rules in
      { ls with
        ls_cur_l = pt_edge_block_destroy ~remrc:true isl ls.ls_cur_l;
        ls_cur_r = pt_edge_block_destroy ~remrc:true isr ls.ls_cur_r;
        ls_rules = vrules; }
  | _, _ -> Log.fatal_exn "pt-pt; improper config"
(* ind - ind *)
let apply_ind_ind (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = sv_find isl ls.ls_cur_l in
  let nr = sv_find isr ls.ls_cur_r in
  match nl.ln_e, nr.ln_e with
  | Lhlist ldl, Lhlist ldr ->
      if l_call_compare ldl ldr = 0 then
        let ls = mapdir_ind_setpars ldl ldr ls in
        { ls with
          ls_cur_l = list_edge_rem isl ls.ls_cur_l;
          ls_cur_r = list_edge_rem isr ls.ls_cur_r;
          ls_rem_l = IntSet.add isl ls.ls_rem_l;
          ls_rules = invalidate_rules isl isr Kind Kind ls.ls_rules; }
      else Log.fatal_exn "list descriptors do not match"
  | Lhemp, Lhemp ->
      (* both edges were consumed by another rule somehow;
       * we can discard the application of that rule *)
      ls
  | _, _ -> Log.fatal_exn "ind-ind; improper config"
(* seg - seg *)
let apply_seg_seg (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = sv_find isl ls.ls_cur_l in
  let nr = sv_find isr ls.ls_cur_r in
  match nl.ln_e, nr.ln_e with
  | Lhlseg (ld0, id0), Lhlseg (ld1, id1) ->
      if l_call_compare ld0 ld1 = 0 then
        if Graph_utils.Nemb.mem id0 ls.ls_cur_i then
          (* two segments match perfectly *)
          let idl = Graph_utils.Nemb.find id0 ls.ls_cur_i in
          if idl != id1 then raise (Le_false "segment mapping");
          let ls = mapdir_ind_setpars ld0 ld1 ls in
          { ls with
            ls_cur_l = lseg_edge_rem isl ls.ls_cur_l;
            ls_cur_r = lseg_edge_rem isr ls.ls_cur_r;
            ls_rem_l = IntSet.add isl ls.ls_rem_l;
            ls_rules = invalidate_rules isl isr Kseg Kseg ls.ls_rules; }
        else (* segment in the left included in a segment in the right *)
          let insrc, ls = gen_map_id Ntaddr id0 ls in
          let ls, r_seg_ld1 = mapsplit_ind_setpars ld0 ld1 ls in
          let rr =
            lseg_edge_add insrc id1 r_seg_ld1 (lseg_edge_rem isr ls.ls_cur_r) in
          collect_rules_node_st id0 insrc
            { ls with
              ls_cur_l = lseg_edge_rem isl ls.ls_cur_l;
              ls_cur_r = rr;
              ls_rem_l = IntSet.add isl ls.ls_rem_l;
              ls_rules = invalidate_rules isl isr Kseg Kseg ls.ls_rules; }
      else Log.todo_exn "unhandled seg-seg case"
  | _, _ -> Log.fatal_exn "seg-seg; improper config"
(* seg - ind *)
let apply_seg_ind (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = sv_find isl ls.ls_cur_l in
  let nr = sv_find isr ls.ls_cur_r in
  match nl.ln_e, nr.ln_e with
  | Lhlseg (ldl, idl), Lhlist ldr ->
      if l_call_compare ldl ldr = 0 then
        (* the segment in the left is a part of an inductive in the right *)
        (* remove the inductive edge being matched in the right side graph *)
        let ls = { ls with ls_cur_r = list_edge_rem isr ls.ls_cur_r } in
        (* add a fresh (middle point) node in the right side graph *)
        let insrc, ls = gen_map_id Ntaddr idl ls in
        let ls, ind_ldr = mapsplit_ind_setpars ldl ldr ls in
        collect_rules_node_st idl insrc
          { ls with
            ls_cur_l = lseg_edge_rem isl ls.ls_cur_l;
            ls_cur_r = list_edge_add insrc ind_ldr ls.ls_cur_r;
            ls_rem_l = IntSet.add isl ls.ls_rem_l;
            ls_rules = invalidate_rules isl isr Kseg Kind ls.ls_rules; }
      else Log.todo_exn "unhandled seg-ind case"
  | _, _ -> Log.fatal_exn "seg-ind; improper config"
(* void - seg *)
let apply_void_seg (isl: int) (isr: int) (ls: le_state): le_state =
  let nr = sv_find isr ls.ls_cur_r in
  match nr.ln_e with
  | Lhlseg (ldr, idr) ->
      let ext_l =
        try Graph_utils.Nemb.find idr ls.ls_cur_i
        with Not_found -> Log.fatal_exn "emp-seg: ext not mapped" in
      if ext_l = isl then 
        (* the segment can be mapped onto an empty region;
         * we get equalities on additive set variables  *)
        let set_par =
          match ldr.lc_def.ld_set with
          | None -> [ ]
          | Some si -> si.s_params in
        let ls = 
          try 
            List.fold_left2
             (fun ls r f ->
               if f.st_add || f.st_head then
                 let sr = S_eq (S_var r, S_empty) in
                 { ls with ls_setctr_r = sr :: ls.ls_setctr_r; }
               else ls
             ) ls ldr.lc_args set_par
          with
          | Not_found ->
              Log.fatal_exn "apply_void_seg: set paramters not match" in 
        { ls with
          ls_cur_r = lseg_edge_rem isr ls.ls_cur_r ;
          ls_rules = invalidate_rules isl isr Kemp Kseg ls.ls_rules }
      else (* segment not mapped into an empty region *)
        raise (Le_false (Printf.sprintf "segment to non empty: _=_> %d" idr))
  | _ -> Log.fatal_exn "void-seg; improper config"

(* stop rule
 *   this rule is specific to inductive edge search
 *   when a stop SV is encountered *)
let apply_stop_list (isl: int) (isr: int) (ls: le_state): le_state=
  (* We may discard the node left in the right graph, and
   * propagate it as a remainder in the right graph!
   * then, if all remainder is of the form  x.i()  it means
   * we may synthesize a (strong) implication edge.
   * To achieve that, we move right inductive edge into a
   * placeholder (ls_excl_l), to be checked at the end. *)
  if !Flags.flag_debug_is_le_list then
    Log.force "IsLe: reached a stop node, about to stop";
  let nr = sv_find isr ls.ls_cur_r in
  match nr.ln_e with
  | Lhemp | Lhpt _ -> ls (* nothing to do *)
  | Lhlist ld ->
      { ls with
        ls_cur_r  = list_edge_rem isr ls.ls_cur_r ;
        ls_excl_l = IntMap.add isl ld ls.ls_excl_l } 
  | Lhlseg _ -> Log.todo_exn "apply_stop_node_ind: segment"


(** Post inclusion check routine *)
(* Checks whether a configuration is a success configuration *)
exception Unmapped
let is_success (ls: le_state): le_state =
  let num_l = num_edges ls.ls_cur_l in
  let num_r = num_edges ls.ls_cur_r in
  if !Flags.flag_debug_is_le_list then
    Log.force "%sReturn from is_le: %d | %d" (pp_le_state ls) num_l num_r;
  if (not ls.ls_emp_both || num_l = 0) && num_r = 0 then
    (* Inclusion proved in the memory domain; try to discharge the proof
     * obligations that were generated, and pass the remaining ones, either
     * for instantiation in the join, or for discharging in the valset domain
     * later *)
    (* Translation function for SVs *)
    let sv_trans (i: int) =
      try Graph_utils.Nemb.find i ls.ls_cur_i
      with
      | Not_found ->
          Log.info "SV renaming failed (is_le) %d" i;
          raise Unmapped in
    (* Translation function for SETVs *)
    let setv_trans (i: int): int =
      try
        let s = Set_utils.Semb.find i ls.ls_cur_si in
        if IntSet.cardinal s > 1 then
          begin
            Log.info "choices (%d): %s" i (intset_2str s);
            Log.warn "setv_trans needs to choose among several SETVs...";
          end;
        (* we select the max element to avoid hitting the roots *)
        if IntSet.cardinal s >= 1 then IntSet.max_elt s
        else Log.fatal_exn "empty set of SETVs (though should be non empty)"
      with
      | Not_found ->
          if debug_module then
            Log.debug "SETV renaming failed (is_le) %d" i;
          raise Unmapped in
    (* Inclusion established in the list domain; moving to pure predicates *)
    if !Flags.flag_debug_is_le_list then
      begin
        Log.force 
          "Num Predicates to look at: %d,%d" (List.length ls.ls_ctr_r)
          (List.length ls.ls_setctr_r);
        List.iter
          (fun p -> Log.force "  %s" (Nd_utils.n_cons_2str p))
          ls.ls_ctr_r;
        List.iter
          (fun p -> Log.force "  %s" (Set_utils.set_cons_2str p))
          ls.ls_setctr_r;
      end;
    (* First, we look at numerical constraints *)
    let l_remain_num_cons =
      (* Before trying to discharge all constraints, we rename them, and
       * move out of the way those that cannot be fully renamed due to
       * node instantiations being required *)
      let renamed_l, non_renamed_r =
        List.fold_left
          (fun (accl, accr) ctr ->
            if !Flags.flag_debug_is_le_list then
              Log.force "Constraints on the right nodes, to rename: %s"
                (Nd_utils.n_cons_2str ctr);
            try
              Nd_utils.n_cons_map sv_trans ctr :: accl, accr
            with
            | Unmapped ->
                if !Flags.flag_debug_is_le_list then
                  Log.force "Rename-num-KO: %s"
                    (Nd_utils.n_cons_2str ctr);
                accl, ctr :: accr
          ) ([ ], [ ]) (List.rev ls.ls_ctr_r) in
      if non_renamed_r != [ ] then 
        Log.fatal_exn "Non renamed SVs in num pure constraints";
      (* Discharging of num proof obligations *)
      List.fold_left
        (fun acc lctr ->
          let bres = ls.ls_sat_l lctr in
          if !Flags.flag_debug_is_le_list then
            Log.force "Verifying num constraint on left node: %s => %b"
              (Nd_utils.n_cons_2str lctr) bres;
          if bres then acc
          else lctr :: acc
        ) [ ] renamed_l in
    (* Second, we look at set constraints:
     *  - setcons_proved: boolean, ::= "all renamed constraints get proved"
     *  - setcons_rem:    cannot be renamed; preserved for instantiation *)
    let setcons_proved, setcons_rem =
      (* Simplify the constraints, by removing SETVs that were added by
       * unfolding during the inclusion check, and that are not mapped *)
      let all_setvs =
        List.fold_left (fun acc c -> IntSet.union acc (set_cons_setvs c))
          IntSet.empty ls.ls_setctr_r in
      let rem_setvs =
        IntSet.filter
          (fun i -> not (IntMap.mem i ls.ls_cur_si.n_img)
              && IntSet.mem i ls.ls_newsetv_r) all_setvs in
      if debug_module then
        Log.debug "Should remove SETVs: %s" (intset_2str rem_setvs);
      let setcons = set_cons_prune_setvs rem_setvs ls.ls_setctr_r in
      List.fold_left
        (fun (accb, accl) c ->
          try
            if debug_module then
              Log.debug "constraint:   %s" (Set_utils.set_cons_2str c);
            let rc = Set_utils.s_cons_map sv_trans setv_trans c in
            if debug_module then
              Log.debug "constraint => %s" (Set_utils.set_cons_2str rc);
            let satres = ls.ls_setsat_l rc in
            if debug_module then
              Log.debug " satisfaction: %b" satres;
            accb && satres, accl
          with
          | Unmapped ->
              if !Flags.flag_debug_is_le_list then
                Log.force "Rename-set-KO: %s" (Set_utils.set_cons_2str c);
              accb, c :: accl
        ) (true, [ ]) setcons in
    (* Rename and prove equalities induced by the relation *)
    let setcons_proved =
      IntMap.fold
        (fun i s acc ->
          if IntSet.cardinal s > 1 then
            let rep = IntSet.min_elt s in
            let others = IntSet.remove rep s in
            IntSet.fold
              (fun j acc ->
                let b = ls.ls_setsat_l (S_eq (S_var j, S_var rep)) in 
                if debug_module then
                  Log.debug "Adding SETV-eq: S[%d] = S[%d]: %b" i j b;
                acc && b
              ) others acc
          else acc
        ) ls.ls_cur_si.n_img setcons_proved in
    if debug_module then
      Log.debug "Setcons:%b,%d" setcons_proved (List.length setcons_rem);
    { ls with
      ls_ctr_r    = [ ] ; (* accumulator becomes empty *)
      ls_setctr_r = setcons_rem;
      ls_success  = (setcons_proved && List.length l_remain_num_cons = 0) }
  else (* Inclusion could not be established in the memory domain *)
    { ls with ls_success  = false }

(** The new inclusion algorithm, with refactored strategy application *)
(* This function is based on a recursive algorithm implementing a worklist
 * on applicable rules (not on nodes or edges!) *)
let rec is_le_rec (ls: le_state): le_state =
  (* Find out the next rule to apply *)
  match rules_next ls.ls_rules with
  | None -> ls
  | Some (k, (il, ir), rem_rules) ->
      if !Flags.flag_debug_is_le_list then
        begin
          Log.force "%sIsLe-Treating (%d,%d): %s" (pp_le_state ls) il ir
            (rkind_2str k);
          if !Flags.flag_debug_is_le_strategy then
            Log.force "isle-rules ready:\n%s" (rules_2str ls.ls_rules)
        end;
      let ls = { ls with ls_rules = rem_rules } in
      let ls =
        match k with
        | Rstop -> apply_stop_list  il ir ls
        | Rpp   -> apply_pt_pt      il ir ls
        | Rii   -> apply_ind_ind    il ir ls
        | Rss   -> apply_seg_seg    il ir ls
        | Rsi   -> apply_seg_ind    il ir ls
        | Rvs   -> apply_void_seg   il ir ls
        | Rei   -> is_le_unfold true  il ir ls
        | Rps
        | Rpi   -> is_le_unfold false il ir ls in
      is_le_rec ls
and is_le_unfold
    (hint_empty: bool) (* whether to consider empty rules first or last*)
    (il: int) (ir: int) (ls: le_state): le_state =
  if !Flags.flag_debug_is_le_list then
    Log.force "IsLe triggerring unfolding<%b>" hint_empty;
  let l_mat =
    (* if only non empty unfold allowed, do selective unfolding *)
    let only_non_emp = IntSet.mem ir ls.ls_no_unf0 in
    List_mat.unfold ir only_non_emp ls.ls_cur_r in
  if !Flags.flag_debug_is_le_list then
    Log.force "IsLe performed unfolding: %d" (List.length l_mat);
  let els =
    List.fold_left
      (fun acc ur ->
        match acc with
        | Some _ ->
            (* inclusion already found, no other check *)
            acc
        | None ->
            (* inclusion not found yet; we try current disjunct *)
            List.iter
              (fun ctr ->
                if !Flags.flag_debug_is_le_list then  
                  Log.force 
                    "Num Predicate added to prove, on right side: %s"
                    (Nd_utils.n_cons_2str ctr)
              ) ur.ur_cons;
            try
              let ls0 =
                let nsetvs =
                  IntMap.fold (fun i _ -> IntSet.add i) ur.ur_newsetvs
                    ls.ls_newsetv_r in
                collect_rules_node_st il ir
                  { ls with
                    ls_cur_r     = ur.ur_lmem;
                    ls_ctr_r     = ur.ur_cons @ ls.ls_ctr_r;
                    ls_setctr_r  = ur.ur_setcons @ ls.ls_setctr_r;
                    ls_newsetv_r = nsetvs } in
              let ols = is_le_rec ls0 in
              let lsuccess = is_success ols in
              if lsuccess.ls_success then Some lsuccess
              else None
            with
            | Le_false msg ->
                if !Flags.flag_debug_is_le_list then  
                  Log.force "is_success returned and failed: %s" msg;
                (* underlying test may fail, while next succeeds *)
                (* hence, we catch Le_false and return None here *)
                None
      ) None l_mat in
  match els with
  | None -> raise (Le_false "unfold: no successful branch")
  | Some ls ->
      assert ls.ls_success ;
      ls

(** General inclusion functions (inclusion testing engine) *)
let is_le_start (ls: le_state): le_state option =
  (* Iteration *)
  let ols = is_le_rec ls in
  (* Computation of the inclusion check result *)
  let lls = is_success ols in
  if lls.ls_success then
    (* inclusion holds, relation gets forwarded *)
    Some lls
  else
    (* inclusion does not hold, no relation to forward *)
    None
let gen_is_le
    (emp_both: bool)        (* whether both arguments should be fully emptied *)
    (stop: int Aa_sets.t option) (* optional stop nodes *)
    (xl: lmem)              (* left input *)
    (nou0: IntSet.t)        (* no unfold 0 *)
    (es: IntSet.t)          (* segment end(s), if any *)
    (pl: n_cons -> bool)    (* satisfiability, in the left argument *)
    (sl: set_cons -> bool)  (* satisfiability, left arg, set constraints *)
    (xr: lmem)              (* right input *)
    (r: Graph_sig.node_emb) (* injection from right into left *)
    (* injection from right set variables into left set variables *) 
    (s_r: Graph_sig.node_emb)
    : le_state option =
  let ni = Graph_utils.Nemb.init r in
  let si = Set_utils.Semb.init s_r in
  let rules = rules_init emp_both es ni xl xr r in
  let ils = { ls_cur_l     = xl ;
              ls_cur_r     = xr ;
              ls_cur_i     = ni ;
              ls_cur_si    = si;
              ls_rules     = rules;
              ls_rem_l     = IntSet.empty ;
              ls_sat_l     = pl ;
              ls_setsat_l  = sl ;
              ls_ctr_r     = [ ] ;
              ls_setctr_r  = [ ] ;
              ls_newsetv_r = IntSet.empty ;
              ls_success   = false ;
              ls_emp_both  = emp_both;
              ls_stop_l    = stop;
              ls_excl_l    = IntMap.empty;
              ls_no_unf0   = nou0;
              ls_end_seg   = es; } in
  try
    if not !very_silent_mode then
      Log.force "start is_le";
    let ob = is_le_start ils in
    if not !very_silent_mode then
      Log.force "return is_le %b" (ob != None);
    ob
  with
  | Le_false s ->
      if not !very_silent_mode then
        Log.force "[List]  is_le fails on exception: %s" s;
      None

(** Full inclusion checking, used in the domain functor *)
let is_le
    (xl: lmem)              (* left input *)
    (pl: n_cons -> bool)    (* satisfiability, in the left argument *)
    (sl: set_cons -> bool) (* satisfiability, left arg, set constraints *)
    (xr: lmem)              (* right input *)
    (r: Graph_sig.node_emb) (* injection from right into left *)
    (* injection from right set var into left set var *)
    (s_r: Graph_sig.node_emb)
    : is_le_ym =
  let res = gen_is_le true None xl IntSet.empty IntSet.empty pl sl xr r s_r in
  match res with
  | None -> `Ilr_not_le
  | Some ls ->
      if ls.ls_success then 
        `Ilr_le (ls.ls_cur_i.Graph_sig.n_img, ls.ls_cur_si.Set_sig.n_img, 
                 ls.ls_setctr_r)
      else `Ilr_not_le

(** Partial inclusion checking function, used for join *)
let is_le_weaken_check
    (xl: lmem)              (* left input *)
    (nou0: IntSet.t)        (* no unfold 0 *)
    (es: IntSet.t)          (* segment end(s), if any *)
    (pl: n_cons -> bool)    (* satisfiability, in the left argument *)
    (sl: set_cons -> bool)  (* satisfiability, left arg, set constraints *)
    (xr: lmem)              (* right input *)
    (r: Graph_sig.node_emb) (* injection from right into left *)
    (* injection from right setvar into left set var *)
    (svar_r: Graph_sig.node_emb)
    : List_sig.is_le_weaken_check =
  let res = gen_is_le false None xl nou0 es pl sl xr r svar_r in
  match res with
  | None -> `Ilr_not_le
  | Some ls ->
      `Ilr_le_rem (ls.ls_cur_l, ls.ls_rem_l, ls.ls_cur_i.Graph_sig.n_img,
                   ls.ls_cur_si.Set_sig.n_img,
                   ls.ls_setctr_r)

(** Partial inclusion checking functeion, used for unary abstract *)
let is_le_weaken_guess
    ~(stop: int Aa_sets.t option) (* optional stop nodes *)
    (xl: lmem)           (* left input *)
    (nou0: IntSet.t)        (* no unfold 0 *)
    (es: IntSet.t)       (* segment end(s), if any *)
    (pl: n_cons -> bool) (* satisfiability, in the left argument *)
    (sl: set_cons -> bool) (* satisfiability, left arg, set constraints *)
    (xr: lmem)           (* right input *)
    (r: Graph_sig.node_emb) (* injection from right into left *)
    (* injection from right setvar into left set var *)
    (svar_r: Graph_sig.node_emb)
    : List_sig.is_le_weaken_guess =
  let res = gen_is_le false stop xl nou0 es pl sl xr r svar_r in
  match res with
  | None -> `Ilr_not_le
  | Some ls ->
      (* - if no stop node found, returns a full inductive
       * - if one stop node found, returns a segment
       * - if several stop nodes found, fails *)
      IntMap.fold
        (fun i ld -> function
          | `Ilr_le_list _ -> 
              `Ilr_le_lseg (ls.ls_cur_l, i, ls.ls_cur_i.Graph_sig.n_img,
                            ls.ls_cur_si.Set_sig.n_img, ls.ls_setctr_r)
          | _ -> Log.fatal_exn "is_le_weaken: too many solutions"
        ) ls.ls_excl_l (`Ilr_le_list (ls.ls_cur_l, ls.ls_cur_i.Graph_sig.n_img,
                                      ls.ls_cur_si.Set_sig.n_img,
                                      ls.ls_setctr_r))
