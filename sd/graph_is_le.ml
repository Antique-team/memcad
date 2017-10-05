(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_is_le.ml
 **       inclusion algorithm on graphs
 ** Xavier Rival, 2011/09/21 *)
open Data_structures
open Flags
open Lib

open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig
open Inst_sig

open Set_sig
open Gen_dom
open Gen_is_le

open Graph_utils
open Set_utils
open Inst_utils


(** Error report *)
module Log =
  Logger.Make(struct let section = "g_isle__" and level = Log_level.DEBUG end)
let debug_module = false


(** Inclusion check auxilliary elements *)
(* A notion of state used in the inclusion check algorithm *)
type le_state =
    { (* Arguments configurations *)
      ls_cur_l:    graph ;
      ls_cur_r:    graph ;
      ls_cur_i:    node_embedding ; (* current right to left mapping *)
      (* Mapping from right SETVs into left SETVs *)
      ls_cur_si:   setv_embedding;
      (** Iteration strategy *)
      (* Pending rules (given as pairs of node names) *)
      ls_rules:    rules ; (* instances of rules pending application *)
      (* Nodes that were removed in the left argument (helps join) *)
      ls_rem_l:    IntSet.t ;
      (** Underlying domain constraints *)
      (* Satisfiability *)
      ls_sat_l:    (n_cons -> bool) ;
      ls_setsat_l: (set_cons -> bool) ;
      (* new constraints on fresh symbolic variables of left *)
      ls_ctr_l:    n_cons list ;     (* constraints on fresh SVs *)
      ls_fsvs_l:   IntSet.t;         (* fresh SVs *)
      ls_inst_l:   n_expr IntMap.t;
      (* Accumulation of constraints *)
      ls_ctr_r:    n_cons list ;
      ls_setctr_r: set_cons list ;
      (* used for future guess_cons instantiation *)
      ls_iseg_r: seg_edge list ;
      (* collect the fresh node and their arguments introduced
       * on the right side in rules seg-seg, seg-ind *)
      ls_fresh_seg_r: ind_edge IntMap.t ;
      (** Termination of the inclusion checking *)
      (* Whether we only need to empty both graphs or only the left graph *)
      ls_emp_both: bool ;
      (* Whether a success configuration has been reached *)
      ls_success:  bool ;
      (** Hints *)
      (* Hint on the left argument: nodes not to split *)
      ls_hint_l:   int Aa_sets.t option ;
      (* Right remainder, excluded due to hint => left *)
      ls_excl_l:   graph ;
      (* Optional "end of segment node", to inhibit rules from that point *)
      ls_end_seg:  IntSet.t ;
      (** Parameters about the is_le semantics *)
      (* Whether we consider a sub-memory: no alloc check for sub-memories *)
      ls_submem:   bool;
      (* derive some disequality from left graph *)
      ls_gl_diseq: (int -> int -> bool);
    }
(* Pretty-printing of a configuration *)
let pp_le_state (ls: le_state): string =
  let config_sep: string = "------------------------------------------\n" in
  let s0 =
    Printf.sprintf "%sLeft:\n%sRight:\n%sInjection:\n%sSet Inject:\n%s\n"
      config_sep (graph_2stri " " ls.ls_cur_l) (graph_2stri " " ls.ls_cur_r)
      (Nemb.ne_full_2stri "  " ls.ls_cur_i)
      (Set_utils.Semb.ne_full_2stri "  " ls.ls_cur_si)
  and s1 =
    Printf.sprintf "N_cons:\n%s\nSet_cons:\n%s\nN_cons_l:\n%s\nN_fresh_svs_l:\n%s\nN_inst_l:\n%s\n%s\n "
      (gen_list_2str "" Nd_utils.n_cons_2str ";" ls.ls_ctr_r)
      (gen_list_2str "" Set_utils.set_cons_2str ";" ls.ls_setctr_r)
      (gen_list_2str "" Nd_utils.n_cons_2str ";" ls.ls_ctr_l)
      (IntSet.t_2str ";" ls.ls_fsvs_l)
      (IntMap.t_2str "\n" Nd_utils.n_expr_2str ls.ls_inst_l)
      config_sep in
  s0 ^ s1

(** Management of the set of applicable rules *)
(* Collecting applicable rules at a graph node *)
let collect_rules_node_gen =
  let sv_seg_end i g =
    match (node_find i g).n_e with
    | Hseg se -> Some se.se_dnode
    | Hemp | Hpt _ | Hind _ -> None in
  collect_rules_sv_gen sv_kind sv_seg_end
let collect_rules_node = collect_rules_node_gen false None
let collect_rules_node_st (il: nid) (ir: nid) (ls: le_state): le_state =
  let nr =
    collect_rules_node_gen false ls.ls_hint_l ls.ls_end_seg ls.ls_cur_i
      ls.ls_cur_l ls.ls_cur_r il ir ls.ls_rules in
  { ls with ls_rules = nr }
(* Initialization: makes prioretary points-to rules *)
let rules_init
    (prio: bool) (* whether available pt-edges should be treated in priority *)
    (es: IntSet.t) (* end of segment(s), if any *)
    (ni: node_embedding)
    (gl: graph) (gr: graph) (r: node_emb): rules =
  if !Flags.flag_debug_is_le_shape then
    Log.force "isle init,l:\n%sisle init,-r:\n%s"
      (graph_2stri "  " gl) (graph_2stri "  " gr);
  let r =
    Aa_maps.fold
      (fun ir il acc ->
        if !Flags.flag_debug_is_le_shape then
          Log.force "collecting at %d,%d" il ir;
        collect_rules_node_gen prio None es ni gl gr il ir acc
      ) r empty_rules in
  r



(** Utility functions for the is_le rules *)

(* Checks whether it is possible to match to lists of arguments
 * in the current configuration *)
let arg_match (ls: le_state) (al: ind_args) (ar: ind_args): bool =
  assert (List.length al.ia_int = 0);
  assert (List.length ar.ia_int = 0);
  assert (List.length al.ia_ptr = List.length ar.ia_ptr);
  List.fold_left2
    (fun acc ial iar ->
      try acc && Nemb.find iar ls.ls_cur_i = ial
      with Not_found -> false
    ) true al.ia_ptr ar.ia_ptr

(* Augment the current mapping to take into account a matching of
 * a pair of lists of inductive arguments *)
let fix_map_id (msg: string) (ls: le_state) (il: nid) (ir: nid): le_state =
  try
    let oil = Nemb.find ir ls.ls_cur_i in
    if oil = il then ls
    else
      (* in the case of equal *)
    if IntSet.mem il ls.ls_fsvs_l then
      let cs = Nc_cons (Apron.Tcons1.EQ, Ne_var il, Ne_var oil) in
      { ls with ls_ctr_l = cs :: ls.ls_ctr_l }
    else if
      ls.ls_sat_l (Nc_cons (Apron.Tcons1.EQ, Ne_var il, Ne_var oil)) then ls
    else
      raise (Le_false (Printf.sprintf "fix_map[%s] (%d,%d->%d)" msg ir il oil))
  with
  | Not_found ->
      collect_rules_node_st il ir
        { ls with ls_cur_i = Nemb.add ir il ls.ls_cur_i }
let fix_map_args (msg: string)
    (ls: le_state) (al: nid list) (ar: nid list): le_state =
  if List.length al != List.length ar then
    Log.fatal_exn "fix_map_args[%s], lengths differ" msg;
  let smsg = Printf.sprintf "%s,l" msg in
  List.fold_left2 (fix_map_id smsg) ls al ar
let fix_map_pargs (msg: string)
    (ls: le_state) (al: ind_args) (ar: ind_args): le_state =
  fix_map_args (Printf.sprintf "%s,ptr" msg) ls al.ia_ptr ar.ia_ptr
let fix_map_iargs (msg: string)
    (ls: le_state) (al: ind_args) (ar: ind_args): le_state =
  fix_map_args (Printf.sprintf "%s,int" msg) ls al.ia_int ar.ia_int
let fix_map_sargs (msg: string)
    (ls: le_state) (al: ind_args) (ar: ind_args): le_state =
  if List.length al.ia_set != List.length ar.ia_set then
    Log.fatal_exn "fix_map_args[%s], lengths differ" msg;
  try
    List.fold_left2
      (fun ls r l ->
        { ls with
          ls_cur_si = Set_utils.Semb.add r l ls.ls_cur_si; }
      ) ls ar.ia_set al.ia_set
  with Invalid_argument _ ->
    Log.fatal_exn "mapdir_ind_setpars: arguments not match"

let wkind_map_int_arg (msg: string) (ls: le_state) (ty: int_wk_typ)
    (il: nid) (ir: nid): le_state =
  let f ir ls =
    try
      Nemb.find ir ls.ls_cur_i, ls
    with
      Not_found ->
        let ill, g = sv_add_fresh Ntint Nnone ls.ls_cur_l in
        ill, { ls with
               ls_cur_l = g;
               ls_fsvs_l = IntSet.add ill ls.ls_fsvs_l;
               ls_cur_i = Nemb.add ir ill ls.ls_cur_i } in
  match ty with
  | `Eq -> fix_map_id msg ls il ir
  | `Non -> if Nemb.mem ir ls.ls_cur_i then ls else snd (f ir ls)
  | `Leq ->
      let ill, ls = f ir ls in
      let ctr = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var ill, Ne_var il) in
      { ls with ls_ctr_l = ctr :: ls.ls_ctr_l }
  | `Geq ->
      let ill, ls = f ir ls in
      let ctr = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var il, Ne_var ill) in
      { ls with ls_ctr_l = ctr :: ls.ls_ctr_l }
  | `Add -> fix_map_id msg ls il ir

let wkind_map_int_args (msg: string) (ls: le_state)
    (tys: int_wk_typ IntMap.t) (ils: nid list) (irs: nid list)
    : le_state =
  let _, ls =
    List.fold_left2
      (fun (index, ls) il ir ->
        let ls = wkind_map_int_arg msg ls (IntMap.find index tys) il ir in
        index+1, ls
      ) (0, ls) ils irs in
  ls

let wkind_map_set_arg (msg: string) (ls: le_state) (ty: set_wk_typ)
    (il: nid) (ir: nid): le_state =
  match ty with
  | `Eq | `SAdd _ ->
    { ls with
      ls_cur_si = Set_utils.Semb.add ir il ls.ls_cur_si; }
  | `Non ->
    let ill, g = setv_add_fresh false None ls.ls_cur_l in
    { ls with
      ls_cur_l = g ;
      ls_cur_si =Set_utils.Semb.add ir ill ls.ls_cur_si }

let wkind_map_set_args (msg: string) (ls: le_state)
    (tys: set_wk_typ IntMap.t) (ils: nid list) (irs: nid list)
  : le_state =
  let _, ls =
    List.fold_left2 (fun (index, ls) il ir ->
        let ls =
          wkind_map_set_arg msg ls (IntMap.find index tys) il ir in
        index+1, ls
      ) (0, ls) ils irs in
  ls

let wkind_map_is_args (msg: string) (ls: le_state)
    (tys: pars_wk_typ) (il: ind_args) (ir: ind_args)
  : le_state =
  wkind_map_set_args msg
    (wkind_map_int_args msg ls tys.int_typ il.ia_int ir.ia_int )
    tys.set_typ il.ia_set ir.ia_set

let fix_map_all_args (msg: string)
    (ls: le_state) (al: ind_args) (ar: ind_args): le_state =
  fix_map_sargs msg
    (fix_map_iargs msg (fix_map_pargs msg ls al ar) al ar) al ar

(* Generate a fresh node, to be mapped with some given node *)
let fresh_map_id (nt: ntyp) (il: int) (ls: le_state): int * le_state =
  let ir, g = sv_add_fresh nt Nnone ls.ls_cur_r in
  ir, { ls with
        ls_cur_r = g ;
        ls_cur_i = Nemb.add ir il ls.ls_cur_i }
(* Generate a fresh set variable, to be mapped with some given set variable *)
let fresh_map_sid (il: int) (ls: le_state): int * le_state =
  let ir, g = setv_add_fresh false None ls.ls_cur_r in
  ir, { ls with
        ls_cur_r = g ;
        ls_cur_si =Set_utils.Semb.add ir il ls.ls_cur_si }

let fresh_map_args (nt: ntyp) (ill: int list)
    (ls: le_state): nid list * le_state =
  let lppars, inj, rg2 =
    List.fold_left
      (fun (acclr, acci, accg) il ->
        let nir, ngr =
          sv_add_fresh nt Nnone accg in
        nir :: acclr, Nemb.add nir il acci, ngr
      ) ([ ], ls.ls_cur_i, ls.ls_cur_r) ill in
  List.rev lppars,
  { ls with
    ls_cur_r = rg2 ;
    ls_cur_i = inj }

let fresh_map_iargs (ill: int list) (ls: le_state)
  : nid list * le_state =
  let lipars, rg2 =
    List.fold_left
      (fun (acclr, accg) il ->
        let nir, ngr = sv_add_fresh Ntint Nnone accg in
        nir :: acclr, ngr
      ) ([ ], ls.ls_cur_r) ill in
  let ls =  { ls with ls_cur_r = rg2} in
  let irr =  List.rev lipars in
  irr, ls

let fresh_map_sargs (ill: int list)
    (ls: le_state): nid list * le_state =
  let lspars, sinj, rg2 =
    List.fold_left
      (fun (acclr, acci, accg) il ->
        let nir, ngr =
          setv_add_fresh false None accg in
        nir :: acclr, Set_utils.Semb.add nir il acci, ngr
      ) ([ ], ls.ls_cur_si, ls.ls_cur_r) ill in
  List.rev lspars,
  { ls with
    ls_cur_r = rg2 ;
    ls_cur_si = sinj }

let fresh_map_all_args (al: ind_args)  (ls: le_state)
    : int list * int list * int list * le_state =
  let lppars, ls = fresh_map_args Ntaddr al.ia_ptr ls in
  let lipars, ls = fresh_map_iargs al.ia_int ls in
  let lspars, ls = fresh_map_sargs al.ia_set ls in
  lppars, lipars, lspars, ls

let wkseg_iargs (msg: string) (l_sargs: ind_args) (l_dargs: ind_args)
    (r_sargs: ind_args)
    (r_dargs: ind_args) (ind: ind) (ls: le_state): le_state =
  let do_nth_arg (index: int) (lsa: int) (lda: int) (rsa: int) (rda: int)
      (wkt: int_wk_typ) (ls: le_state): le_state =
    match wkt with
    | `Eq -> fix_map_id msg (fix_map_id msg ls lsa rsa) lda rda
    | `Non -> ls
    | `Leq -> wkind_map_int_arg msg
                (wkind_map_int_arg msg ls `Leq lsa rsa) `Geq lda rda
    | `Geq -> wkind_map_int_arg msg
                (wkind_map_int_arg msg ls `Geq lsa rsa) `Leq lda rda
    | `Add ->
        let isa, g = sv_add_fresh Ntint Nnone ls.ls_cur_l in
        let ida, g = sv_add_fresh Ntint Nnone g in
        let ctr = Nc_cons (Apron.Tcons1.EQ, Ne_var isa,
                           Ne_bin (Apron.Texpr1.Add, Ne_var ida,
                                   Ne_bin (Apron.Texpr1.Sub,
                                           Ne_var lsa, Ne_var lda))) in
        let ls =  { ls with
                    ls_cur_l  = g;
                    ls_fsvs_l = IntSet.add isa (IntSet.add ida ls.ls_fsvs_l);
                    ls_ctr_l  = ctr :: ls.ls_ctr_l } in
        fix_map_id msg (fix_map_id msg ls isa rsa) ida rda in
  let rec do_args (index: int) (l_sargs: int list) (l_dargs: int list)
      (r_sargs: int list)
      (r_dargs: int list) (wk: int_wk_typ IntMap.t) (ls: le_state): le_state =
    match l_sargs, l_dargs, r_sargs, r_dargs with
    | [], [], [], [] -> ls
    | lsa :: tl_s, lda :: tl_d, rsa :: tr_s, rda :: tr_d ->
        let ls = do_nth_arg index lsa lda rsa rda (IntMap.find index wk) ls in
        do_args (index+1) tl_s tl_d tr_s tr_d wk ls
    | _ ->  Log.fatal_exn "fix_map_args[%s], lengths differ" msg; in
  do_args 0 l_sargs.ia_int l_dargs.ia_int r_sargs.ia_int r_dargs.ia_int
    ind.i_pars_wktyp.int_typ ls


(* Enriching an algorithm state with the result of a unification *)
let le_state_enrich (l: (int * int * int) list) (ls: le_state): le_state =
  List.fold_left
    (fun (ls: le_state) (il, ir, _) ->
      fix_map_id "make_blocks_compatible" ls il ir
    ) ls l

(* Making blocks compatible, through a possibly enriched unification *)
let make_blocks_compatible
    (mcl: pt_edge Block_frag.t) (mcr: pt_edge Block_frag.t)
    (ls: le_state)
    : le_state * bool =
  let bf_2str = Block_frag.block_frag_2str (fun _ -> ".") in
  if !Flags.flag_debug_graph_blocks then
    Log.force "Enforcing compatibility:\n - %s\n - %s"
      (bf_2str mcl) (bf_2str mcr);
  (* Enrich the mapping with extra mappings *)
  (* Attempt at performing the unification *)
  try
    Block_frag.fold_list2_bound1
      (fun lbeg rbeg ls ->
        match Bounds.unify_all lbeg rbeg with
        | None -> raise Stop
        | Some (uni, ubeg) -> le_state_enrich uni ls
      ) mcl mcr ls, true
  with
  | Stop -> ls, false



(** Individual rules *)
(* Unfolding rules that do not appear here and are part of unfold:
 *    emp - ind
 *    pt - ind
 *    pt - seg *)

(* Below is the implementation of all the non unfolding rules *)
(* pt - pt [par ptr OK, par int OK] *)
let apply_pt_pt (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = node_find isl ls.ls_cur_l in
  let nr = node_find isr ls.ls_cur_r in
  match nl.n_e, nr.n_e with
  | Hpt mcl, Hpt mcr ->
      if not ls.ls_submem then
        begin (* allocation consistency check, but only if not submem *)
          let check_alloc =
            match nl.n_alloc, nr.n_alloc with
            | Nstack, Nstack
            | Nnone, Nnone -> true
            | Nheap sl, Nheap sr -> sl = sr
            | _, _ -> false in
          if not check_alloc then
            Log.fatal_exn "alloc constraint fails: %s-%s"
              (nalloc_2str nl.n_alloc) (nalloc_2str nr.n_alloc)
        end;
      (* Experimental code for arrays *)
      let sz_l = Block_frag.cardinal mcl and sz_r = Block_frag.cardinal mcr in
      if sz_l != sz_r then raise (Le_false "sizes do not match");
      let ls, compat =
        let r = make_blocks_compatible mcl mcr ls in
        if !Flags.flag_debug_graph_blocks then
          Log.force "Arrayness: %b" (not (fst r == ls));
        r in
      if not compat then
        raise (Le_false "blocks not compatible");
      (* Code that works only in the non array case *)
      let ls =
        Block_frag.fold_base
          (fun os pl ls ->
            if Block_frag.mem os mcr then
              let pr = Block_frag.find_addr os mcr in
              (* Sizes do not normally need be matched
               * (the matching of bounds kind of supersedes it) *)
              if not (pl.pe_size = pr.pe_size) then
                Log.warn "is_le, pt-pt, sizes";
              let ls =
                let odl = snd pl.pe_dest and odr = snd pr.pe_dest in
                if !Flags.flag_debug_graph_blocks then
                  Log.force "unifying %s-%s"
                    (Offs.t_2str odl) (Offs.t_2str odr);
                if Offs.t_is_const odl && Offs.t_is_const odr
                    && Offs.compare odl odr = 0 then ls
                else
                  match Offs.t_unify odl odr with
                  | None -> raise (Le_false "incompatible destination offsets")
                  | Some (uni, _) -> le_state_enrich uni ls in
              let idl = fst pl.pe_dest and idr = fst pr.pe_dest in
              (* check we do not overwrite anything in the mapping *)
              (* => alternative solution: add equality constraint to prove *)
              (* check treatment of this problem here *)
              let ls_cur_i =
                if Nemb.mem idr ls.ls_cur_i then
                  let midl = Nemb.find idr ls.ls_cur_i in
                  if midl = idl then ls.ls_cur_i
                  else (* prove equality *)
                    if ls.ls_sat_l (Nc_cons (Apron.Tcons1.EQ, Ne_var idl,
                                             Ne_var midl)) then
                      ls.ls_cur_i
                    else
                      raise (Le_false "pt-pt creates incompatible mapping")
                else
                  Nemb.add idr idl ls.ls_cur_i in
              collect_rules_node_st idl idr
                { ls with
                  ls_cur_i = ls_cur_i;
                  ls_rem_l = IntSet.add isl ls.ls_rem_l; }
            else ls
          ) mcl ls in
      let vrules = invalidate_rules isl isr Kpt Kpt ls.ls_rules in
      { ls with
        ls_cur_l = pt_edge_block_destroy isl ls.ls_cur_l;
        ls_cur_r = pt_edge_block_destroy isr ls.ls_cur_r;
        ls_rules = vrules; }
  | _, _ -> Log.fatal_exn "pt-pt; improper config"

(* ind - ind [par ptr OK, par int OK] *)
let apply_ind_ind (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = node_find isl ls.ls_cur_l in
  let nr = node_find isr ls.ls_cur_r in
  match nl.n_e, nr.n_e with
  | Hind icl, Hind icr ->
      if Ind_utils.compare icl.ie_ind icr.ie_ind = 0 then
        (* deal with integer and set parameters *)
        let wk_type = compute_wk_type isl icl ls.ls_sat_l in
        let ls =
          wkind_map_is_args "ind-ind" ls wk_type
            icl.ie_args icr.ie_args in
        (* HSL: deal with pointer parameters with hacks *)
        let ls =
          (* fast ind-ind rule: if left ptr is null, tries to discharge
           * obligation, without matching parameters *)
          if !Flags.do_quick_ind_ind_mt
              && icl.ie_ind.i_mt_rule
              && ls.ls_sat_l (Nc_cons (Apron.Tcons1.EQ,
                                       Ne_var isl, Ne_csti 0))
              && Ind_utils.no_par_use_rules_emp icl.ie_ind
              (* when left ptr is null, parameters may *
               * need match, therefore, some heuristic to guess when *
               * matching is not necessary *)
              && List.exists (fun ele ->
                  (node_find ele ls.ls_cur_l).n_attr <> Attr_none ||
                  (Nemb.mem ele ls.ls_cur_i)
                ) icl.ie_args.ia_ptr
          then
            (* heap region in the left side is empty and all the empty rules
             * assert no information on all parameters => no matching ! *)
            ls
          else fix_map_pargs "ind-ind" ls icl.ie_args icr.ie_args in
        { ls with
          ls_cur_l = ind_edge_rem isl ls.ls_cur_l;
          ls_cur_r = ind_edge_rem isr ls.ls_cur_r;
          ls_rem_l = IntSet.add isl ls.ls_rem_l;
          ls_rules = invalidate_rules isl isr Kind Kind ls.ls_rules }
      else Log.fatal_exn "inductives do not match"
  | Hemp, Hemp ->
      (* both edges were consumed by another rule somehow;
       * we can discard the application of that rule *)
      ls
  | _, _ -> Log.fatal_exn "ind-ind; improper config"

(* seg - seg [par ptr OK, par int KO] *)
let apply_seg_seg (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = node_find isl ls.ls_cur_l in
  let nr = node_find isr ls.ls_cur_r in
  match nl.n_e, nr.n_e with
  | Hseg s0, Hseg s1 ->
      if Ind_utils.compare s0.se_ind s1.se_ind = 0 then
        let ls = fix_map_pargs "seg_seg,src" ls s0.se_sargs s1.se_sargs in
        let ls = fix_map_sargs "seg_seg,src" ls s0.se_sargs s1.se_sargs in
        (* default case: a*=b * G < a*=d * H   ==>   d*=b * G < H *)
        let default_seg_seg ( ) =
          (* segment gets consumed in the left argument;
           * another (shorter) segment gets added in the right argument *)
          (* remove the former segment in the right side *)
          let ls = { ls with ls_cur_r = seg_edge_rem isr ls.ls_cur_r } in
          (* add a fresh (middle point) node in the right side graph *)
          let insrc, ls = fresh_map_id Ntaddr s0.se_dnode ls in
          (* add fresh nodes for the mapping of middle arguments *)
          let lppars, lipars, lspars, ls =
            fresh_map_all_args s0.se_dargs ls in
          let se_args = { ia_ptr = lppars ;
                          ia_int = lipars;
                          ia_set = lspars; } in
          let ls =
            wkseg_iargs "seg_seg,int" s0.se_sargs s0.se_dargs s1.se_sargs
              se_args s0.se_ind ls in
          (* build the fresh segment edge and add it to the right side graph *)
          let se = { se_ind   = s0.se_ind ;
                     se_sargs = se_args;
                     se_dargs = s1.se_dargs ;
                     se_dnode = s1.se_dnode } in
          collect_rules_node_st s0.se_dnode insrc
            { ls with
              ls_cur_l = seg_edge_rem isl ls.ls_cur_l;
              ls_cur_r = seg_edge_add insrc se ls.ls_cur_r;
              ls_rem_l = IntSet.add isl ls.ls_rem_l;
              ls_fresh_seg_r =
              IntMap.add insrc { ie_ind  = s0.se_ind;
                                 ie_args = se_args} ls.ls_fresh_seg_r;
              ls_rules = invalidate_rules isl isr Kseg Kseg ls.ls_rules } in
        (* s1: right side, s0: left side *)
        if Nemb.mem s1.se_dnode ls.ls_cur_i then
          (* case:  a*=b * G < a*=b * H   ==>   G < H *)
          (* attempts to match both segments and remove them completely *)
          let idl = Nemb.find s1.se_dnode ls.ls_cur_i in
          if idl = s0.se_dnode then
            let ls = fix_map_pargs "seg_seg,dst" ls s0.se_dargs s1.se_dargs in
            let ls = fix_map_sargs "seg_seg,dst" ls s0.se_dargs s1.se_dargs in
            let ls = wkseg_iargs "seg_seg,int" s0.se_sargs s0.se_dargs
                s1.se_sargs s1.se_dargs s0.se_ind ls in
            (* we can consume both segments in the same time *)
            let ls_iseg_r =
              if s1.se_dargs.ia_int = [] then ls.ls_iseg_r
              else s1::ls.ls_iseg_r in
            { ls with
              ls_cur_l = seg_edge_rem isl ls.ls_cur_l;
              ls_cur_r = seg_edge_rem isr ls.ls_cur_r;
              ls_iseg_r = ls_iseg_r;
              ls_rem_l = IntSet.add isl ls.ls_rem_l;
              ls_rules = invalidate_rules isl isr Kseg Kseg ls.ls_rules }
          else default_seg_seg ( )
        else if IntMap.cardinal ls.ls_cur_l.g_g
            = IntMap.cardinal ls.ls_cur_r.g_g then
          let ls = fix_map_pargs "seg_seg,dst" ls s0.se_dargs s1.se_dargs in
          let ls = fix_map_sargs "seg_seg,dst" ls s0.se_dargs s1.se_dargs in
          let ls = wkseg_iargs "seg_seg,int" s0.se_sargs s0.se_dargs
              s1.se_sargs s1.se_dargs s0.se_ind ls in
          let ls_iseg_r =
            if s1.se_dargs.ia_int = [] then ls.ls_iseg_r
            else s1::ls.ls_iseg_r in
          collect_rules_node_st s0.se_dnode s1.se_dnode
            { ls with
              ls_cur_l = seg_edge_rem isl ls.ls_cur_l;
              ls_cur_r = seg_edge_rem isr ls.ls_cur_r;
              ls_iseg_r = ls_iseg_r;
              ls_rem_l = IntSet.add isl ls.ls_rem_l;
              ls_cur_i = Nemb.add s0.se_dnode s1.se_dnode ls.ls_cur_i;
              ls_rules = invalidate_rules isl isr Kseg Kseg ls.ls_rules }
        else
          default_seg_seg ( )
      else Log.fatal_exn "rule seg-seg, applied to distinct inductives"
  | _, _ -> Log.fatal_exn "rule seg-seg, not applied to seg-seg"

(* seg - ind [par ptr OK, par int KO] *)
let apply_seg_ind (isl: int) (isr: int) (ls: le_state): le_state =
  let nl = node_find isl ls.ls_cur_l in
  let nr = node_find isr ls.ls_cur_r in
  match nl.n_e, nr.n_e with
  | Hseg segl, Hind indr ->
      if Ind_utils.compare indr.ie_ind segl.se_ind = 0 then
        (* case: a*=b * G < a() * H   ==>   G < b() * H *)
        (* segment gets consumed in the left argument;
         * inductive gets split into a segment and an inductive in the right *)
        let ls = fix_map_pargs "seg_ind,src" ls segl.se_sargs indr.ie_args in
        let ls = fix_map_sargs "seg_ind,src" ls segl.se_sargs indr.ie_args in
        (* add a fresh (middle point) node in the right side graph *)
        let insrc, ls = fresh_map_id Ntaddr segl.se_dnode ls in
        (* add fresh nodes for the mapping of pointer destination arguments *)
        let lppars, lipars, lspars, ls = fresh_map_all_args segl.se_dargs ls in
        let se_args = { ia_ptr = lppars ;
                        ia_int = lipars;
                        ia_set = lspars; } in
        let ls =
          wkseg_iargs "seg_ind,int" segl.se_sargs segl.se_dargs indr.ie_args
            se_args segl.se_ind ls in
        (* build the fresh inductive edge and add it to the right side graph *)
        let ie =
          { ie_ind  = indr.ie_ind ;
            ie_args = { ia_ptr = lppars ;
                        ia_int = lipars;
                        ia_set = lspars; } } in
        collect_rules_node_st segl.se_dnode insrc
          { ls with
            ls_cur_l = seg_edge_rem isl ls.ls_cur_l;
            ls_cur_r = ind_edge_add insrc ie (ind_edge_rem isr ls.ls_cur_r);
            ls_fresh_seg_r =
            IntMap.add insrc ie ls.ls_fresh_seg_r;
            ls_rem_l = IntSet.add isl ls.ls_rem_l;
            ls_rules = invalidate_rules isl isr Kseg Kind ls.ls_rules }
      else Log.todo_exn "unhandled seg-ind case"
  | _, _ -> Log.fatal_exn "seg-ind; improper config"

(* void - seg [par ptr OK, par int KO] *)
let apply_void_seg (isl: int) (isr: int) (ls: le_state): le_state =
  let nr = node_find isr ls.ls_cur_r in
  match nr.n_e with
  | Hseg s1 ->
      let idr = s1.se_dnode in
      let ext_l =
        try Nemb.find idr ls.ls_cur_i
        with Not_found -> Log.fatal_exn "emp-seg: ext not mapped" in
      if ext_l = isl then (* segment successfully mapped to empty region *)
        (* pointer arguments are mapped to each other *)
        let ls =
          List.fold_left2
            (fun acc iars iard ->
              let ofind i =
                try Some (Nemb.find i acc.ls_cur_i)
                with Not_found -> None in
              match ofind iars, ofind iard with
              | None, None -> raise (Le_false "emp-seg, no ptr par info")
              | Some ial, None ->
                  { acc with ls_cur_i = Nemb.add iard ial acc.ls_cur_i }
              | None, Some ial ->
                  { acc with ls_cur_i = Nemb.add iars ial acc.ls_cur_i }
              | Some ias, Some iad ->
                  if ias = iad then acc
                  else raise (Le_false "emp-seg, conflicting ptr par info")
            ) ls s1.se_sargs.ia_ptr s1.se_dargs.ia_ptr in
        let setctr =
          List.fold_left2
            (fun acc iars iard ->
              S_eq (S_var iars, S_var iard) :: acc
            ) ls.ls_setctr_r
            s1.se_sargs.ia_set s1.se_dargs.ia_set in
        let intctr =
          List.fold_left2
            (fun acc iars iard ->
              Nc_cons (Apron.Tcons1.EQ, Ne_var iars, Ne_var iard) :: acc
            ) ls.ls_ctr_r
            s1.se_sargs.ia_int s1.se_dargs.ia_int in
        { ls with
          ls_setctr_r = setctr;
          ls_ctr_r    = intctr;
          ls_cur_r = seg_edge_rem isr ls.ls_cur_r ;
          ls_rules = invalidate_rules isl isr Kemp Kseg ls.ls_rules }
      else (* segment not mapped into an empty region *)
        Log.todo_exn "segment to non empty: %s=%s> %d"
          s1.se_ind.i_name s1.se_ind.i_name s1.se_dnode
  | _ -> Log.fatal_exn "void-seg; improper config"

(* stop rule [par ptr OK, par int KO]
 *   this rule is specific to inductive edge search
 *   when a stop node is encountered (to limit weakening depth) *)
let apply_stop_node_ind (isl: nid) (isr: nid) (ls: le_state): le_state=
  (* We may discard the node left in the right graph, and
   * propagate it as a remainder in the right graph!
   * then, if all remainder is of the form  x.i()  it means
   * we may synthesize a (strong) implication edge.
   * To achieve that, we move right inductive edge into a
   * placeholder (ls_excl_l), to be checked at the end. *)
  if debug_module then
    Log.debug "IsLe: reached a stop node, about to stop";
  let nr = node_find isr ls.ls_cur_r in
  match nr.n_e with
  | Hemp | Hpt _ ->
      (* do nothing in this case for now; not sure what to do *)
      ls
  | Hind icr ->
      assert_no_int_arg "stop(ind)" icr.ie_args ;
      let nexcl =
        (* mapping of the pointer arguments *)
        let pargs =
          List.map
            (fun i ->
              if debug_module then
                Log.debug "Trying to map %d" i;
              try Nemb.find i ls.ls_cur_i
              with Not_found -> Log.fatal_exn "stop-node: ptr par not mapped"
            ) icr.ie_args.ia_ptr in
        (* mapping of the integer arguments *)
        let iargs =
          List.map
            (fun i ->
              if debug_module then
                Log.debug "Trying to map %d" i;
              try Nemb.find i ls.ls_cur_i
              with Not_found -> Log.fatal_exn "stop-node: ptr par not mapped"
            ) icr.ie_args.ia_int in
        (* mapping of the set arguments*)
        let sargs =
          List.map
            (fun i ->
              if debug_module then
                Log.debug "Trying to map %d" i;
              try IntSet.choose (Set_utils.Semb.find i ls.ls_cur_si)
              with Not_found -> Log.fatal_exn "stop-node: ptr par not mapped"
            ) icr.ie_args.ia_set in
        let args = { ia_ptr = pargs ;
                     ia_int = iargs ;
                     ia_set = sargs } in
        let g0 = sv_add isl nr.n_t Nnone ls.ls_excl_l in
        let g1 =
          List.fold_left
            (fun accg i -> sv_add i Ntaddr Nnone g0) g0 pargs in
        if debug_module then
          Log.debug "Excl:\n%s" (graph_2stri "  " g1);
        let ie = { ie_ind  = icr.ie_ind ;
                   ie_args = args } in
        ind_edge_add isl ie g1 in
      { ls with
        ls_cur_r  = ind_edge_rem isr ls.ls_cur_r ;
        ls_excl_l = nexcl }
  | Hseg _ ->
      Log.todo_exn "apply_stop_node_ind: segment"


(** Post inclusion check routine *)
(* Checks whether a configuration is a success configuration *)
let is_success (ls: le_state): le_state =
  let num_l = num_edges ls.ls_cur_l in
  let num_r = num_edges ls.ls_cur_r in
  if !Flags.flag_debug_is_le_shape then
    Log.force
      "%sReturn from is_le: %d | %d" (pp_le_state ls) num_l num_r;
  if (not ls.ls_emp_both || num_l = 0) && num_r = 0 then
    (* Inclusion established in the graph domain;
     * we now need to look at side predicates *)
    (* first: collect unmapped sv from constraints on right side *)
    let f_unmap (i: int) (acc: IntSet.t) =
      if Nemb.mem i ls.ls_cur_i then acc else IntSet.add i acc in
    let non_mapped_svs_r =
      List.fold_left
        (fun acc ctr ->
          Nd_utils.n_cons_fold f_unmap ctr acc
        ) IntSet.empty ls.ls_ctr_r in
    (* for all the non mapped svs in right side, map them to generated fresh
     * svs in left side *)
    let ls =
      IntSet.fold
        (fun sv ls ->
          let typ = (IntMap.find sv ls.ls_cur_l.g_g).n_t in
          let il, g = sv_add_fresh typ Nnone ls.ls_cur_l in
          { ls with
            ls_cur_l  = g;
            ls_fsvs_l = IntSet.add il ls.ls_fsvs_l;
            ls_cur_i  = Nemb.add sv il ls.ls_cur_i }
        ) non_mapped_svs_r ls in
    (* now, rename all the constraints on right side (ls_ctr_r) to constraints
     * on left side (ls_ctr_l) *)
    let ls = List.fold_left (fun ls ctr ->
        try
          let ctr =
            Nd_utils.n_cons_map (fun i -> Nemb.find i ls.ls_cur_i) ctr in
          { ls with ls_ctr_l = ctr :: ls.ls_ctr_l }
        with
          Not_found -> Log.fatal_exn "nd_instantiation: non_complete sv map"
      ) ls (List.rev ls.ls_ctr_r) in
    let ls = {ls with ls_ctr_r = [];} in
    if !Flags.flag_debug_is_le_shape then
      begin
        Log.force "Predicates to look at: %d" (List.length ls.ls_ctr_l);
        List.iter
          (fun p -> Log.force "  %s" (Nd_utils.n_cons_2str p))
          ls.ls_ctr_l;
        Log.force "Instantiable svs: %s"
          (IntSet.t_2str ";" ls.ls_fsvs_l);
        Log.force "Instantiated svs: %s"
          (IntMap.t_2str "\n" Nd_utils.n_expr_2str ls.ls_inst_l);
      end;
    (* seperate constraints on left side into two parts: a part without
       fresh svs, which should be proved satisfied and a part with fresh
       svs, which can be should for instantiate fresh svs *)
    let ctr_to_prove, ctr_to_inst = List.fold_left (fun (accp, acci) ctr ->
        let no_freshsvs =
          Nd_utils.n_cons_fold
            (fun i acc -> if IntSet.mem i ls.ls_fsvs_l then false else acc)
            ctr true in
        if no_freshsvs then ctr::accp, acci
        else accp, ctr::acci
      )([], []) ls.ls_ctr_l in
    let ls = {ls with ls_ctr_l = ctr_to_inst} in
    (* instantiation fresh svs according to constraints on left side *)
    let inst, ctr_to_prove1, ctr_to_inst =
      nd_instantiation_eq ls.ls_ctr_l ls.ls_fsvs_l ls.ls_inst_l in
    let ctr_to_prove = ctr_to_prove @ ctr_to_prove1 in
    let ls = { ls with
               ls_inst_l = inst;
               ls_ctr_l  = ctr_to_inst } in
    (* update node mapping and instantiation *)
    let f_l2r (l: int) (j: int) (nm: node_embedding): node_embedding =
      let r =
        IntMap.fold (fun k e acc -> if e = l then IntMap.add k j acc else acc)
          nm.n_img nm.n_img in
      { nm with n_img = r } in
    let e_l2r (l: int) (nm: node_embedding): int option =
      let r = IntMap.filter (fun k e -> e = l) nm.n_img in
      try Some (fst (IntMap.choose r))
      with Not_found -> None in
    let ls_cur_i =
      IntMap.fold
        (fun i e cur_i ->
          match e with
          | Ne_var j -> f_l2r i j cur_i
          | _ ->
              begin
                match e_l2r i cur_i with
                | None ->  cur_i
                | Some j -> cur_i
              end
        ) inst ls.ls_cur_i in
    let ls = { ls with ls_cur_i = ls_cur_i } in
    (* Discharging of proof obligations *)
    let l_rem =
      List.fold_left
        (fun acc lctr ->
          let bres = ls.ls_sat_l lctr in
          if !Flags.flag_debug_is_le_shape then
            Log.force "Verifying constraint on left node: %s => %b"
              (Nd_utils.n_cons_2str lctr) bres;
          if bres then acc
          else lctr :: acc
        ) [ ] ctr_to_prove in
    let l_rem =
      List.fold_left
        (fun acc lctr ->
          let bres =
            match lctr with
            | Nc_cons (Apron.Tcons1.DISEQ, Ne_var i, Ne_var j) ->
                ls.ls_gl_diseq i j
            | _ -> false in
          if !Flags.flag_debug_is_le_shape then
            Log.force "Verifying constraint on left node: %s => %b"
              (Nd_utils.n_cons_2str lctr) bres;
          if bres then acc
          else lctr :: acc
        ) [ ] l_rem in
    { ls with
      ls_ctr_r    = [ ] ; (* accumulator becomes empty *)
      ls_success  = (List.length l_rem = 0) ; }
  else (* Inclusion could not be established in the graph domain *)
    { ls with ls_success  = false }


(** The new inclusion algorithm, with refactored strategy application *)
(* This function is based on a recursive algorithm
 * implementing a worklist on applicable rules (not
 * nodes or edges!) *)
let rec s_is_le_rec (ls: le_state): le_state =
  (* Find out the next rule to apply *)
  match rules_next ls.ls_rules with
  | None ->
      (* indicates there are no remaing rules to apply (we are finished) *)
      (* or maybe we should look for a stop node *)
      if !Flags.flag_debug_is_le_shape then
        Log.force "IsLe-NoRule:\n%s" (pp_le_state ls);
      ls
  | Some (k, (il, ir), rem_rules) ->
      (* ir is a real node unless k = Rstop *)
      assert (k = Rstop || ir >= 0);
      if !Flags.flag_debug_is_le_shape then
        begin
          Log.force "%sIsLe-Treating (%d,%d): %s" (pp_le_state ls) il ir
            (rkind_2str k);
          if !Flags.flag_debug_is_le_strategy then
            Log.force "isle-nodes to treat:\n%s" (rules_2str ls.ls_rules)
        end;
      let ls0 = { ls with ls_rules = rem_rules } in
      let ls1 =
        match k with
        (* Stop *)
        | Rstop -> apply_stop_node_ind il ir ls0
        (* Rules that should be reduced *)
        | Rpp -> apply_pt_pt   il ir ls0
        | Rii -> apply_ind_ind il ir ls0
        | Rss -> apply_seg_seg il ir ls0
        | Rsi -> apply_seg_ind il ir ls0
        | Rvs -> apply_void_seg il ir ls0
        (* Unfold rules *)
        | Rei -> s_is_le_unfold true il ir ls0
        | Rps
        | Rpi ->
            try
              s_is_le_unfold false il ir ls0
            with
            | Le_false "unfold: no successful branch" ->
                s_is_le_unfold true il ir ls0 in
      s_is_le_rec ls1
and s_is_le_unfold
    (hint_empty: bool) (* whether to consider empty rules first or last*)
    (il: nid) (ir: nid) (ls: le_state): le_state =
  if !Flags.flag_debug_is_le_shape then
    Log.force "IsLe triggerring unfolding<%b>" hint_empty;
  let l_mat =
    Graph_materialize.materialize_ind ~submem:ls.ls_submem
      (Some hint_empty) false false ir ls.ls_cur_r in
  if !Flags.flag_debug_is_le_shape then
    Log.force "IsLe performed unfolding: %d" (List.length l_mat);
  let els =
    List.fold_left
      (fun acc ur ->
        (* only the empty rule of the segment materialization will yield
         * equalities to reduce immediately, and we should not get any here *)
        assert (ur.ur_eqs = PairSet.empty);
        match acc with
        | Some _ ->
            (* inclusion already found, no other check *)
            acc
        | None ->
            (* inclusion not found yet; we try current disjunct *)
            if !Flags.flag_debug_is_le_shape then
              List.iter
                (fun ctr ->
                  Log.force "Predicate to prove on right nodes: %s"
                    (Nd_utils.n_cons_2str ctr)
                ) ur.ur_cons;
            try
              let ls0 =
                collect_rules_node_st il ir
                  { ls with
                    ls_cur_r = ur.ur_g ;
                    ls_ctr_r = ur.ur_cons @ ls.ls_ctr_r;
                    ls_setctr_r = ur.ur_setcons @ ls.ls_setctr_r;
                  } in
              let ols = s_is_le_rec ls0 in
              let lsuccess = is_success ols in
              if lsuccess.ls_success then
                Some lsuccess
              else
                None
            with
            | Le_false msg ->
                if !Flags.flag_debug_is_le_shape then
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


(** The main inclusion testing functions *)
(* Basically, trigger the functions above *)
let rec is_le_start (ls: le_state): le_state option =
  (* Iteration *)
  let ols = s_is_le_rec ls in
  (* Computation of the inclusion check result *)
  let lls = is_success ols in
  if lls.ls_success then
    (* inclusion holds, relation gets forwarded *)
    Some lls
  else
    (* inclusion does not hold, no relation to forward *)
    None

(* The main function for inclusion testing
 *  - inst:
 *    the first argument allows for parameters be marked as instantiable
 *    in the right hand side of an inclusion check performed to enable a
 *    weakening (e.g. in join)
 *  - stop:
 *    allows to use the liveness analysis results in order to guide the
 *    weakening process
 *)
let is_le_generic
    (instantiable_nodes: IntSet.t option) (* nodes that may be instantiated *)
    ~(submem: bool)      (* whether sub-memory is_le (no alloc check) *)
    (emp_both: bool)     (* whether both arguments should be fully emptied *)
    (ho: hint_ug option) (* hint, the left argument ("stop" nodes) *)
    (es: IntSet.t)       (* segment end(s), if any *)
    (xl: graph)          (* left input *)
    (pl: n_cons -> bool) (* satisfiability, in the left argument *)
    (spl: set_cons -> bool) (* set satisfiability, in the left argument *)
    (xr: graph)          (* right input *)
    (r: node_emb)        (* injection from right into left *)
    (* injection from right set variables into left set variables *)
    (s_r: Graph_sig.node_emb)
    : le_state option (* extended relation if inclusion proved *) =
  try
    (* Initialization *)
    let lh = Option.map (fun x -> x.hug_live) ho in
    let ni = Nemb.init r in
    let si = Set_utils.Semb.init s_r in
    let ils = { ls_cur_l    = xl ;
                ls_cur_r    = xr ;
                ls_cur_i    = ni ;
                ls_cur_si   = si;
                ls_rules    = rules_init emp_both es ni xl xr r ;
                ls_rem_l    = IntSet.empty ;
                ls_sat_l    = pl ;
                ls_setsat_l = spl;
                ls_ctr_l    = [ ];
                ls_fsvs_l   = IntSet.empty;
                ls_inst_l   = IntMap.empty;
                ls_iseg_r   = [ ];
                ls_fresh_seg_r = IntMap.empty;
                ls_ctr_r    = [ ] ;
                ls_setctr_r = [ ] ;
                ls_success  = false ;
                ls_emp_both = emp_both;
                ls_hint_l   = lh;
                ls_excl_l   = (graph_empty xl.g_inds);
                ls_end_seg  = es;
                ls_submem   = submem;
                ls_gl_diseq = sat_graph_diseq xl; } in
    (* Temporary *)
    if !Flags.flag_debug_is_le_shape then
      begin
        match ho with
        | None -> Log.force "IsLe: no hint"
        | Some h -> Log.force "IsLe: { %s }"
                      (Aa_sets.t_2str "; " string_of_int h.hug_live)
      end;
    (* Launch *)
    if not !very_silent_mode then
      Log.info "\n\n[IGraph]  start is_le\n\n";
    let ob = is_le_start ils in
    if not !very_silent_mode then
      Log.info "[IGraph]  return is_le %b" (ob != None);
    ob
  with
  | Le_false msg ->
      if not !very_silent_mode then
        Log.force "[IGraph]  is_le fails on exception: %s" msg;
      None


(* for some non-instantiated set variables, generate freash set variables
 for instantiation *)
let gen_fresh_inst (non_inst: IntSet.t) (inst: set_expr IntMap.t) (t: graph)
    : set_expr IntMap.t * graph  * IntSet.t=
  IntSet.fold
    (fun e (inst, t, ns) ->
      assert (not (IntMap.mem e inst));
      let key, t = setv_add_fresh false None t in
      IntMap.add e (S_var key) inst, t, IntSet.add key ns
    ) non_inst (inst, t, IntSet.empty)

(* split set constraints with fresh set variables *)
let split_cons_fresh (setctr: set_cons list) (setv: IntSet.t)
    : set_cons list * set_cons list =
  List.fold_left
    (fun (accs, acc_f) ele ->
      if IntSet.inter setv (Set_utils.set_cons_setvs ele) = IntSet.empty then
        ele :: accs, acc_f
      else
        accs, ele :: acc_f
    ) ([], []) setctr

(* instantiation of set variables in is_le  *)
let set_instantiation (ls: le_state) (g: graph)
    : le_state * set_expr IntMap.t *set_cons list * set_cons list * IntSet.t =
  (* initialize instantiation of set variables from set mapping and
   * generate equal set constraints that need to be proved *)
  let inst, setcons_l = gen_eq_setctr ls.ls_cur_si in
  (* first instantiation pass, which only produce new instantiation according
   * to initialize instantiation, this pass will not generate fresh set
   * variables on the left side *)
  let inst, setcons = instantiate ls.ls_setctr_r inst ls.ls_cur_i.n_img in
  (* compute a minimal set of non instantiated set variables,
   * that instantiating them could lead to a complete instantiation*)
  let non_inst = check_non_inst setcons inst in
  (* map minimal  non instantiated set variables to fresh set variables in
   * the left side *)
  let inst, ls_cur_l, nset = gen_fresh_inst non_inst inst ls.ls_cur_l in
  let ls = { ls with ls_cur_l = ls_cur_l } in
  (* second instantiation pass, produce a complete instantiation and
   * set constraints that need to be proved *)
  let inst, setcons = instantiate setcons inst ls.ls_cur_i.n_img in
  (* rename set constraints to the left side according to instantiation *)
  let setcons_l1 = replace_cons setcons inst ls.ls_cur_i.n_img in
  (* remove set variables from unfolding during inclusion checking*)
  let inst = IntMap.filter (fun k _ -> Keygen.key_is_used g.g_setvkey k) inst in
  let set_cons_l = setcons_l@setcons_l1 in
  (* filter set constraints with fresh set variables as they cannot be
   * proved, need further instantiation in joining *)
  let set_cons_l, further_prove = split_cons_fresh set_cons_l nset in
  ls, inst, set_cons_l, further_prove, nset

(* guess constraints among set parameters and numerical parameters
 * input graph *)
let guess_cons (xl: graph) (ls: le_state): le_state =
  if !Flags.flag_debug_is_le_shape then
    Log.force "begin: Guess_cons";
  let ls_iind_l =
    List.map
      (fun se ->
        let id = Nemb.find se.se_dnode ls.ls_cur_i in
        let ie =
          let ptrs =
            List.map (fun i -> Nemb.find i ls.ls_cur_i) se.se_dargs.ia_ptr in
          let ints =
            List.map (fun i -> Nemb.find i ls.ls_cur_i) se.se_dargs.ia_int in
          let sets =
            List.map (fun i -> IntSet.choose (Semb.find i ls.ls_cur_si))
              se.se_dargs.ia_set in
          { ie_ind  = se.se_ind;
            ie_args = { ia_ptr = ptrs;
                        ia_int = ints;
                        ia_set = sets } } in
        (id, ie)
      ) ls.ls_iseg_r in
  let merge_g (gi: graph) (go: graph): graph =
    let g =
      IntMap.fold
        (fun id node acc ->
          if IntMap.mem id acc then acc
          else IntMap.add id node acc
        ) go.g_g gi.g_g in
    { gi with
      g_nkey   = go.g_nkey;
      g_g      = g;
      g_svemod = go.g_svemod } in
  let creat_g (id: int) (ie: ind_edge): graph =
    let g0 = sv_add id Ntaddr Nnone (graph_empty xl.g_inds) in
    let f_buildpars = List.fold_left (fun acc i -> IntSet.add i acc) in
    let ia_nodes = f_buildpars IntSet.empty ie.ie_args.ia_int in
    let pa_nodes = f_buildpars IntSet.empty ie.ie_args.ia_ptr in
    let sa_nodes = f_buildpars IntSet.empty ie.ie_args.ia_set in
    let g0 = IntSet.fold (fun i -> sv_add i Ntint Nnone) ia_nodes g0 in
    let g0 = IntSet.fold (fun i -> sv_add i Ntaddr Nnone) pa_nodes g0 in
    let g0 = IntSet.fold (fun i -> setv_add false i) sa_nodes g0 in
    ind_edge_add id ie g0 in
  let init_inj (id: int) (ie: ind_edge): node_embedding * setv_embedding =
    let nm = Nemb.add id id Nemb.empty in
    let nm =
      List.fold_left (fun acc i -> Nemb.add i i acc) nm ie.ie_args.ia_ptr in
    let nm =
      List.fold_left (fun acc i -> Nemb.add i i acc) nm ie.ie_args.ia_int in
    let sm =
      List.fold_left
        (fun acc i -> Semb.add i i acc) Semb.empty ie.ie_args.ia_set in
    nm, sm in
  List.fold_left
    (fun ls (id, ie) ->
      if ie.ie_args.ia_int = [] then ls
      else
        let ls_cur_i, ls_cur_si = init_inj id ie in
        let ls_cur_l = merge_g xl ls.ls_cur_l in
        let ls_cur_r = creat_g id ie in
        let ls_a =
          { ls with
            ls_cur_l       = ls_cur_l;
            ls_cur_r       = ls_cur_r;
            ls_cur_i       = ls_cur_i;
            ls_cur_si      = ls_cur_si;
            ls_rules       = empty_rules;
            ls_ctr_r       = [];
            ls_setctr_r    = [];
            ls_iseg_r      = [];
            ls_fresh_seg_r = IntMap.empty;
            ls_success     = false;
            ls_emp_both    = false; } in
        let ls_a = collect_rules_node_st id id ls_a in
        match is_le_start ls_a with
        | Some lls -> lls
        | None -> ls
    ) ls ls_iind_l

let do_types (xr: graph) (ls: le_state): int_wk_typ IntMap.t =
  (* type integer parameters on right graph *)
  let type_iargs_r = type_iargs_g xr (fun ir -> Nemb.find ir ls.ls_cur_i) in
  let type_iargs_l =
    IntMap.fold
      (fun ir wk acc ->
        let il = Nemb.find ir ls.ls_cur_i in
        if IntSet.mem il ls.ls_fsvs_l then
          try IntMap.add il (merge_wktype (IntMap.find il acc) wk) acc
          with Not_found -> IntMap.add il wk acc
        else acc
      ) type_iargs_r IntMap.empty in
  IntMap.fold
    (fun id ie acc ->
      let wkt = seg_end_wkt ie.ie_ind.i_pars_wktyp.int_typ in
      type_iargs_ie ie.ie_args wkt acc
    ) ls.ls_fresh_seg_r type_iargs_l


(* The main function for inclusion testing:
 * used for checking stabilization of abstract iterates
 *
 *  - stop:
 *    allows to use the liveness analysis results in order to guide the
 *    weakening process
 *)
let is_le
    ~(submem: bool)      (* whether sub-memory is_le (no alloc check) *)
    (xl: graph)          (* left input *)
    (ho: hint_ug option) (* hint, the left argument ("stop" nodes) *)
    (pl: n_cons -> bool) (* satisfiability, in the left argument *)
    (spl: set_cons -> bool) (* set satisfiability, in the left argument *)
    (xr: graph)          (* right input *)
    (r: node_emb)        (* injection from right into left *)
    (s_r: node_emb)        (* injection from right set vars into left *)
    : (int IntMap.t       (* extended relation if inclusion proved *)
         * set_expr IntMap.t (* instantiated constraints of SETVs *)
         * sv_inst           (* sv instantiation  *)
      ) option  =
  match is_le_generic None submem true ho IntSet.empty xl pl spl xr r s_r with
  | None -> None
  | Some ls ->
    if num_edges ls.ls_excl_l = 0 then
      let ls_r = guess_cons xl ls in
      let ls = { ls with
                 ls_ctr_l  = ls_r.ls_ctr_l;
                 ls_fsvs_l = ls_r.ls_fsvs_l;
                 ls_inst_l = ls_r.ls_inst_l } in
      (* sv instantiation according to eq numerical constraints *)
      let ie =
        IntMap.fold (fun k _ acc -> IntSet.add k acc)
          ls.ls_inst_l IntSet.empty in
      let sv_inst =
        { sv_inst_empty with
          sv_fresh = ls.ls_fsvs_l;
          sv_ie    = ie;
          sv_eqs   = ls.ls_inst_l;
          sv_cons  = ls.ls_ctr_l; } in
      let sv_inst = sv_instantiation sv_inst ls.ls_sat_l in
      let sv_inst = do_sv_inst_left_ctrs sv_inst ls.ls_sat_l in
      let typed_fresh_svl = do_types xr ls in
      let sv_inst =
        typed_sv_instantiation sv_inst typed_fresh_svl ls.ls_sat_l in
        assert (sv_inst.sv_cons = []);
      if !Flags.flag_debug_is_le_shape then
        Log.force "Instantiation of symbolic variables:\n%s"
          (sv_inst_2stri "" sv_inst);
      let ls = { ls with
                 ls_inst_l = sv_inst.sv_eqs;
                 ls_ctr_l = sv_inst.sv_cons } in
      let ls, inst, set_cons_l, further_prove, fresh_setv =
        set_instantiation ls xr in
      if !Flags.flag_debug_is_le_shape then
        Log.force "Instantiation of set variables:\n%s"
          (IntMap.fold
             (fun i sr acc ->
               Printf.sprintf "%sS[%d]->%s\n" acc i
                 (Set_utils.set_expr_2str sr)
             ) inst "");
      if List.for_all ls.ls_setsat_l set_cons_l
          && further_prove = [] && fresh_setv = IntSet.empty then
        Some (ls.ls_cur_i.n_img, inst, sv_inst)
      else None
    else Log.fatal_exn "is_le did not completely consume right argument"


(* Partial inclusion test:
 * used for weakening graphs (join, directed_weakening, graph_abs)
 * used for verifying assertions
 *
 * used for weakening graphs (join, directed_weakening, graph_abs)
 *  - inst:
 *    nodes that can be instantiated are the integer parameters in the right
 *    hand side (they are used for weakening)
 *  - stop:
 *    allows to use the liveness analysis results in order to guide the
 *    weakening process
 *)
let is_le_partial
    (instantiable_nodes: IntSet.t option) (* nodes that may be instantiated *)
    (search_ind: bool)   (* whether to search for an inductive / a segment *)
    ~(submem: bool)      (* whether sub-memory is_le (no alloc check) *)
    (xl: graph)          (* left input *)
    (ho: hint_ug option) (* hint, the left argument ("stop" nodes) *)
    (es: IntSet.t)       (* segment end(s), if any *)
    (pl: n_cons -> bool) (* satisfiability, in the left argument *)
    (spl: set_cons -> bool) (* set satisfiability, in the left argument *)
    (xr: graph)          (* right input *)
    (r: node_emb)        (* injection from right into left *)
    (s_r: node_emb)        (* injection from right set vars into left *)
    : is_le_res (* result, left remainder, and possibly right segment *) =
  match
    is_le_generic instantiable_nodes submem false ho es xl pl spl xr r s_r with
  | None -> Ilr_not_le
  | Some ls ->
      if search_ind then
        (* Tries to extract *one* *inductive* edge from graph *)
        match ind_edge_extract_single ls.ls_excl_l with
        | many, None ->
            (* all the right argument was consumed
             * likely means an inductive edge will be synthesized *)
            if !Flags.flag_debug_weak_abs then
              Log.force "IsLe partial: inductive found";
            if many then
              Log.fatal_exn
                "IsLe partial for local abstraction; a lot of stuff left"
            else (* left graph is empty, weaken to ind succeeded *)
              Ilr_le_ind ls.ls_cur_l
        | b, Some (ir, ie) ->
            if b then
              begin
                (* there was more than a single inductive edge left
                 * or other edges remained; this is a failure case *)
                if !Flags.flag_debug_weak_abs then
                  Log.force "IsLe partial: several inductives ?";
                Ilr_not_le
              end
            else
              (* there was exactly one inductive edge left to match
               * likely means a segment will be synthesized *)
              begin
                if !Flags.flag_debug_weak_abs then
                  Log.force "IsLe partial: segment found";
                Ilr_le_seg (ls.ls_cur_l, ir, ie, ls.ls_cur_i.n_img)
              end
      else
        begin
          (* sv instantiation according to eq numerical constraints *)
          let ie =
            IntMap.fold (fun k _ acc -> IntSet.add k acc) ls.ls_inst_l
              IntSet.empty in
          let sv_inst =
            { sv_inst_empty with
              sv_fresh = ls.ls_fsvs_l;
              sv_ie    = ie;
              sv_eqs   = ls.ls_inst_l;
              sv_cons  = ls.ls_ctr_l; } in
          let sv_inst  = sv_instantiation sv_inst ls.ls_sat_l in
          if !Flags.flag_debug_is_le_shape then
            Log.force "Instantiation of symbolic variables:\n%s"
              (sv_inst_2stri "" sv_inst);
          let ls = { ls with
                     ls_inst_l = sv_inst.sv_eqs;
                     ls_ctr_l  = sv_inst.sv_cons } in
          let ls, inst, set_cons_l, further_prove, fresh_setv =
            set_instantiation ls xr in
          if !Flags.flag_debug_is_le_shape then
            Log.force "Instantiation of set variables:\n%s"
              (IntMap.fold
                 (fun i sr acc ->
                   Printf.sprintf "%sS[%d]->%s\n" acc i
                     (Set_utils.set_expr_2str sr)
                 ) inst "");
          if !Flags.flag_debug_is_le_shape then
            Log.force "Set predicates to prove:\n%s\n"
              (gen_list_2str "" Set_utils.set_cons_2str ";" set_cons_l);
          if !Flags.flag_debug_is_le_shape then
            Log.force "Set predicates for further prove:\n%s\n"
              (gen_list_2str "" Set_utils.set_cons_2str ";" further_prove);
          (* prove set predicates *)
          if List.for_all ls.ls_setsat_l set_cons_l then
            Ilr_le_rem (ls.ls_cur_l, ls.ls_rem_l, ls.ls_cur_i.n_img,
                        inst, fresh_setv, sv_inst, further_prove)
          else
            Ilr_not_le
        end
