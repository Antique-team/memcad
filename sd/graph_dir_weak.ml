(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_dir_weak.ml
 **       experimental graph "graph directed weakening" algorithm
 **       - takes two arguments;
 **       - weakens only the second argument
 **       (the first one would be preserved as unroll)
 ** Xavier Rival, 2012/03/29 *)
open Data_structures
open Flags
open Lib

open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig

open Graph_utils
open Ind_utils
open Inst_utils


(** Error report *)
module Log =
  Logger.Make(struct let section = "g_dweak_" and level = Log_level.DEBUG end)


(** Limitations:
 **  - some unimplemented rules
 **  - parameters not handled everywhere *)


(** Abort and backtrack *)
exception Abort_rule of string


(** Applicable rules *)
(* Not done yet: Rsegest, Rindintro *)
type rkind =
  | Rpp | Rii (* matching of pairs of pt/inductive edges *)
  | Rsegintro (* introduction of a segment *)
  | Riweak    (* inductive in the left; weaken in the right graph *)
let kind_2str: rkind -> string = function
  | Rpp       -> "pt-pt"
  | Rii       -> "ind-ind"
  | Rsegintro -> "seg-intro"
  | Riweak    -> "ind-weak"
type instances = PairSet.t (* for now *)
type rules =
    { r_pt_prio:  instances ; (* prioretary points-to edges *)
      r_pt_pt:    instances ; (* matching a pair of points-to edges *)
      r_ind_ind:  instances ; (* matching a pair of inductive edges *)
      r_ind_weak: instances ; (* weaken into an inductive (right) *)
      r_segintro: instances ; (* introduction of a segment *) }
let rules_2str (r: rules): string =
  let instances_2str (name: string) (s: PairSet.t): string =
    if s != PairSet.empty then
      Printf.sprintf "%s %s\n" name (pairset_2str s)
    else "" in
  (instances_2str "pt-prio:  " r.r_pt_prio)
  ^ (instances_2str "pt-pt:    " r.r_pt_pt)
  ^ (instances_2str "ind-ind:  " r.r_ind_ind)
  ^ (instances_2str "ind-weak: " r.r_ind_weak)
  ^ (instances_2str "seg-intro:" r.r_segintro)


(** State of the algorithm *)
type dw_config =
    { (** Aguments *)
      (* Graphs (left and right) *)
      dw_inl:     graph;
      dw_inr:     graph;
      (* Satisfaction of boolean predicates *)
      dw_satr:    (n_cons -> bool);
      (** Iteration strategy *)
      dw_rules:   rules;
      (** Relations among arguments *)
      dw_rel:     node_wkinj;
      (** Outputs *)
      (* Output under construction *)
      dw_out:     graph }


(** Operations on configuration: managing worklists, mappings *)
(* Find the result SV corresponding to a pair of nodes in the
 * arguments if it exists;
 * if there is no such image SV, allocate one and return it together
 * with the extended configuration *)
let find_in_config (p: int * int) (dw: dw_config): dw_config * int =
  try dw, Nwkinj.find dw.dw_rel p
  with Not_found ->
    let alloc, typ =
      try
        let nl = node_find (fst p) dw.dw_inl in
        let nr = node_find (snd p) dw.dw_inr in
        let a = if nl.n_alloc = nr.n_alloc then nl.n_alloc else Nnone in
        let t =
          if nl.n_t = nr.n_t then nl.n_t
          else
            begin
              Log.info "DirWeak, nodes have different types: %s %s"
                (ntyp_2str nl.n_t) (ntyp_2str nr.n_t);
              Ntraw
            end in
        a, t
      with
      | _ ->
          Log.info "DirWeak find_in_config: no info; synthesize some";
          Nnone, Ntraw in
    let ni, nout = sv_add_fresh typ alloc dw.dw_out in
    let nrel = Nwkinj.add dw.dw_rel p ni in
    { dw with
      dw_out = nout ;
      dw_rel = nrel }, ni
(* Read in node relation; will not modify it (crash if not there) *)
let read_in_config (p: int * int) (dw: dw_config): int =
  try Nwkinj.find dw.dw_rel p
  with Not_found -> Log.fatal_exn "read_in_config"


(** Management of applicable rules *)
(* Empty rules (for initialization) *)
let empty_rules = { r_pt_prio  = PairSet.empty ;
                    r_pt_pt    = PairSet.empty ;
                    r_ind_ind  = PairSet.empty ;
                    r_ind_weak = PairSet.empty ;
                    r_segintro = PairSet.empty }
(* Computes the next applicable rules at a node *)
let collect_rules_node_gen
    (is_prio: int * int -> bool) (* whether pt rules are prioritary (init) *)
    (il: int) (ir: int) (* nodes in both inputs *)
    (dw: dw_config): dw_config =
  Log.info "searching for rules at %d,%d" il ir;
  let nl = node_find il dw.dw_inl in
  let nr = node_find ir dw.dw_inr in
  (* Searching for siblings (only in the right graph) *)
  let detect_siblings (i: int) (j: dw_config): dw_config =
    let s =
      try IntMap.find i dw.dw_rel.wi_l_r
      with Not_found -> IntSet.empty in
    Log.info "siblings search at %d: %d" i (IntSet.cardinal s);
    if IntSet.cardinal s > 1 then
      begin
        Log.info "Siblings found at %d (%d)" i (IntSet.cardinal s);
        let l =
          IntSet.fold (fun j -> PairSet.add (i, j)) s dw.dw_rules.r_segintro in
        { dw with
          dw_rules = { dw.dw_rules with
                       r_segintro = l } }
      end
    else j in
  let dw = detect_siblings il dw in
  (* Regular rules *)
  let nrules =
    let acc = dw.dw_rules in
    match nl.n_e, nr.n_e with
    (* empty nodes, no rule to add *)
    | Hemp  , Hemp   -> acc
    (* usual atomic rules *)
    | Hpt  _, Hpt  _ ->
        if is_prio (il, ir) then
          { acc with r_pt_prio = PairSet.add (il, ir) acc.r_pt_prio }
        else
          { acc with r_pt_pt = PairSet.add (il, ir) acc.r_pt_pt }
    | Hind _, Hind _ ->
        { acc with r_ind_ind = PairSet.add (il, ir) acc.r_ind_ind }
    | Hind _, Hemp
    | Hind _, Hpt  _ ->
        { acc with r_ind_weak = PairSet.add (il, ir) acc.r_ind_weak }
    (* other cases currently not handled *)
    | _, _ ->
        Log.warn "dweak: %s-%s"
          (heap_frag_2strc nl.n_e) (heap_frag_2strc nr.n_e);
        acc in
  { dw with dw_rules = nrules }
let collect_rules_node (il: int) (ir: int) (dw: dw_config): dw_config =
  collect_rules_node_gen (fun _ -> false) il ir dw
(* Computes the set of rules at initialization *)
let init_rules (fhint: int * int -> bool) (dw: dw_config): dw_config =
  PairMap.fold
    (fun (il, ir) _ ->
      collect_rules_node_gen fhint il ir
    ) dw.dw_rel.wi_lr_o dw
(* Strategy function; returns the next applicable rule *)
(* current strategy:
 *  1. pt-prio
 *  2. ind-ind
 *  3. seg-intro
 *  4. [ there should be seg-ext here ]
 *  5. weak-ind, ind-weak
 *  6. pt-pt *)
let rules_next (r: rules): (rkind * (int * int) * rules) option =
  if r.r_pt_prio != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_prio in
    Some (Rpp, p, { r with r_pt_prio = PairSet.remove p r.r_pt_prio })
  else if r.r_ind_ind != PairSet.empty then
    let p = PairSet.min_elt r.r_ind_ind in
    Some (Rii, p, { r with r_ind_ind = PairSet.remove p r.r_ind_ind })
  else if r.r_segintro != PairSet.empty then
    let p = PairSet.min_elt r.r_segintro in
    Some (Rsegintro, p, { r with r_segintro = PairSet.remove p r.r_segintro })
  else if r.r_ind_weak != PairSet.empty then
    let p = PairSet.min_elt r.r_ind_weak in
    Some (Riweak, p, { r with r_ind_weak = PairSet.remove p r.r_ind_weak })
  else if r.r_pt_pt != PairSet.empty then
    let p = PairSet.min_elt r.r_pt_pt in
    Some (Rpp, p, { r with r_pt_pt = PairSet.remove p r.r_pt_pt })
  else None


(** Invalidate rules that become infeasible, due to other rules
 *  being applied *)
(* Kinds of elements to invalidate *)
type invalid =
  | Ihf of heap_frag   (* a heap fragment as per graph_sig *)
  | Inone              (* nothing *)
  | Iblob of IntSet.t  (* a memory blob *)
  | Isiblings          (* siblings of a node *)
(* Case of a local rule *)
let invalidate_rules
    (isl: nid) (isr: nid)
    (invl: invalid) (invr: invalid) (r: rules): rules =
  (* Map over the rules type *)
  let map_rules (f: PairSet.t -> PairSet.t) (r: rules): rules =
    { r_pt_prio  = f r.r_pt_prio;
      r_pt_pt    = f r.r_pt_pt;
      r_ind_ind  = f r.r_ind_ind;
      r_ind_weak = f r.r_ind_weak;
      r_segintro = f r.r_segintro; } in
  (* Invalidate rules over a set *)
  let invalidate (il, ir) (s: PairSet.t): PairSet.t =
    if !Flags.flag_debug_join_strategy then
      Log.force "invalidating join rule at (%d,%d)" il ir;
    PairSet.remove (il, ir) s in
  let invalidate_map (f: (int * int) -> bool) (s: PairSet.t): PairSet.t =
    PairSet.fold
      (fun p acc ->
        if f p then invalidate p acc
        else acc
      ) s s in
  (* Rules consuming *one* node in each side *)
  let invalidate_l  = invalidate_map (fun (x, _) -> x = isl)
  (*and invalidate_r  = invalidate_map (fun (_, y) -> y = isr)*)
  and invalidate_lr = invalidate_map (fun (x, y) -> x = isl || y = isr) in
  (* Rules consuming a blob in one side *)
  let invalidate_nb (s: IntSet.t) =
    map_rules (invalidate_map (fun (_, y) -> IntSet.mem y s)) in
  let invalidate_bb (sl: IntSet.t) (sr: IntSet.t) =
    map_rules
      (invalidate_map (fun (x, y) -> IntSet.mem x sl || IntSet.mem y sr)) in
  match invl, invr with
  | Ihf (Hpt _), Ihf (Hpt _) ->
      { r with
        r_pt_prio = invalidate_lr r.r_pt_prio;
        r_pt_pt   = invalidate_lr r.r_pt_pt }
  | Ihf (Hind _), Ihf (Hind _) ->
      { r with
        r_ind_ind  = invalidate_lr r.r_ind_ind;
        r_ind_weak = invalidate_l  r.r_ind_weak }
  | Inone, Iblob br -> invalidate_nb br r
  | Iblob bl, Iblob br -> invalidate_bb bl br r
  | Isiblings, Inone ->
      { r with
        r_segintro = invalidate_l r.r_segintro }
  | _, _ -> Log.todo_exn "invalidate"


(** Rules utility functions *)

(* Try to guess an inductive definition from a points-to edges map *)
let select_inductive_candidate
    (msg: string)
    (is_seg: bool) (* is it for a segment ? *)
    (mcr: pt_edge Block_frag.t) =
  let m = Graph_strategies.extract_compatible_inductives false mcr in
  StringMap.iter (fun s _ -> Log.info "candidate: %s" s) m;
  let l =
    match !Ind_utils.ind_prec with
    | [ ] -> StringMap.fold (fun _ i l -> i :: l) m [ ]
    | _ ->
        List.fold_left
          (fun acc s ->
            if StringMap.mem s m then StringMap.find s m :: acc
            else acc
          ) [ ] (List.rev !Ind_utils.ind_prec) in
  match l with
  | [ ind ] ->
      Log.info "selected inductive %s" ind.i_name ;
      ind
  | _ -> raise (Abort_rule
                  (Printf.sprintf "%s: too many/not enough candidates" msg))


(** Implementation of rules *)

(* pt-pt [par ptr OK, par int OK]
 *   consume edges and produce a matching one *)
let apply_pt_pt
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (dw: dw_config): dw_config =
  let nl = node_find isl dw.dw_inl in
  let nr = node_find isr dw.dw_inr in
  match nl.n_e, nr.n_e with
  | Hpt mcl, Hpt mcr ->
      let dw =
        (* treat the table of edges *)
        Block_frag.fold_base
          (fun os pl dw ->
            if Block_frag.mem os mcr then
              let pr = Block_frag.find_addr os mcr in
              assert (pl.pe_size = pr.pe_size);
              let dl_n, dl_o = pl.pe_dest
              and dr_n, dr_o = pr.pe_dest in
              assert (Offs.compare dl_o dr_o = 0);
              let dw, id = find_in_config (dl_n, dr_n) dw in
              let pe = { pe_size = pl.pe_size ;
                         pe_dest = id, dl_o } in
              collect_rules_node dl_n dr_n
                { dw with
                  dw_out = pt_edge_block_append (is, os) pe dw.dw_out }
            else
              begin
                Log.info "unable to match edge in pt-pt!";
                dw
              end
          ) mcl dw in
      let vrules =
        invalidate_rules isl isr (Ihf nl.n_e) (Ihf nr.n_e) dw.dw_rules in
      { dw with
        dw_inl   = pt_edge_block_destroy isl dw.dw_inl;
        dw_inr   = pt_edge_block_destroy isr dw.dw_inr;
        dw_rules = vrules; }
  | _, _ -> (* we may check the rule was not invalidated ? *)
      Log.fatal_exn "pt-pt: improper case"

(* ind-ind [par ptr OK, par int OK]
 *   consume edges and produce a matching one *)
let apply_ind_ind
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (dw: dw_config): dw_config =
  let nl = node_find isl dw.dw_inl in
  let nr = node_find isr dw.dw_inr in
  match nl.n_e, nr.n_e with
  | Hind iel, Hind ier ->
      assert (List.length iel.ie_args.ia_int =
              List.length ier.ie_args.ia_int);
      assert (List.length iel.ie_args.ia_ptr =
              List.length ier.ie_args.ia_ptr);
      assert (List.length iel.ie_args.ia_set = 0);
      assert (List.length ier.ie_args.ia_set = 0);
      if Ind_utils.compare iel.ie_ind ier.ie_ind = 0 then
        let l_pargs, j =
          List.fold_left2
            (fun (acc_l, acc_j) ial iar ->
              let nj, ia = find_in_config (ial, iar) acc_j in
              Log.info "ptr parameter map: %d-%d" ial iar;
              ia :: acc_l, nj
            ) ([ ], dw) iel.ie_args.ia_ptr ier.ie_args.ia_ptr in
        (* Construction of a new inductive edge for the pair graph *)
        let l_iargs, rel, out =
          List.fold_left2
            (fun (acc_l, acc_rel, acc_out) ial iar ->
              let ia, n_out = sv_add_fresh Ntint Nnone acc_out in
              ia :: acc_l,
              Nwkinj.add acc_rel (ial, iar) ia,
              n_out
            ) ([ ], dw.dw_rel, dw.dw_out) iel.ie_args.ia_int
            ier.ie_args.ia_int in
        let ie = { ie_ind  = iel.ie_ind ;
                   ie_args = { ia_ptr = List.rev l_pargs ;
                               ia_int = List.rev l_iargs ;
                               ia_set = [ ] } } in
        (* HS: todo: deal with set parameters *)
        let vrules =
          invalidate_rules isl isr (Ihf nl.n_e) (Ihf nr.n_e) dw.dw_rules in
        { dw with
          dw_rules = vrules;
          dw_inl   = ind_edge_rem isl dw.dw_inl;
          dw_inr   = ind_edge_rem isr dw.dw_inr;
          dw_out   = ind_edge_add is ie out;
          dw_rel   = rel }
      else Log.todo_exn "join: inductive edges fails"
  | _, _ -> (* we may check the rule was not invalidated ? *)
      Log.fatal_exn "ind-ind: improper case"

(* seg-intro [par ptr KO, par int KO] *)
(* Issues left with rule seg-intro:
 *  - depending on the strategy, the siblings to a node may be
 *    considered several times in the course of the algorithm
 *    so a seg-intro may be triggered again; we should avoid that
 *    => this actually happens in several cases, causing by-pass
 *)
let apply_seg_intro
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (dw: dw_config): dw_config =
  (* extract other siblings *)
  let siblings =
    try IntMap.find isl dw.dw_rel.wi_l_r
    with
    | Not_found ->
        (* this should not happen, as this rule should be triggered only
         * when there are siblings in the relation (so isl should be there) *)
        Log.fatal_exn "inconsistent mapping in seg-intro" in
  assert (IntSet.mem isr siblings);
  let siblings = IntSet.remove isr siblings in
  assert (IntSet.cardinal siblings = 1); (* should only be >= 1 *)
  let idr = IntSet.min_elt siblings in
  let id =
    try PairMap.find (isl, idr) dw.dw_rel.wi_lr_o
    with Not_found -> Log.fatal_exn "pair (%d,%d) not found" isl idr in
  (* trigger a weakening attempt (to segment) *)
  let nr = node_find isr dw.dw_inr in
  (* determine inductive definition *)
  let ind = (* try to determine which inductive to synthesize *)
    let search_avail_def ( ) =
      match nr.n_e with
      | Hpt mcr -> select_inductive_candidate "seg-intro" true mcr
      | _ -> raise (Abort_rule "seg-intro fails (ind not found)") in
    if Flags.flag_weaken_use_attribute then
      match nr.n_attr with
      | Attr_none | Attr_array _ ->
          (* no attribute, try to search through available definitions *)
          search_avail_def ( )
      | Attr_ind iname ->
          (* attribute gives a hint of the inductive to select *)
          Ind_utils.ind_find iname
    else search_avail_def ( ) in
  let lcandidates =
    let sibl = IntMap.find isl dw.dw_rel.wi_l_r in
    Graph_strategies.extract_segment_directions sibl ind.i_dirs dw.dw_inr in
  Log.info "Found %d seg-candidates" (List.length lcandidates);
  let isr, idr =
    match lcandidates with
    | (x, y) :: _ ->
        if x = isr then x, y
        else raise (Abort_rule "seg-intro: not the best source")
    | [ ] -> raise (Abort_rule "seg-intro: no pair of nodes") in
  assert (ind.i_ipars = 0);
  assert (ind.i_spars = 0);
  assert (ind.i_ppars = 0);
  (* test of inclusion of a part of the right side into a segment edge *)
  let le_res, ser =
    Graph_algos.is_le_seg false ind dw.dw_inr isr idr dw.dw_satr
      (fun _ -> false) in
  match le_res with
  | Ilr_le_rem (grem, removedr, inj, sinst, _, sv_inst, cons_non_proved) ->
      if ser.se_sargs.ia_ptr != [ ] || ser.se_dargs.ia_ptr != [ ] then
        Log.fatal_exn "dw, segintro does not support parameters";
      assert (sinst = IntMap.empty); (* HS: todo *)
      assert (sv_inst = sv_inst_empty); (* HS: todo *)
      assert (cons_non_proved = []); (* HS: todo *)
      let seg =
        { se_ind   = ind ;
          se_sargs = { ia_ptr = [ ] ;
                       ia_int = [ ];
                       ia_set = [ ] } ;
          se_dargs = { ia_ptr = [ ] ;
                       ia_int = [ ];
                       ia_set = [ ];} ;
          se_dnode = id } in
      let vrules =
        invalidate_rules isl isr Isiblings Inone
          (invalidate_rules isl isr Inone (Iblob removedr) dw.dw_rules) in
      { dw with
        dw_rules = vrules;
        dw_inr   = grem;
        dw_out   = seg_edge_add is seg dw.dw_out }
  | Ilr_not_le -> (* rule application failed *)
      Log.fatal_exn "seg-intro fails (not le)"
  | Ilr_le_seg _ | Ilr_le_ind _ -> (* those cases should not happen *)
      Log.fatal_exn "seg-intro: absurd is_le result"


(** Engine iterating over available rules *)
let rec dweak (dw: dw_config): dw_config =
  let ppi = graph_2stri "  " in 
  match rules_next dw.dw_rules with
  | None ->
      (* there is no more rule to apply, so we can return current config *)
      if !Flags.flag_debug_dweak_shape then
        begin
          Log.force "no more rule applies;\n%s" (rules_2str dw.dw_rules);
          Log.force
            "----------------\nSituation:\n- L:\n%s- R:\n%s- O:\n%s- M:\n%s"
            (ppi dw.dw_inl) (ppi dw.dw_inr) (ppi dw.dw_out)
            (Nwkinj.wi_2stri "  " dw.dw_rel);
        end;
      dw
  | Some (r, (il, ir), rem_rules) ->
      if !Flags.flag_debug_dweak_shape then
        begin
          Log.force
            "----------------\nSituation:\n- L:\n%s- R:\n%s- O:\n%s- M:\n%s"
            (ppi dw.dw_inl) (ppi dw.dw_inr) (ppi dw.dw_out)
            (Nwkinj.wi_2stri "  " dw.dw_rel);
          if !Flags.flag_debug_dweak_strategy then
            Log.force "join-nodes to treat:\n%s"
              (rules_2str dw.dw_rules)
        end;
      let dw = { dw with dw_rules = rem_rules } in
      if !Flags.flag_debug_dweak_shape then
        Log.force "dw-Treating (%d,%d) (%s)\n" il ir (kind_2str r);
      let is =
        try Nwkinj.find dw.dw_rel (il, ir)
        with Not_found -> Log.fatal_exn "%d,%d not found" il ir in
      try
        let nj =
          match r with
          | Rpp -> apply_pt_pt is il ir dw
          | Rii -> apply_ind_ind is il ir dw
          | Rsegintro -> apply_seg_intro is il ir dw
          | _ ->
              Log.todo_exn "some rule applies: %s" (kind_2str r) in
        dweak nj
      with
      | e -> Log.fatal_exn "crashed: exc: %s" (Printexc.to_string e)


(** Directed weakening function:
 **  - takes two arguments;
 **  - over-approximates only the right argument;
 **  - use the left argument as a "hint" of where to lose precision *)
let directed_weakening
    (xl: graph)              (* left graph *)
    (xr: graph)              (* right graph *)
    (satr: n_cons -> bool)   (* right sat function *)
    (ho: hint_bg option)     (* optional hint (roots) *)
    (wi: node_wkinj)         (* node weak injection *)
    (xo: graph)              (* pre-initialized output *)
    : graph * node_wkinj =
  (* Hint for prioritary pt edges due to the environment *)
  let h =
    match ho with
    | None -> fun _ -> true
    | Some s ->
        fun (j,i) ->
          try Aa_maps.find j s.hbg_live = i
          with Not_found -> false in
  (* Initialization of the algorithm state *)
  let dw_init = { dw_inl   = xl;
                  dw_inr   = xr;
                  dw_satr  = satr;
                  dw_rules = empty_rules;
                  dw_rel   = wi;
                  dw_out   = xo } in
  let dw_init = init_rules h dw_init in
  (* Start the iterative algorithm *)
  let dw_res = dweak dw_init in
  dw_res.dw_out, dw_res.dw_rel



(** Extraction of the mapping *)
let extract_mapping (xr: graph) (wi: node_wkinj): unit node_mapping =
  let init (g: graph): unit node_mapping =
    { nm_map    = IntMap.empty ;
      nm_rem    = get_all_nodes g ;
      nm_suboff = fun _ -> true ; } in
  PairMap.fold
    (fun (_, ir) io acc ->
      Nd_utils.add_to_mapping ir io acc
    ) wi.wi_lr_o (init xr)
