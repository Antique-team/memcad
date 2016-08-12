(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_join.ml
 **       graph join algorithm
 ** Xavier Rival, 2011/07/25 *)
open Data_structures
open Lib
open Offs

open Graph_sig
open Graph_encode
open Ind_sig
open Nd_sig
open Sv_sig

open Gen_dom
open Gen_join

open Graph_utils
open Ind_utils


(** Error report *)
module Log =
  Logger.Make(struct let section = "g_join__" and level = Log_level.DEBUG end)



(** Aborting a rule *)
exception Abort_rule of string



(** Collapsing and instantiation:
 *  - "collapsings" over blocks of points-to edges
 *  - for nodes synthesized as inductive parameters *)
(* Empty instantiation *)
let inst_empty =
  { ins_expr    = IntMap.empty;
    ins_fold    = IntMap.empty;
    ins_new_off = [ ]; }
(* Printing of a node collapsing *)
let n_collapsing_2str (nc: n_collapsing): string =
  let f (_, on, sz) =
    Printf.sprintf "%s[%s]" (onode_2str on) (Offs.size_2str sz) in
  Printf.sprintf "%d |-> {%s} [%s]" nc.col_base
    (gen_list_2str "" f "," nc.col_block) (OffSet.t_2str "; " nc.col_extptr)



(** Join algorithm state *)
(* State *)
type join_config =
    { (** Iteration strategy *)
      (* Rules that could be applied right away *)
      j_rules:  rules;
      (** Arguments *)
      (* Arguments (left and right) *)
      j_inl:    graph;
      j_inr:    graph;
      j_jal:    join_arg;
      j_jar:    join_arg;
      (* Satisfaction of boolean predicates *)
      j_satl:   (n_cons -> bool);
      j_satr:   (n_cons -> bool);
      (** Relations among arguments *)
      (* Relation between arguments/output nodes *)
      j_rel:    node_relation;
      (* Instantiations for nodes in the left and right argument *)
      j_instl:  n_instantiation;
      j_instr:  n_instantiation;
      (* Hint: nodes that should be treated in priority *)
      j_hint:   (int * int -> bool);
      (* lint: nodes address should forget value *)
      j_lint:   (onode * onode -> bool);
      (* relation pair been dropped XR=>HS: explain more *)
      j_drel:   PairSet.t;
      (** Outputs *)
      (* Output under construction *)
      j_out:    graph;
      (** Parameters about the is_le semantics *)
      (* Whether we consider a sub-memory: no alloc check for sub-memories *)
      j_submem: bool; }



(** Operations on configuration: managing mappings *)
(* Find node the result node corresponding to a pair of nodes in the
 * arguments if it exists;
 * if there is no such image node, allocate one and return it together
 * with the extended configuration *)
let find_in_config (p: int * int) (j: join_config): join_config * int =
  try j, Nrel.find j.j_rel p
  with Not_found ->
    let alloc, typ, att =
      try
        let nl = node_find (fst p) j.j_inl in
        let nr = node_find (snd p) j.j_inr in
        let a = if nl.n_alloc = nr.n_alloc then nl.n_alloc else Nnone in
        let t = ntyp_merge nl.n_t nr.n_t in
        a, t, node_attribute_lub nl.n_attr nr.n_attr
      with
      | Not_found ->
          Log.fatal_exn "find_in_config: node not found (%d,%d)"
            (fst p) (snd p) in
    let ni, nout = sv_add_fresh ~attr: att typ alloc j.j_out in
    let nrel = Nrel.add j.j_rel p ni in
    { j with
      j_out = nout ;
      j_rel = nrel }, ni

(* Find in config, loose version:
 *  may drop relation in "side", if the other node has already a mapping 
 *  - e.g., if a mapping (3,8) exists and side=Rgh, then
 *    find_in_config_looose (3,9) will return (3,8)
 *  - in the same situation but when (3,6), (3,8) exist in the mapping, the
 *    result is non-deterministic
 *  - when no such mapping exists, it behaves exactly like find_in_config
 * This function can be used when mapping parameters of an inductive predicate
 * that can be ignored (e.g., prev parameter of a dll definition, for the empty
 * rule).
 *)
let find_in_config_loose
    (side: side)         (* side that can be dropped *)
    ((il,ir) as p: int * int) (* candidate mapping *)
    (j: join_config): join_config * int =
  let debug_loc = false in
  let io, is = Graph_algos.get_sides side p in
  (* the side shows the empty side, thus, we should take the parameter
   * from the other side *)
  let s = Nrel.siblings (Graph_algos.other_side side) io j.j_rel in
  if debug_loc then
    Log.force "find_in_config_loose_%s %d, (%d,%d): { %s }"
      (Graph_algos.side_2str side) io il ir (IntSet.t_2str ", " s);
  if s = IntSet.empty then
    (* no solution: revert back to the classical find_in_config *)
    find_in_config p j
  else
    (* at least one solution (possibly many): pick one *)
    let pnew = Graph_algos.get_sides side (io, IntSet.min_elt s) in
    let j, inew = find_in_config pnew j in
    if debug_loc then Log.force "find_in_config_loose return: %d" inew;
    j, inew

(* Read in node relation; will not modify it (crash if not there) *)
let read_in_config (p: int * int) (j: join_config): int =
  try Nrel.find j.j_rel p
  with Not_found -> Log.fatal_exn "read_in_config"



(** Management of applicable rules *)
(* Computes the next applicable rules at a node *)
let collect_rules_node_gen
    (is_prio: int * int -> bool) (* whether pt rules are prioritary (init) *)
    (il: int) (ir: int) (* nodes in both inputs *)
    (jc: join_config): join_config =
  let is_seg_ext =
    Graph_utils.is_bseg_ext jc.j_jal.abs_go il jc.j_jar.abs_go ir in
  let is_seg_intro = 
    Graph_utils.is_bseg_intro jc.j_jal.abs_go il jc.j_jar.abs_go ir in
  let jr =
    collect_rules_sv_gen is_prio is_seg_ext is_seg_intro jc.j_rel
      il (sv_kind il jc.j_inl) ir (sv_kind ir jc.j_inr) jc.j_rules in
  { jc with j_rules = jr }
let collect_rules_node (il: int) (ir: int) (jc: join_config): join_config =
  collect_rules_node_gen 
    (* let node in encoded graph with high priority  *)
    (fun (l,ir) -> encode_node_find il jc.j_jal && encode_node_find ir jc.j_jar)
    il ir jc
(* Computes the set of rules at initialization *)
let init_rules (jc: join_config): join_config =
  PairMap.fold
    (fun (il, ir) _ ->
      collect_rules_node_gen jc.j_hint il ir
    ) jc.j_rel.n_inj jc



(** Utility functions for the is_le rules *)

(* Unification of block fragmentations for array analyses
 * Inputs two states with blocks that have different numbers of elements
 *    and performs some abstraction on their structure, to make them
 *    "similar", so that the join algorithm can continue
 * Returns:
 *  - a new join configuration
 *  - a pair of unified blocks *)
type extracted_block = (Bounds.t * onode * Offs.size) list
let block_array_unify
    (stride: int) (* array, attribute determined stride *)
    (* for each side: node, size, fragmentation of the block *)
    (nl: node) (sl: int) (mcl: pt_edge Block_frag.t) (* left node and block *)
    (nr: node) (sr: int) (mcr: pt_edge Block_frag.t) (* right node and block *)
    (j: join_config) (* join configuration *)
    : join_config * (pt_edge Block_frag.t * pt_edge Block_frag.t) =
  (* assertion that the right side is initially finer than the left one *)
  let sdelta = sr - sl in
  assert (0 < sdelta);
  (* utility function: checks whether the head offset is on stride *)
  let has_first_on_stride (mc: pt_edge Block_frag.t): bool =
    Bounds.is_on_stride stride (Block_frag.first_bound mc) in
  (* 1. collect sdelta elements in the right + 1 *)
  let bnd_low_r = Block_frag.first_bound mcr in
  let ext_r: extracted_block ref = ref [] in
  let mcr_r: pt_edge Block_frag.t ref = ref mcr in
  let span_r: Offs.size ref = ref Offs.size_zero in
  let shift_r () = (* take one element in the right state and move it out *)
    let (b, e), rem = Block_frag.extract_rem_first !mcr_r in
    mcr_r := rem;
    ext_r := (b, e.pe_dest, e.pe_size) :: !ext_r;
    span_r := Offs.size_add_size !span_r e.pe_size in
  for i = 0 to sdelta do (* repeat this for sdelta + 1 elements *)
    shift_r ()
  done;
  (* enriching right hand side graph *)
  let sum_r, tr = sv_add_fresh Ntraw nr.n_alloc j.j_inr in
  let sum_pt_r = { pe_size = Offs.size_of_int 0;
                   pe_dest = sum_r, Offs.zero } in
  let col_r = { col_base   = nr.n_i;
                col_stride = stride;
                col_block  = []; (* still to compute *) 
                col_extptr = OffSet.empty } in
  (* 2. look whether the right side has size 1 *)
  if sl = 1 then
    let col_r = { col_r with col_block = List.rev !ext_r } in
    let sum_pt_r = { sum_pt_r with pe_size = !span_r } in
    let instr = { j.j_instr with
                  ins_fold = IntMap.add sum_r col_r j.j_instr.ins_fold } in
    let j = { j with
              j_inr   = tr;
              j_instr = instr } in
    j, (mcl, Block_frag.append_head bnd_low_r sum_pt_r !mcr_r)
  else
    begin
      (* 3. collect elements up to stride in the right *)
      while not (has_first_on_stride !mcr_r) do
        shift_r ()
      done;
      (* 4. do the same in the left side *)
      let bnd_low_l = Block_frag.first_bound mcl in
      let ext_l: extracted_block ref = ref [] in
      let mcl_l: pt_edge Block_frag.t ref = ref mcl in
      let span_l: Offs.size ref = ref Offs.size_zero in
      let shift_l () =
        let (b, e), rem = Block_frag.extract_rem_first !mcl_l in
        mcl_l := rem;
        ext_l := (b, e.pe_dest, e.pe_size) :: !ext_l;
        span_l := Offs.size_add_size !span_l e.pe_size in
      shift_l ();
      while not (has_first_on_stride !mcl_l) do
        shift_l ()
      done;
      (* 5. enrich graphs and produce result *)
      let col_r = { col_r with col_block = List.rev !ext_r } in
      let sum_pt_r = { sum_pt_r with pe_size = !span_r } in
      let instr = { j.j_instr with
                    ins_fold = IntMap.add sum_r col_r j.j_instr.ins_fold } in
      let sum_l, tl = sv_add_fresh Ntraw nl.n_alloc j.j_inl in
      let col_l = { col_base   = nl.n_i;
                    col_stride = stride;
                    col_block  = List.rev !ext_l;
                    col_extptr = OffSet.empty } in
      let sum_pt_l = { pe_size = !span_l;
                       pe_dest = sum_l, Offs.zero } in
      let instl = { j.j_instl with
                    ins_fold = IntMap.add sum_l col_l j.j_instl.ins_fold } in
      let j = { j with
                j_inl   = tl;
                j_inr   = tr;
                j_instl = instl;
                j_instr = instr } in
      j, (Block_frag.append_head bnd_low_l sum_pt_l !mcl_l,
          Block_frag.append_head bnd_low_r sum_pt_r !mcr_r)
    end

(* Unification of bounds and offsets:
 *  -> may augment the configuration with new mapping
 *  -> returns a new bound, with symbolic variables in the join
 *     result naming space *)
let unify_gen
    (a_2str: 'a -> string)
    (unifier: 'a -> 'a -> (int * int * int) list * 'a)
    (renamer: int IntMap.t -> 'a -> 'a)
    (xl: 'a) (xr: 'a) (j: join_config)
    : join_config * 'a =
  let uni, b_new = unifier xl xr in
  let j, index =
    List.fold_left
      (fun (j, acc) (svl, svr, svtemp) ->
        let j, svnew = find_in_config (svl, svr) j in
        j, IntMap.add svtemp svnew acc
      ) (j, IntMap.empty) uni in
  let x_new = renamer index b_new in
  j, x_new
let unify_bounds (bl: Bounds.t) (br: Bounds.t) (j: join_config)
    : join_config * Bounds.t =
  unify_gen Bounds.t_2str Bounds.unify Bounds.rename bl br j
let unify_offsets (offl: Offs.t) (offr: Offs.t) (j: join_config)
    : join_config * Offs.t =
  if Offs.t_is_const offl
      && Offs.t_is_const offr
      && Offs.compare offl offr = 0 then
    (* fast unification of constant offsets *)
    j, offl
  else
    (* non constant offsets, more complex unification algorithm *)
    let unifier o0 o1 =
      match Offs.t_unify o0 o1 with
      | None ->
          (* replaces this with a variable offset:
           *  - variable offsets should be stored in a special map
           *  - renaming of those offsets will require special care...
           * risk: to perform this operation while trying to compensate
           *       another precision issue *)
          raise Stop
      | Some (uni, o) -> uni, o in
    try unify_gen Offs.t_2str unifier Offs.t_rename offl offr j
    with
    | Stop ->
        (* "normal" unification failed;
         * we switch to a less accurate offset unification, where a new
         * offset is generated (or reused), that consists only in a single
         * variable and is reused later *)
        assert (j.j_instl.ins_new_off = [ ]);
        assert (j.j_instr.ins_new_off = [ ]);
        let n, out = sv_add_fresh ~attr: Attr_none Ntint Nnone j.j_out in
        let ores = Offs.of_n_expr (Ne_var n) in
        Log.info "Binding offsets %s,%s => %s"
          (Offs.t_2str offl) (Offs.t_2str offr) (Offs.t_2str ores);
        { j with
          j_instl = { j.j_instl with
                      ins_new_off = (offl, n, ores) :: j.j_instl.ins_new_off };
          j_instr = { j.j_instr with
                      ins_new_off = (offr, n, ores) :: j.j_instr.ins_new_off };
          j_out   = out },
        ores
let unify_sizes (sl: Offs.size) (sr: Offs.size) (j: join_config)
    : join_config * Offs.size =
  if Offs.size_is_const sl
      && Offs.size_is_const sr
      && Offs.is_zero (Offs.of_size (Offs.size_sub_size sl sr)) then
    j, sl (* sizes are already fixed constants and unified *)
  else
    let unifier o0 o1 =
      match Offs.size_unify sl sr with
      | None -> Log.fatal_exn"no unifying size"
      | Some (uni, sz) -> uni, sz in
    unify_gen Offs.size_2str unifier Offs.size_rename sl sr j

(* Try to guess an inductive definition from a points-to edges map *)
let block_inductive_candidate
    (msg: string)
    (g: graph)     (* graph used to bound a set of inductives *)
    (is_seg: bool) (* is it for a segment ? *)
    (mcr: pt_edge Block_frag.t) =
  (* inductives which are compatible with the points-to edges *)
  let m = Graph_strategies.extract_compatible_inductives false mcr in
  (* filtering candidates used in the domain *)
  let m = StringMap.filter (fun s ind -> StringSet.mem s g.g_inds) m in
  if !Flags.flag_debug_join_shape then
    StringMap.iter (fun s _ -> Log.force "candidate: %s" s) m;
  let l = StringMap.fold (fun _ ind acc -> ind :: acc) m [ ] in
  match l with
  | [ ind ] ->
      if !Flags.flag_debug_join_shape then
        Log.force "selected inductive %s" ind.i_name ;
      ind
  | hd :: tl ->
      (* use of the precedence directive to choose an order... *)
      let l = 
        match !Ind_utils.ind_prec with
        | [ ] -> l
        | _ ->
            let l_prec = 
              List.fold_left
                (fun acc s ->
                  try StringMap.find s m :: acc with Not_found -> acc
                ) [ ] (List.rev !Ind_utils.ind_prec) in
            if l_prec = [] then l
            else l_prec in
      if List.length l = 1 then
        List.hd l 
      else 
        let inds_in = collect_inds g in
        let l = List.filter (fun ind -> StringSet.mem ind.i_name inds_in) l in
        assert (List.length l = 1);
        List.hd l
  | _ ->
      raise (Abort_rule
               (Printf.sprintf "%s: too many/not enough candidates" msg))



(** Individual join rules *)

(* pt-pt [par ptr OK, par int OK]
 *   consume edges and produce a matching one *)
let apply_pt_pt
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let nl = node_find isl j.j_inl in
  let nr = node_find isr j.j_inr in
  match nl.n_e, nr.n_e with
  | Hpt mcl, Hpt mcr ->
      let sz_l = Block_frag.cardinal mcl and sz_r = Block_frag.cardinal mcr in
      (* If array, we may have to make the blocks compatible *)
      let j =
        if sz_l != sz_r then
          let j, (ul, ur) =
            match nl.n_attr, nr.n_attr with
            | Attr_array (stride_l, _), Attr_array (stride_r, _) ->
                if stride_l = stride_r then
                  block_array_unify stride_l nl sz_l mcl nr sz_r mcr j
                else Log.fatal_exn "unify: %d, %d" stride_l stride_r
            | Attr_array _, _ | _, Attr_array _ -> Log.fatal_exn"Unify part"
            | Attr_none, Attr_none ->
                raise (Abort_rule "no attribute in both sides")
            | _ -> Log.fatal_exn "Other case of unify %s, %s"
                     (node_attribute_2str nl.n_attr)
                     (node_attribute_2str nr.n_attr) in
          Block_frag.fold_list2_bound2
            (fun (osl, el) (osr, er) pl pr j ->
              if !Flags.flag_debug_array_blocks then
                Log.force
                  "treating offsets:\n -L: %s (%s) -> %s\n -R: %s (%s) -> %s"
                  (Bounds.t_2str osl) (Offs.size_2str pl.pe_size)
                  (Bounds.t_2str el)
                  (Bounds.t_2str osr) (Offs.size_2str pr.pe_size)
                  (Bounds.t_2str er);
              (* Unification of the lower bound and of the size *)
              let j, os = unify_bounds osl osr j in
              let j, usize =
                let sl = Bounds.sub_t el osl
                and sr = Bounds.sub_t er osr in
                let j, usize = unify_bounds sl sr j in
                j, Offs.to_size (Bounds.to_offs usize) in
              (* Computation of the new edge *)
              let dl_n, dl_o = pl.pe_dest
              and dr_n, dr_o = pr.pe_dest in
              assert (Offs.compare dl_o dr_o = 0);
              let j, id = find_in_config (dl_n, dr_n) j in
              let pe = { pe_size = usize;
                         pe_dest = id, dl_o } in
              if !Flags.flag_debug_array_blocks then
                Log.force "adding: %d, %s" is (Bounds.t_2str os);
              let out =
                pt_edge_block_append ~nochk: true (is, os) pe j.j_out in
              collect_rules_node dl_n dr_n { j with j_out = out }
            ) ul ur j
        else
          Block_frag.fold_list2_base
            (fun osl osr (pl: pt_edge) (pr: pt_edge) j ->
              let onl, onr =
                (isl, Bounds.to_offs osl), (isr, Bounds.to_offs osr) in
              let j, u_os = unify_bounds osl osr j in
              let j, u_size = unify_sizes pl.pe_size pr.pe_size j in
              let dl_n, dl_o = pl.pe_dest
              and dr_n, dr_o = pr.pe_dest in
              let j, dd_o = unify_offsets dl_o dr_o j in
              let j, id = find_in_config (dl_n, dr_n) j in
              let pe = { pe_size = u_size ;
                         pe_dest = id, dd_o } in
              (* comsume the pt edge in encoded graph *)
              let j = { j with 
                        j_jal = encode_pt_pt onl (dl_n, dl_o) j.j_jal;
                        j_jar = encode_pt_pt onr (dr_n, dr_o) j.j_jar; } in
              (* XR=>HS: explain these cases *)
              if j.j_lint (onl, onr) then
                { j with
                  j_out = pt_edge_block_append (is, u_os) pe j.j_out;
                  j_drel = PairSet.add (dl_n, dr_n) j.j_drel }
              else
                collect_rules_node dl_n dr_n
                  { j with
                    j_out = pt_edge_block_append (is, u_os) pe j.j_out }
            ) mcl mcr j in
      let vrules = invalidate_rules isl isr Ipt Ipt j.j_rules in
      { j with
        j_inl   = pt_edge_block_destroy isl j.j_inl;
        j_inr   = pt_edge_block_destroy isr j.j_inr;
        j_rules = vrules; }
  | _, _ -> (* we may check the rule was not invalidated ? *)
      Log.fatal_exn"pt-pt: improper case"

(* ind-ind [par ptr OK, par int OK]
 *   consume edges and produce a matching one *)
let apply_ind_ind
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let nl = node_find isl j.j_inl in
  let nr = node_find isr j.j_inr in
  match nl.n_e, nr.n_e with
  | Hind iel, Hind ier ->
      assert (List.length iel.ie_args.ia_int =
              List.length ier.ie_args.ia_int);
      assert (List.length iel.ie_args.ia_ptr =
              List.length ier.ie_args.ia_ptr);
      if Ind_utils.compare iel.ie_ind ier.ie_ind = 0 then
        (* check if inductive edge is empty *)
        let bign_l = Ind_utils.no_par_use_rules_emp iel.ie_ind
            && j.j_satl (Nc_cons (Apron.Tcons1.EQ, Ne_var isl, Ne_csti 0)) in
        let bign_r = Ind_utils.no_par_use_rules_emp ier.ie_ind
            && j.j_satr (Nc_cons (Apron.Tcons1.EQ, Ne_var isr, Ne_csti 0)) in
        let l_pargs, j =
	  (* when one inductive edge is empty but not the other *)
          if (bign_l || bign_r) && (bign_l != bign_r) then
            let side = if bign_l then Lft else Rgh in
            List.fold_left2
              (fun (acc, j) ial iar ->
                let io, is =  Graph_algos.get_sides side (ial, iar) in
                Log.info "search (%d,%d), could advantage %d" ial iar io;
                let j, ni =
                  try
                    let _ = Nrel.find j.j_rel (ial, iar) in
                    find_in_config (ial, iar) j 
                  with Not_found ->
                    find_in_config_loose side (ial, iar) j in
                ni :: acc, j
              ) ([ ], j) iel.ie_args.ia_ptr ier.ie_args.ia_ptr
          else
            List.fold_left2
              (fun (acc_l, acc_j) ial iar ->
                let nj, ia = find_in_config (ial, iar) acc_j in
                ia :: acc_l, nj
              ) ([ ], j) iel.ie_args.ia_ptr ier.ie_args.ia_ptr in
        (* Construction of a new inductive edge for the pair graph *)
        let l_iargs, rel, out =
          List.fold_left2
            (fun (acc_l, acc_rel, acc_out) ial iar ->
              let ia, n_out =
                sv_add_fresh Ntint Nnone acc_out in
              ia :: acc_l,
              Nrel.add acc_rel (ial, iar) ia,
              n_out
            ) ([ ], j.j_rel, j.j_out) iel.ie_args.ia_int ier.ie_args.ia_int in
        let ie = { ie_ind  = iel.ie_ind ;
                   ie_args = { ia_ptr = List.rev l_pargs ;
                               ia_int = List.rev l_iargs } } in
        let vrules = invalidate_rules isl isr Iind Iind j.j_rules in
        { j with
          j_rules = vrules;
          j_inl   = ind_edge_rem isl j.j_inl;
          j_inr   = ind_edge_rem isr j.j_inr;
          j_out   = ind_edge_add is ie out;
          j_rel   = rel }
      else Log.todo_exn "join: inductive edges fails"
  | _, _ -> (* we may check the rule was not invalidated ? *)
      Log.fatal_exn"ind-ind: improper case"

(* ind-weak [par ptr OK, par int OK]
 * ind-weak: weakening the right side to match an inductive in the left side
 * weak-ind: weakening the left side to match an inductive in the right side *)
let apply_gen_ind_weak
    (side: side) (* side of the rule (weakening side) *)
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let rname = Graph_algos.sel_side side ("ind-weak", "weak-ind") in
  let iso, iss = Graph_algos.get_sides side (isl, isr) in
  let ino, ins = Graph_algos.get_sides side (j.j_inl, j.j_inr) in
  let sato, sats = Graph_algos.get_sides side (j.j_satl, j.j_satr) in
  (* r -> side; l -> other side *)
  let ns = node_find iss ins in
  match ns.n_e with
  | Hind ies ->
      let n_int = List.length ies.ie_args.ia_int in
      (* construction of a graph with just one inductive edge *)
      (* experimental:
       * integer arguments of the inductive are special nodes
       * that might be instantiated *)
      let le_res, ieo, instantiable_nodes =
        Graph_algos.is_le_ind ~submem:j.j_submem ies.ie_ind ino iso sato in
      begin
        match le_res with
        | Ilr_le_rem (grem, removed, rel, inst) ->
            (* addition of instantiations of the nodes of "other side" *)
            let insto, insts =
              Graph_algos.get_sides side (j.j_instl, j.j_instr) in
            let ninsto =
              IntMap.fold
                (fun i ex acc ->
                  if IntMap.mem i acc then
                    (* double instantiation attempt, fail *)
                    Log.fatal_exn "%s: attempt at double instantiation" rname
                  else IntMap.add i ex acc
                ) inst insto.ins_expr in
            let j =
              match side with
              | Lft ->
                  let vrules =
                    invalidate_rules isl isr (Iblob (IntSet.singleton isl))
                      (Iblob removed) j.j_rules in
                  { j with
                    j_rules = vrules;
                    j_inl   = ind_edge_rem isl j.j_inl;
                    j_inr   = grem;
                    j_instr = { insto with ins_expr = ninsto } }
              | Rgh ->
                  let vrules =
                    invalidate_rules isl isr (Iblob removed)
                      (Iblob (IntSet.singleton isr)) j.j_rules in
                  { j with
                    j_rules = vrules;
                    j_inl   = grem;
                    j_inr   = ind_edge_rem isr j.j_inr;
                    j_instl = { insto with ins_expr = ninsto } } in
            assert (IntMap.cardinal inst = IntSet.cardinal instantiable_nodes);
            let bign_s =
              Ind_utils.no_par_use_rules_emp ies.ie_ind
                && sats (Nc_cons (Apron.Tcons1.EQ, Ne_var iss, Ne_csti 0)) in
            let bign_o =
              Ind_utils.no_par_use_rules_emp ies.ie_ind
                && sato (Nc_cons (Apron.Tcons1.EQ, Ne_var iso, Ne_csti 0)) in
            if bign_s && bign_o then
              (* both inductive edges denote the empty store *)
              j
            else
              (* either of the edges denotes non empty stores *)
              let (ie, gout), j =
                let revppars, j =
                  List.fold_left2
                    (fun (acc, j) is io ->
                      (* if bign_s, then we can ignore is, and look for a better
                       * choice in the configuration, if bign_o, then we can
                       * ignore io, and look for a better choice in the
                       * configuration *)
                      let nio, loose =
                        try IntMap.find io rel, false
                        with Not_found -> io, true
                      in
                      let p = Graph_algos.get_sides side (nio, is) in
                      if bign_s then
                        Log.info "search (%d,%d) (s), could advantage %d"
                          (fst p) (snd p) nio;
                      if bign_o || loose then
                        Log.info "search (%d,%d) (o), could advantage %d"
                          (fst p) (snd p) is;
                      let j, ni =
                        if bign_s then find_in_config_loose side p j
                        else if bign_o || loose then
                          find_in_config_loose (Graph_algos.other_side side) p j
                        else find_in_config p j in
                      ni :: acc, j
                    ) ([ ], j) ies.ie_args.ia_ptr ieo.ie_args.ia_ptr in
                let ppars = List.rev revppars in
                ind_edge_make ies.ie_ind.i_name ppars n_int j.j_out, j in
              let rel =
                let l_pairs =
                  let al, ar =
                    match side with
                    | Lft -> ies.ie_args, ieo.ie_args
                    | Rgh -> ieo.ie_args, ies.ie_args in
                  List.map2 (fun x y -> x, y) al.ia_int ar.ia_int in
                List.fold_left2 Nrel.add j.j_rel
                  (List.rev l_pairs) ie.ie_args.ia_int in
              { j with
                j_out = ind_edge_add is ie gout ;
                j_rel = rel }
        | Ilr_not_le -> (* rule application failed *)
            if Flags.flag_join_bypass_fail_rules then
              j (* By-pass the rule *)
            else Log.fatal_exn "%s: fails" rname
        | Ilr_le_ind _ | Ilr_le_seg _ -> (* those cases should not happen *)
            Log.fatal_exn "%s: absurd is_le result" rname
      end;
  | _ -> (* we may check the rule was not invalidated ? *)
      Log.fatal_exn "%s: improper case" rname
let apply_weak_ind = apply_gen_ind_weak Rgh
let apply_ind_weak = apply_gen_ind_weak Lft

(* seg-intro [par ptr OK, par int KO] *)
(* Issues left with rule seg-intro:
 *  - depending on the strategy, the siblings to a node may be
 *    considered several times in the course of the algorithm
 *    so a seg-intro may be triggered again; we should avoid that
 *    => this actually happens in several cases, causing by-pass
 *)
let apply_gen_seg_intro
    (side: side) (* side of the rule, i.e., where the empty chunk is found *)
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  (* side resolution:
   *  - "l" -> "s"
   *  - "r" -> "o" *)
  let rname    = Graph_algos.sel_side side ("seg-intro-l", "seg-intro-r") in
  let iso, iss = Graph_algos.get_sides side (isl, isr) in
  let cho, chs = Graph_algos.get_sides side ('l', 'r') in
  let ino, ins = Graph_algos.get_sides side (j.j_inl, j.j_inr) in
  let ego, egs = Graph_algos.get_sides side (j.j_jal, j.j_jar) in
  let sato, sats = Graph_algos.get_sides side (j.j_satl, j.j_satr) in
  (* extract other siblings *)
  let allsibl = Graph_algos.sel_side side (j.j_rel.n_l2r, j.j_rel.n_r2l) in
  let siblings =
    try IntMap.find iss allsibl
    with
    | Not_found ->
        (* this should not happen, as this rule should be triggered only
         * when there are siblings in the relation (so isl should be there) *)
        Log.fatal_exn "inconsistent mapping in %s" rname in
  assert (IntSet.mem iso siblings);
  let siblings = IntSet.remove iso siblings in
  let seg_end = Graph_utils.choose_dst iso ego.abs_go siblings in  
  (* destination node in the other side *)
  let ido =
    let card = IntSet.cardinal siblings in
    let card_end = IntSet.cardinal seg_end in
    if card = 0 then Log.fatal_exn"no sibling";
    let n = IntSet.min_elt siblings in
    if card > 1 && card_end = 1 then
      begin
        Log.info "seg-intro found too many siblings: %s ; picking end: %d"
          (intset_2str siblings) (IntSet.min_elt seg_end);
        IntSet.min_elt seg_end
      end
    else 
      begin
        Log.info "seg-intro found too many siblings: %s ; picking %d"
          (intset_2str siblings) n;
        n
      end in
  if !Flags.flag_debug_join_shape then
    Log.force "seg-intro attempt: S%c:%d -> (S%c:%d,D%c:%d)"
      chs iss cho iso cho ido;
  (* destination node in the result *)
  let pd = Graph_algos.get_sides side (ido, iss) in
  let id =
    try PairMap.find pd j.j_rel.n_inj
    with Not_found ->
      Log.fatal_exn "pair (%d,%d) not found" (fst pd) (snd pd) in
  let id_node = node_find id j.j_out in
  (* trigger a weakening attempt (to segment) *)
  let no = node_find iso (Graph_algos.sel_side side (j.j_inr, j.j_inl)) in
  (* determine inductive definition *)
  let ind = (* try to determine which inductive to synthesize *)
    let search_avail_def ( ) =
      match no.n_e with
      | Hpt mco -> block_inductive_candidate rname ins true mco
      | Hseg se -> se.se_ind
      | _ -> raise (Abort_rule "seg-intro fails (ind not found)") in
    if Flags.flag_weaken_use_attribute then
      match no.n_attr with
      | Attr_none | Attr_array _ ->
          (* no attribute, try to search through available definitions *)
          search_avail_def ( )
      | Attr_ind iname ->
          (* attribute gives a hint of the inductive to select *)
          Ind_utils.ind_find iname
    else search_avail_def ( ) in
  let is_continue =
    let lcandidates =
      let sibl = IntMap.find iss allsibl in
      Graph_strategies.extract_segment_directions sibl ind.i_dirs ino in
    if !Flags.flag_debug_join_shape then
      Log.force "Found %d seg-candidates" (List.length lcandidates);
    let is_source = List.exists (fun (x, y) -> x = iso) lcandidates in
    let niss, nido  = node_find iss ins, node_find ido ino in
    let is_rule = 
      match (niss.n_attr, niss.n_e), (nido.n_attr, nido.n_e) with
      (* compare the property of end nodes to see if the rule is ok to apply *)
      | (Attr_ind _, Hpt _), (Attr_none, Hemp) -> false
      | _, _ -> true in 
    match lcandidates, is_source, is_rule with
    | (x, y) :: _, false, _ ->
        raise (Abort_rule "seg-intro: not the best source")
    | (x, y)::_, true, false ->
      false
    | (x, y)::_, true, true -> true
    | [ ], _, _ -> raise (Abort_rule "seg-intro: no pair of nodes") in
  if not is_continue then
    collect_rules_node_gen (fun (l, r) -> l=isl && r = isr) isl isr j
  else 
    begin
      assert (ind.i_ipars = 0);
      (* test of inclusion of a part of the right side into a segment edge *)
      let le_res, seo =
        Graph_algos.is_le_seg ~submem:j.j_submem ind ino iso ido sato in
      match le_res with
      | Ilr_le_rem (gremo, removedo, inj, inst) ->
          assert (inst = IntMap.empty);
          (* rule success; perform the weakening *)
          (* begin temp *)
          (* this code is ugly and works only for pointer parameters *)
          if !Flags.flag_debug_join_shape then
            Log.force "seg_intro: should work";
          (* mapping the pointer parameters of the new edge *)
          let f_do_it (j: join_config) (iao: ind_args): nid list =
            List.map
              (fun io ->
                let nio =
                  try IntMap.find io inj
                  with Not_found -> raise (Abort_rule rname) in
                nio
              ) iao.ia_ptr in
          let m_osrc = f_do_it j seo.se_sargs in
          let m_odst = f_do_it j seo.se_dargs in
          let id_pars_opt =
            match id_node.n_e with
            | Hpt _ | Hemp -> None
            | Hind ie -> Some ie.ie_args
            | Hseg se -> Some se.se_sargs in
          (* when the destination node is null, we may need to modify the
           * parameter *)
          let m_odst = 
            if sato (Nc_cons (Apron.Tcons1.EQ, Ne_var ido, Ne_csti 0)) then
              match id_pars_opt with
              | None -> m_odst 
              | Some ind_pars ->
                  List.map
                    (fun io ->
                      snd (Nrel.find_p j.j_rel io)
                    ) ind_pars.ia_ptr
            else m_odst in
          let m_s =
            let lll, _ =
              List.fold_left2
                (fun (acc, i) iaso iado ->
                  let set = IntSet.add iaso (IntSet.singleton iado) in
                  let candidates = Nrel.mult_bind_candidates side j.j_rel set in
                  if !Flags.flag_debug_join_shape then
                    Log.force "Par =.(%d)==.(%d)=> candidates: %s (set %s)"
                      iaso iado (intset_2str candidates) (intset_2str set);
                  let card = IntSet.cardinal candidates in
                  let par =
                    if card = 0 then
                      (* Backup solution:
                       * see if there is an inductive edge in ins at node iss
                       * if so, try to "guess" the parameter there, to be used
                       * for both ends of the (empty) segment being
                       * introduced *)
                      let ns = node_find iss ins in
                      match ns.n_e with
                      | Hind ns_ie ->
                          if Ind_utils.compare ns_ie.ie_ind ind = 0 then
                            let par = List.nth ns_ie.ie_args.ia_ptr i in
                            if !Flags.flag_debug_join_shape then
                              Log.force "seg-in backup par search => %d" par;
                            par
                          else
                            Log.fatal_exn "backup parameter search failed (ind)"
                      | Hseg ns_se ->
                          if Ind_utils.compare ns_se.se_ind ind = 0 then
                            let par = List.nth ns_se.se_sargs.ia_ptr i in
                            if !Flags.flag_debug_join_shape then
                              Log.force "seg-in backup par search => %d" par;
                            par
                          else
                            Log.fatal_exn"seg-in backup par search failed (seg)"
                      | Hpt mc ->
                          (* If the inductive analysis did find out where
                           * a parameter may be stored try to retrieve it *)
                          let guessed_par =
                            try IntMap.find i ind.i_fl_pars
                            with Not_found ->
                              Log.fatal_exn
                                "backup parameter search failed (pt)" in
                          let guessed_edge =
                            Block_frag.find_addr
                              (Bounds.of_int guessed_par) mc in
                          if Offs.is_zero (snd guessed_edge.pe_dest) then
                            fst guessed_edge.pe_dest
                          else
                            Log.fatal_exn
                              "backup parameter search failed (pt, off!=0)"
                      | Hemp ->
                          (* in this case, the edge may have been already
                           * matched, thus, we can get some information from
                           * the out graph *)
                          let nd = node_find id j.j_out in
                          match nd.n_e with
                          | Hind ind_edge ->
                              if Ind_utils.compare ind_edge.ie_ind ind = 0 then
                                let par = List.nth ind_edge.ie_args.ia_ptr i in
                                let in_pars = IntMap.find par j.j_rel.n_pi in
                                let _, par_s =
                                  Graph_algos.get_sides side in_pars in
                                if !Flags.flag_debug_join_shape then
                                  Log.force "seg-in backup par search=> %d"
                                    par_s;
                                par_s 
                              else
                                Log.fatal_exn
                                  "backup parameter search failed (empty)"
                          | _ ->
                              Log.fatal_exn
                                "backup parameter search failed (empty)"
                    else if card = 1 then
                      IntSet.min_elt candidates
                    else
                      Log.fatal_exn
                        "seg-intro: too many or not enough candidates" in
                  par :: acc, i + 1
                ) ([], 0) m_osrc m_odst in
            List.rev lll in
          let f_combine m_o j =
            let f m0 m1 =
              let mm, j =
                List.fold_left2
                  (fun (accm, j) il ir ->
                    let j, m = find_in_config (il, ir) j in
                    m :: accm, j
                  ) ([], j) m0 m1 in
              List.rev mm, j in
            match side with
            | Lft -> f m_s m_o
            | Rgh -> f m_o m_s in
          let mm_src, j = f_combine m_osrc j in
          let mm_dst, j = f_combine m_odst j in
          (* end temp *)
          let seg =
            { se_ind   = ind ;
              se_sargs = { ia_ptr = mm_src ;
                           ia_int = (assert (ind.i_ipars = 0); [ ]) } ;
              se_dargs = { ia_ptr = mm_dst ;
                           ia_int = (assert (ind.i_ipars = 0); [ ]) } ;
              se_dnode = id } in
          let j =
            match side with
            | Lft ->  collect_rules_node isl ido  { j with j_inr = gremo }
            | Rgh ->  collect_rules_node ido isr  { j with j_inl = gremo } in
          let vrules =
            match side with
            | Lft ->
                invalidate_rules isl isr Isiblings Inone
                  (invalidate_rules isl isr Inone (Iblob removedo) j.j_rules)
            | Rgh ->
                invalidate_rules isl isr Inone Isiblings
                  (invalidate_rules isl isr (Iblob removedo) Inone j.j_rules) in
          { j with
            j_rules = vrules;
            j_out   = seg_edge_add is seg j.j_out }
      | Ilr_not_le -> (* rule application failed *)
          (* HS: instead of failing, we need to try weaken *)
          { j with j_rules = rules_add_weakening (isl, isr) j.j_rules }
      | Ilr_le_seg _ | Ilr_le_ind _ -> (* those cases should not happen *)
          Log.fatal_exn"seg-intro: absurd is_le result"
    end
let apply_seg_intro_l = apply_gen_seg_intro Lft
let apply_seg_intro_r = apply_gen_seg_intro Rgh


(* seg-ext [par ptr OK, par int KO] *)
let apply_seg_ext
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  try
    let nl = node_find isl j.j_inl in
    let nr = node_find isr j.j_inr in
    (* weak side *)
    let side =
      match nl.n_e, nr.n_e with
      | Hseg _, _ -> Rgh 
      | _, Hseg _ -> Lft
      | _, _  -> Log.fatal_exn"indintro: improper case" in
    let _ = Graph_algos.sel_side side ("ext-seg", "seg-ext") in
    let iso, iss = Graph_algos.get_sides side (isl, isr) in
    let ino, ins = Graph_algos.get_sides side (j.j_inl, j.j_inr) in
    let sato, sats = Graph_algos.get_sides side (j.j_satl, j.j_satr) in
    let no, ns =  Graph_algos.get_sides side (nl, nr) in
    let nro, nrs = Graph_algos.get_sides side (j.j_rel.n_l2r, j.j_rel.n_r2l) in
    (* match edge in the left graph with a segment *)
    match no.n_e with
    | Hseg seo ->
        assert_no_int_arg "join,seg-ext" seo.se_sargs;
        assert_no_int_arg "join,seg-ext" seo.se_dargs;
        let ind = seo.se_ind in
        (* extract destination of sel, and see if it is mapped into sthg *)
        let ido = seo.se_dnode in
        (* extract a "tentative" destination in the right side *)
        let ids, guessed =
          let s =
            try IntMap.find ido nro
            with Not_found -> IntSet.empty in
          if !Flags.flag_debug_join_shape then
            Log.force "set found: %s" (intset_2str s);
          let card = IntSet.cardinal s in
          if card = 1 then
            let elt = IntSet.min_elt s in
            let nids, nido  = node_find elt ins, node_find ido ino in
            let is_rule = 
              match (nido.n_attr, nido.n_e), (nids.n_attr, nids.n_e) with
              (* compare the property of end nodes to see
               * if the rule is ok to apply *)
              | (Attr_none, Hpt _), (Attr_none, Hemp) -> false
              | _, _ -> true in 
            if not is_rule then 
              raise (Abort_rule "seg-ext failed (other)")
            else 
              elt, false
          else
            (* Backup solution:
             * - if card > 1,
             *    see if there is a segment in the right side, and if so
             *    look if its destination works as well
             * - if card = 0,
             *    see if there is a segment in the right side and use it... *)
            match ns.n_e with
            | Hseg ses ->
                if IntSet.mem ses.se_dnode s then ses.se_dnode, false
                else if card = 0 then
                  begin (* no other solution anyway *)
                    Log.warn
                      "seg-ext takes next segment (not sure about end-point)";
                    ses.se_dnode, true
                  end
                else Log.fatal_exn"seg-ext backup failed (seg)"
            | _ -> raise (Abort_rule "seg-ext backup failed (other)") in
        (* test of inclusion of a part of the right side into a segment edge *)
        let le_res, ses =
          Graph_algos.is_le_seg ~submem:j.j_submem ind ins iss ids sats in
        begin
          match le_res with
          | Ilr_le_rem (grem, removedr, inj, inst) ->
              (* success case *)
              (* synthesis and addition of a new segment edge *)
              assert (inst = IntMap.empty);
              assert (seo.se_sargs.ia_int = [ ]);
              assert (ses.se_sargs.ia_int = [ ]);
              (* mapping the pointer parameters of the new edge *)
              let find (l, r) j =
                find_in_config (Graph_algos.get_sides side (l, r)) j in
              let f_do_it j ial iar =
                let j, l =
                  List.fold_left2
                    (fun (accj, accl) il ir ->
                      let nir =
                        try IntMap.find ir inj
                        with Not_found -> raise (Abort_rule "seg-ext") in
                      let nj, ni = find (il, nir) accj in
                      nj, ni :: accl
                    ) (j, [ ]) ial.ia_ptr iar.ia_ptr in
                j, { ia_ptr = List.rev l ;
                     ia_int = (assert (ind.i_ipars = 0); [ ]) } in
              let j, res_sargs = f_do_it j seo.se_sargs ses.se_sargs in
              let j, res_dargs = f_do_it j seo.se_dargs ses.se_dargs in
              (* => If id is not here, add rules from there !!!  *)
              let j, id = find (ido, ids) j in
              let seg = { se_ind   = ind ;
                          se_sargs = res_sargs ;
                          se_dargs = res_dargs ;
                          se_dnode = id } in
              (* there are some case that guessed is true, but we still need *
               * collect rules*)
              let idl, idr = Graph_algos.get_sides side (ido, ids) in
              let j = collect_rules_node idl idr j in
              let vrules =
                match side with
                | Rgh ->
                    invalidate_rules isl isr (Iblob (IntSet.singleton isl))
                      (Iblob removedr) j.j_rules
                | Lft ->
                    invalidate_rules isl isr (Iblob removedr)
                      (Iblob (IntSet.singleton isr)) j.j_rules in
              let j =
                match side with
                | Rgh ->
                    { j with
                      j_inl = seg_edge_rem isl j.j_inl;
                      j_inr = grem; }
                | Lft ->
                    { j with
                      j_inl = grem;
                      j_inr = seg_edge_rem isr j.j_inr; } in
              { j with
                j_rules = vrules;
                j_out   = seg_edge_add is seg j.j_out }
          | Ilr_not_le -> (* rule application failed *)
              Log.fatal_exn"seg-ext fails"
          | Ilr_le_seg _ | Ilr_le_ind _ -> (* those cases should not happen *)
              Log.fatal_exn"seg-ext: absurd is_le result"
        end
    | _ -> (* we may check the rule was not invalidated ? *)
        Log.fatal_exn"seg-ext: improper case"
  with Abort_rule _ ->   
    (* HS: instead of failing, we need to try weaken to inductive edge *)
    { j with j_rules = rules_add_weakening (isl, isr) j.j_rules }


(* seg_ext_ext [par ptr OK, par int KO] *)
let apply_seg_ext_ext
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  try
    (* find destination in both side *)
    let idl, indl_name = Option.get (seg_extension_end isl j.j_jal) in
    let idr, indr_name = Option.get (seg_extension_end isr j.j_jar) in
    assert (indl_name = indr_name);
    Log.info "isl: %d, idl: %d; isr: %d, idr: %d" isl idl isr idr;
    let ind = Ind_utils.ind_find indl_name in
    (* test of inclusion of a part of the left side into a segment edge *)
    let le_res, sel =
      Graph_algos.is_le_seg ~submem:j.j_submem ind j.j_inl isl idl j.j_satl in
    (* test of inclusion of a part of the right side into a segment edge *)
    let re_res, ser =
      Graph_algos.is_le_seg ~submem:j.j_submem ind j.j_inr isr idr j.j_satr in
    begin
      match le_res, re_res with
      | Ilr_le_rem (greml, removedl, injl, instl),
        Ilr_le_rem (gremr, removedr, injr, instr) ->
          (* success case *)
          (* synthesis and addition of a new segment edge *)
          assert (instl = IntMap.empty);
          assert (instr = IntMap.empty);
          assert (sel.se_sargs.ia_int = [ ]);
          assert (ser.se_sargs.ia_int = [ ]);
          (* rename segment parameters to the input*)
          let rename (args: ind_args) (inj: int IntMap.t): ind_args =
            let p =
              List.fold_left (fun acc ele -> IntMap.find ele inj :: acc)
                [] (List.rev args.ia_ptr) in
            { args with ia_ptr = p } in
          let sel = { sel with
                      se_sargs = rename sel.se_sargs injl;
                      se_dargs = rename sel.se_dargs injl; } in
          let ser = { ser with
                      se_sargs = rename ser.se_sargs injr;
                      se_dargs = rename ser.se_dargs injr; } in
          (* mapping the pointer parameters of the new edge *)
          let f_do_it j ial iar =
            let j, l =
              List.fold_left2
                (fun (accj, accl) il ir ->
                  let nj, ni = find_in_config (il, ir) accj in
                  nj, ni :: accl
                ) (j, [ ]) ial.ia_ptr iar.ia_ptr in
            j, { ia_ptr = List.rev l ;
                 ia_int = (assert (ind.i_ipars = 0); [ ]) } in
          let j, res_sargs = f_do_it j sel.se_sargs ser.se_sargs in
          let j, res_dargs = f_do_it j sel.se_dargs ser.se_dargs in
          (* => If id is not here, add rules from there !!!  *)
          let j, id = find_in_config (idl, idr) j in
          let seg = { se_ind   = ind ;
                      se_sargs = res_sargs ;
                      se_dargs = res_dargs ;
                      se_dnode = id } in
          (* there are some case that guessed is true, but we still need *
           * collect rules*)
          let j = collect_rules_node idl idr j in
          let vrules =
            invalidate_rules isl isr
              (Iblob removedl) (Iblob removedr) j.j_rules in
          { j with
            j_rules = vrules;
            j_inl   = greml;
            j_inr   = gremr;
            j_jal   = remove_node isl idl j.j_jal;
            j_jar   = remove_node isr idr j.j_jar;
            j_out   = seg_edge_add is seg j.j_out }
            (* rule application failed *)
      | Ilr_not_le, _ -> 
          Log.fatal_exn"seg-ext-ext fails: Ile"
      |  _, Ilr_not_le ->
          Log.fatal_exn"seg-ext-ext fails: Ire"
      | _, _ -> (* those cases should not happen *)
          Log.fatal_exn"seg-ext-ext: absurd is_le result"
    end
  with Invalid_argument _ ->
    Log.info "isl: %d, isr: %d" isl isr;
    j

(* ind-intro [par ptr OK, part int KO]
 *   introduction of an inductive *)
let apply_ind_intro
    (is: int)  (* source node in the target graph *)
    (isl: int) (* source node in the left graph *)
    (isr: int) (* source node in the right graph *)
    (j: join_config): join_config =
  let nl = node_find isl j.j_inl in
  let nr = node_find isr j.j_inr in
  (* emp side *)
  let side = match nl.n_e, nr.n_e with
    | Hemp, Hpt mcr -> Lft 
    | Hpt mcl, Hemp -> Rgh
    | Hemp, Hemp -> Lft 
    (*HS: it is possible that one side is seg, and the other is pt *)
    | Hpt mcl, Hseg _ -> Rgh
    | Hseg _ , Hpt mcr -> Lft
    | _, _  -> Log.fatal_exn"indintro: improper case" in
  let _ = Graph_algos.sel_side side ("emp-pt", "pt-emp") in
  let iso, iss = Graph_algos.get_sides side (isl, isr) in
  let ino, ins = Graph_algos.get_sides side (j.j_inl, j.j_inr) in
  let sato, sats = Graph_algos.get_sides side (j.j_satl, j.j_satr) in
  let no, ns =  Graph_algos.get_sides side (nl, nr) in
  let nro, nrs = Graph_algos.get_sides side (j.j_rel.n_l2r, j.j_rel.n_r2l) in
  match ns.n_e, no.n_e with
  | _, Hpt mco ->
      (* 1. search for candidate inductive definitions:
       *    - should have an empty rule
       *    - should have a rule matching the rhs signature *)
      let ind = 
        match ns.n_attr with
        | Attr_none | Attr_array _ ->
            block_inductive_candidate "indintro" ino false mco
        | Attr_ind iname ->
            (* attribute gives a hint of the inductive to select *)
            Ind_utils.ind_find iname in
      if !Flags.flag_debug_join_shape then
        Log.force "Selected candidate %s" ind.i_name;
      if ind.i_ppars != 0 then Log.warn "ind-intro, pointer parameters";
      assert (ind.i_ipars = 0);
      (* 2. verify that inclusion holds in both sides *)
      let le_res_s, ies, instants =
        Graph_algos.is_le_ind ~submem:j.j_submem ind ins iss sats in
      let le_res_o, ieo, instanto =
        Graph_algos.is_le_ind ~submem:j.j_submem ind ino iso sato in
      begin
        match le_res_s, le_res_o with
        | Ilr_le_rem (grems, removeds, rels, insts),
          Ilr_le_rem (gremo, removedo, relo, insto) ->
            assert (insts = IntMap.empty);
            assert (insto = IntMap.empty);
            let ppars =
              (* computation of pointer parameters:
               *    - assumes mappings found in the right hand side
               *    - no mapping in the left hand side (no edge)
               * => find a candidate node mapped to the right parameter *)
              let lrev =
                List.fold_left2
                  (fun accp pl0 pr0 ->
                    if !Flags.flag_debug_join_shape then
                      Log.force "parameters: %d - %d" pl0 pr0;
                    let pr1 =
                      try IntMap.find pr0 relo
                      with Not_found ->
                        Log.fatal_exn "ind-intro ppars, no R-map" in
                    let pl1 = 
                      try IntMap.find pl0 rels 
                      with Not_found ->
                        let set0 =
                          try IntMap.find pr1 nro
                          with Not_found ->
                            Log.fatal_exn"ind-intro ppars, no L-set" in
                        if !Flags.flag_debug_join_shape then
                          Log.force "only right mapping %d: %d elts" pr1
                            (IntSet.cardinal set0);
                        if IntSet.cardinal set0 = 0 then
                          Log.fatal_exn"ind-intro ppars, empty L-set"
                        else if IntSet.cardinal set0 > 1 then
                          Log.fatal_exn"ind-intro ppars, too large L-set"
                        else IntSet.min_elt set0  in
                    let p =
                      try Nrel.find j.j_rel
                            (Graph_algos.get_sides side (pr1, pl1))
                      with Not_found ->
                        Log.fatal_exn "ind-intro, ppar not found" in
                    p :: accp
                  ) [ ] ies.ie_args.ia_ptr ieo.ie_args.ia_ptr in
              List.rev lrev in
            let ie =
              { ie_ind  = ind ;
                ie_args = { ia_ptr = ppars;
                            ia_int = (assert (ind.i_ipars = 0); [ ]) } } in
            let vrules =
              match side with
              | Lft ->
                  invalidate_rules isl isr
                    (Iblob removeds) (Iblob removedo) j.j_rules
              | Rgh ->
                  invalidate_rules isl isr
                    (Iblob removedo) (Iblob removeds) j.j_rules in
            let j =
              match side with
              | Lft -> 
                  { j with
                    j_inl = grems;
                    j_inr = gremo; }
              | Rgh ->
                  { j with
                    j_inl = gremo;
                    j_inr = grems; } in
            { j with
              j_rules = vrules;
              j_out   = ind_edge_add is ie j.j_out }
        | _, _ ->
            match side with
            | Lft ->
                Log.info "ind-intro: verification of inclusion: %s - %s"
                  (is_le_res_2str le_res_s) (is_le_res_2str le_res_o);
                Log.todo_exn "ind-intro: le failed"
            | Rgh ->
                Log.info "ind-intro: verification of inclusion: %s - %s"
                  (is_le_res_2str le_res_o) (is_le_res_2str le_res_s);
                Log.todo_exn "ind-intro: le failed"
      end
  | Hemp, Hemp ->
      (* another rule was applied before, we can abort that one *)
      j
  | _, _ ->
      Log.fatal_exn"indintro: improper case"



(** The new join algorithm with worklist over available rules *)
(* This implementation of join relies on a strategy with worklist that
 * iterates over rules.
 *)
let rec s_join (jc: join_config): join_config =
  let ppi = graph_2stri "  " in 
  (* Find the next rule to apply, and trigger it *)
  match rules_next jc.j_rules with
  | None -> (* there is no more rule to apply, so we return current config *)
      if !Flags.flag_debug_join_shape then
        Log.force "no more rule applies;\n%s" (rules_2str jc.j_rules);
      if PairSet.is_empty jc.j_drel then jc 
      else (* XR?: comment what this is doing *)
        let jc =
          PairSet.fold
            (fun (il, ir) acc ->
              if IntMap.mem il jc.j_inl.g_g && IntMap.mem ir jc.j_inr.g_g then
                collect_rules_node il ir acc
              else acc
            ) jc.j_drel jc in
        s_join { jc with j_drel = PairSet.empty }
  | Some (k, (il, ir), rem_rules) ->
      if !Flags.flag_debug_join_shape then
        begin
          Log.force
            "----------------\nSituation:\n- L:\n%s%s- R:\n%s%s- O:\n%s- M:\n%s"
            (ppi jc.j_inl) (Graph_encode.to_string jc.j_jal.abs_go) 
            (ppi jc.j_inr) (Graph_encode.to_string jc.j_jar.abs_go) 
            (ppi jc.j_out) 
            (Nrel.nr_2stri "  " jc.j_rel);
          if !Flags.flag_debug_join_strategy then
            Log.force "%s----------------" (rules_2str jc.j_rules)
        end;
      let jc = { jc with j_rules = rem_rules } in
      let is =
        try PairMap.find (il, ir) jc.j_rel.n_inj
        with Not_found ->
          Log.fatal_exn "pair (%d,%d) not found" il ir in
      if !Flags.flag_debug_join_shape then
        Log.force "join-Treating (%d,%d) (%s)" il ir (kind_2str k);
      try
        let nj =
          match k with
          | Rpp           -> apply_pt_pt       is il ir jc
          | Rii           -> apply_ind_ind     is il ir jc
          | Rweaki        -> apply_weak_ind    is il ir jc
          | Riweak        -> apply_ind_weak    is il ir jc
          | Rsegext       -> apply_seg_ext     is il ir jc
          | Rsegintro Lft -> apply_seg_intro_l is il ir jc
          | Rsegintro Rgh -> apply_seg_intro_r is il ir jc
          | Rindintro     -> apply_ind_intro   is il ir jc
          | Rsplitind Lft -> Log.fatal_exn "Sep-ind-l"
          | Rsplitind Rgh -> Log.fatal_exn "Sep-ind-r"
          | Rsegext_ext   -> apply_seg_ext_ext is il ir jc in
        s_join nj
      with
      | Abort_rule msg ->
          if !Flags.flag_debug_join_shape then
            Log.force "Aborting rule %s" msg;
          s_join jc

let s_g_join (jc: join_config): join_config =
  s_join (init_rules jc)



(** The main join function *)
(* Performs initialization and triggers either algorithm *)
let join
    ~(submem: bool)        (* whether sub-memory is_le (no alloc check) *)
    ((xl, jl): graph * join_arg) (* left input *)
    (satl: n_cons -> bool) (* left satisfaction function *)
    ((xr, jr): graph * join_arg) (* right input *)
    (satr: n_cons -> bool) (* right satisfaction function *)
    (ho: hint_bg option)   (* optional hint *)
    (lo: lint_bg option)   (* optional nullable node address *)
    (r: node_relation)     (* relation between both inputs *)
    (noprio: bool)         (* whether to NOT make roots prioretary *)
    (o: graph)             (* pre-computed, initial version of output *)
    : graph * node_relation (* extended relation *)
    * n_instantiation (* inst for left argument *)
    * n_instantiation (* inst for right argument *) =
  if not !Flags.very_silent_mode then
    Log.force "\n\n[Gr,al]  start join\n\n";
  assert (xl.g_svemod = Dom_utils.svenv_empty);
  assert (xr.g_svemod = Dom_utils.svenv_empty);
  let h =
    if noprio then fun _ -> false
    else
      match ho with
      | None -> fun _ -> true
      | Some s ->
          let prio_nodes =
            if Flags.flag_join_parameters_prio then
              (* roots r such that r->n and n is a segment or inductive
               * arguments should be considered prioritary in this case *)
              begin
                (* checks whether i appears as an argument *)
                let f_ind_args (i: nid) (ia: ind_args): unit =
                  if List.mem i ia.ia_ptr || List.mem i ia.ia_int then
                    raise Stop in
                (* checks whether i is an argument *)
                let f_pred_node (i: nid) (g: graph): bool =
                  try (* raises Stop if it finds i an argument *)
                    IntSet.iter
                      (fun pre_id ->
                        match (node_find pre_id g).n_e with
                        | Hemp
                        | Hpt _ -> ()
                        | Hind ie -> raise Stop (* necessary an argument *)
                        | Hseg se ->
                            f_ind_args i se.se_sargs;
                            f_ind_args i se.se_dargs
                      ) (node_find i g).n_preds;
                    if !Flags.flag_debug_join_shape then
                      Log.force "f_node concluded false on %d" i;
                    false
                  with
                  | Stop ->
                      if !Flags.flag_debug_join_shape then
                        Log.force "f_node concluded true on %d" i;
                      true in
                let f_node (i: nid) (g: graph): bool =
                  match (node_find i g).n_e with
                  | Hpt mc ->
                      Block_frag.fold_base
                        (fun _ pe b -> b || f_pred_node (fst pe.pe_dest) g)
                        mc false
                  | _ -> false in
                IntMap.fold
                  (fun i _ acc ->
                    let il, ir = IntMap.find i r.n_pi in
                    if f_node il xl || f_node ir xr then
                      Aa_maps.add ir il acc
                    else acc
                  ) o.g_g s.hbg_live
              end
            else s.hbg_live in
          fun (i, j) ->
            try Aa_maps.find j prio_nodes = i
            with Not_found -> false in
  let l =
    let is_dead (l, r) lo =
      try (Aa_maps.find l lo.lbg_dead = r)
      with Not_found -> false in 
    match lo with
    | None -> fun (l, r) -> false
    | Some lo -> fun (l, r) -> is_dead (l, r) lo in
  let sat_diseq ctr g =
    match ctr with
    | Nc_cons (Apron.Lincons1.DISEQ, Ne_var i, Ne_var j) ->
      sat_graph_diseq g i j
    | _ -> false in
  let j_sat sat g ctr  = (sat ctr) || (sat_diseq ctr g) in
  let out = s_g_join { j_rules  = empty_rules;
                       j_inl    = xl;
                       j_inr    = xr;
                       j_jal    = jl;
                       j_jar    = jr;
                       j_satl   = j_sat satl xl;
                       j_satr   = j_sat satr xr;
                       j_rel    = r;
                       j_instl  = inst_empty;
                       j_instr  = inst_empty;
                       j_hint   = h;
                       j_lint   = l;
                       j_drel   = PairSet.empty;
                       j_out    = o;
                       j_submem = submem } in
  (* Optional display before return *)
  let ppi = graph_2stri "  " in
  let nl = num_edges out.j_inl and nr = num_edges out.j_inr in
  if !Flags.flag_debug_join_shape || nl != 0 || nr != 0 then
    Log.force
      "Final [%d,%d]:\n- Left:\n%s- Right:\n%s- Out:\n%s\n- Rel:\n%s"
      nl nr (ppi out.j_inl) (ppi out.j_inr) (ppi out.j_out)
      (Nrel.nr_2stri " " out.j_rel);
  out.j_out, out.j_rel, out.j_instl, out.j_instr
