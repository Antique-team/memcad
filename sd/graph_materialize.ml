(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_materialize.ml
 **       unfolding of graphs, materialization
 ** Xavier Rival, 2011/08/06 *)
open Apron
open Data_structures
open Graph_sig
open Graph_utils
open Ind_sig
open Ind_utils
open Lib
open Nd_sig

(** Error report *)
module Log =
  Logger.Make(struct let section = "g_mat___" and level = Log_level.DEBUG end)

      
(** Materialization of one rule *)
(* returns:
 * - unfolded graph
 * - additional constraints
 * - set of new nodes *)
let materialize_rule
    ~(submem: bool) (* whether sub-memory is_le (no alloc check) *)
    (nbase: nid)
    (ind: ind)
    (iargs: ind_args)
    (ondest: (nid * ind_args) option) (* destination (segment case) *)
    (len1: bool) (* whether segment of length 1 (segment case) *)
    (ir: irule)
    (t: graph)
    : (graph * PairSet.t) list * n_cons list * IntSet.t =
  (* debug *)
  if !Flags.flag_debug_materialize then
    Log.force "Materialize rule to %s\n%s\nGraph[%d]:\n%s"
      (match ondest with None -> "full inductive" | Some _ -> "segment")
      (irule_2str ir) nbase (graph_2stri "  " t);
  (* create new nodes *)
  let rec aux_gen_nodes (i: int) (t: graph) =
    if i < 0 then t, IntMap.empty, IntSet.empty
    else
      begin
        let tacc, macc, sacc = aux_gen_nodes (i - 1) t in
        let typ =
          try IntMap.find i ir.ir_typ
          with Not_found -> Log.fatal_exn "missing new SV info in inductive" in
        let n, tn = sv_add_fresh typ Nnone tacc in
        tn, IntMap.add i n macc, IntSet.add n sacc
      end in
  let t0, form_to_act, nnodes = aux_gen_nodes (ir.ir_num-1) t in
  (* mark alloc node, if necessary *)
  let t0 =
    List.fold_left
      (fun acc -> function
        | Pf_alloc sz -> mark_alloc nbase sz acc
        | _ -> acc
      ) t0 ir.ir_pure in
  if !Flags.flag_debug_materialize then
    Log.force "Expanded graph:\n%s" (graph_2stri "  " t0);
  (* functions that return a node *)
  let fetch_ptr_par (i: int): int =
    try List.nth iargs.ia_ptr i
    with Failure _ -> Log.fatal_exn "materialize: ptr par out of range" in
  let fetch_int_par (i: int): int =
    try List.nth iargs.ia_int i
    with Failure _ -> Log.fatal_exn "materialize: int par out of range" in
  (* associate a formal node to its real counterpart *)
  let map_node (i: int): int =
    try IntMap.find i form_to_act
    with Not_found -> Log.fatal_exn "rule formal %d not found" i in
  let map_formal_arg: formal_arg -> int = function
    | `Fa_this      -> nbase
    | `Fa_var_new i -> map_node i
    | `Fa_par_int i -> fetch_int_par i
    | `Fa_par_ptr i -> fetch_ptr_par i
    | `Fa_par_set _ -> Log.todo_exn "set parameter instantiation" in
  let map_formal_main_arg (fa: formal_main_arg): int =
    map_formal_arg (fa :> formal_arg) in
  let map_formal_ptr_arg (fa: formal_ptr_arg): int =
    map_formal_arg (fa :> formal_arg) in
  let map_formal_int_arg (fa: formal_int_arg): int =
    map_formal_arg (fa :> formal_arg) in
  let map_formal_arith_arg (fa: formal_arith_arg): int =
    map_formal_arg (fa :> formal_arg) in
  (* mapping of a set of arguments to a recursive call to an inductive
   * (might be a full inductive edge or a segment) *)
  let map_ind_args (i: indcall): ind_args =
    (* generation of the lists of arguments *)
    { ia_ptr = List.map map_formal_ptr_arg i.ii_argp ;
      ia_int = List.map map_formal_int_arg i.ii_argi } in
  (* create new edges *)
  let t1 =
    (* for code clarity, the ast of inductives might be better off separating
     * those two elements *)
    let l_cells, l_inds =
      List.fold_left
        (fun (ac, ai) -> function
          | Hacell c -> c :: ac, ai
          | Haind  i -> ac, i :: ai
        ) ([ ], [ ]) ir.ir_heap in
    (* materialize all points-to edges once and for all *)
    let t_pt =
      List.fold_left
        (fun tacc c ->
          let pte = { pe_size = Offs.size_of_int c.ic_size ;
                      pe_dest = map_formal_arith_arg c.ic_dest, Offs.zero } in
          pt_edge_block_append (nbase, Bounds.of_offs c.ic_off) pte tacc
        ) t0 (List.rev l_cells) in
    (* proceed with the addition of inductives *)
    match ondest with
    | None ->
        let t_u =
          List.fold_left
            (fun tacc i ->
              (* creation of an inductive edge, with the right nodes
               * in the list of arguments *)
              let ie = { ie_ind  = Ind_utils.ind_find i.ii_ind ;
                         ie_args = map_ind_args i } in
              (* addition of the edge to the graph *)
              ind_edge_add (map_formal_main_arg i.ii_maina) ie tacc
            ) t_pt l_inds in
        [ t_u, PairSet.empty ]
    | Some (nd, argd) ->
        (* two lists of graphs: 1: with a 0-segment; 2: with a 1-segment *) 
        let _, l1 =
          List.fold_left
            (fun (al0, al1) i ->
              assert (i.ii_argi = [ ]);
              let mapped_base = map_formal_main_arg i.ii_maina in
              let mapped_args = map_ind_args i in
              let f_ind: graph -> graph =
                let ie = { ie_ind  = Ind_utils.ind_find i.ii_ind;
                           ie_args = mapped_args } in
                ind_edge_add mapped_base ie in
              let f_seg (gg: graph): graph * PairSet.t =
                let seg = { se_ind   = Ind_utils.ind_find i.ii_ind;
                            se_sargs = mapped_args;
                            se_dargs = argd;
                            se_dnode = nd } in
                if len1 then gg, empty_segment_equalities mapped_base seg
                else seg_edge_add mapped_base seg gg, PairSet.empty in
              let l_up_ind = List.map (fun (g, s) -> f_ind g, s) al1 in
              if (i.ii_ind = ind.i_name) then
                List.map f_ind al0, (List.map f_seg al0) @ l_up_ind
              else
                List.map f_ind al0, l_up_ind
            ) ([ t_pt ], [ ]) l_inds in
        l1 in
  (* compute predicates *)
  let rec map_aexpr: aexpr -> n_expr = function
    | Ae_cst i ->
        Ne_csti i
    | Ae_var fa ->
        Ne_var (map_formal_arith_arg fa)
    | Ae_plus (e0, e1) ->
        Ne_bin (Texpr1.Add, map_aexpr e0, map_aexpr e1) in
  let map_aform: aform -> n_cons = function
    | (Af_equal (e0, e1) | Af_noteq (e0, e1)) as f ->
        let op =
          match f with
          | Af_equal (_, _) -> Tcons1.EQ
          | Af_noteq (_, _) -> Tcons1.DISEQ in
        let te0 = map_aexpr e0 and te1 = map_aexpr e1 in
        Nc_cons (op, te0, te1) in
  (* handling predicates different from allocation *)
  let p =
    List.fold_left
      (fun accp -> function
        | Pf_alloc sz -> accp
        | Pf_arith f -> map_aform f :: accp
        | Pf_set _ -> Log.todo_exn "set predicate"
      ) [ ] ir.ir_pure in
  (* final result *)
  if !Flags.flag_debug_materialize then
    List.iter
      (fun (t, _) ->
        Log.force "Unfolded graph:\n%s" (graph_2stri "  " t)) t1;
  t1, p, nnodes


(** Materialization of an inductive *)
(* returns a list of tuples of the same form as for materialize_rule *)
let materialize_ind
    ~(submem: bool) (* whether sub-memory is_le (no alloc check) *)
    (hint_empty: bool option) (* whether to put empty rules first, last or not*)
    (es: bool) (* whether to generate empty segment case (for segment unfold) *)
    (len1: bool) (* whether segment is of length 1 (for segment unfold) *)
    (nbase: nid) (* source: node where unfolding should take place *)
    (t: graph)   (* input graph *)
    : unfold_res list =
  let indedge, odest, t0 = ind_or_seg_edge_find_rem nbase t in
  let indname = indedge.ie_ind.i_name in
  let ind = Ind_utils.ind_find indname in
  (* we take hint (in is_le) to order the rules in a "more likely to succeed"
   * order (this is a trick to avoid backtracking, by trying to predict which
   * rule will give a successful comparison) *)
  let rules =
    let rules =
      match odest with
      | None -> ind.i_rules (* full inductive; consider all rules *)
      | Some _ -> ind.i_srules (* segment: only consider segment rules *) in
    match hint_empty with
    | None -> rules
    | Some b ->
        let emp, non_emp =
          List.fold_left
            (fun (ae, ane) ir ->
              if ir.ir_kind = Ik_empz then (* rule has empty heap *)
                ir :: ae, ane
              else (* rule has non empty heap *)
                ae, ir :: ane
            ) ([ ], [ ]) rules in
        (* put empty first if not b (the fold left will put them at the
         * beginning again) *)
        match b, Flags.flag_unfold_sel with
        |  true,  true -> emp
        |  true, false -> non_emp @ emp
        | false,  true -> non_emp
        | false, false -> emp @ non_emp in
  (* case of the empty segment, if we are unfolding a segment and es is true *)
  let emp_seg_case =
    if es then
      match odest with
      | None -> (* the edge is a full inductive *)
          [ ]
      | Some (ndst, adst) ->
          (* the edge is a segment; consider the empty case here *)
          let eqs =
            empty_segment_equalities nbase { se_ind   = ind;
                                             se_sargs = indedge.ie_args;
                                             se_dargs = adst;
                                             se_dnode = ndst } in
          Log.info "Equalities to propagate: %s"
            (PairSet.t_2str ", " eqs);
          [ { ur_g    = t0;
              ur_cons = [ ];
              ur_eqs  = eqs;
              ur_news = IntSet.empty } ]
    else [ ] in
  (* materialization of all the other rules *)
  List.fold_left
    (fun acc ir ->
      let lg, cl, is =
        materialize_rule ~submem:submem nbase ind indedge.ie_args
          odest len1 ir t0 in
      List.fold_left
        (fun acc (g, eqs) ->
          { ur_g    = g;
            ur_cons = cl;
            ur_eqs  = eqs;
            ur_news = is } :: acc
        ) acc lg
    ) emp_seg_case rules


(** Higher level unfold function *)
let unfold
    ~(submem: bool) (* whether sub-memory is_le (no alloc check) *)
    (nbase: int)    (* source: node where unfolding should take place *)
    (d: unfold_dir) (* direction, for segment edges only *)
    (g: graph)      (* input *)
    : unfold_res list =
  match d with
  | Udir_fwd -> materialize_ind ~submem:submem None true false nbase g
  | Udir_bwd ->
      (* Empty segment case *)
      let emp_seg_case =
        let seg = seg_edge_find nbase g in
        let eqs = empty_segment_equalities nbase seg in
        { ur_g    = seg_edge_rem nbase g;
          ur_cons = [ ];
          ur_eqs  = eqs;
          ur_news = IntSet.empty } in
      (* Splitting case *)
      let g, nmid = seg_split nbase g in
      if !Flags.flag_debug_bwd_unfold then
        Log.force "Bwd-unfold, after splitting:\n%s" (graph_2stri "  " g);
      let non_emp_seg_cases =
        materialize_ind ~submem:submem None false true nmid g in
      (* Putting it all together *)
      emp_seg_case :: non_emp_seg_cases
