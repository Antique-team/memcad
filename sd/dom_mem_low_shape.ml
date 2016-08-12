(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_mem_low_shape.ml
 **       Low level memory abstraction (memory cells level)
 ** Xavier Rival, 2011/05/27 *)
open Data_structures
open Flags
open Lib
open Offs
open Timer

open Ast_sig
open C_sig
open Dom_sig
open Graph_sig
open Graph_encode
open Ind_sig
open Nd_sig
open Sv_sig
open Svenv_sig

open Ast_utils
open Dom_utils
open Graph_utils
open Nd_utils

open Apron

(** Improvements to consider:
 ** - share code for the initialization of join and weakening
 **   (this will be better done when the structures are made similar)
 **)

(** Error report *)
module Log =
  Logger.Make(struct let section = "dm_ls___" and level = Log_level.DEBUG end)

(** Localization of cells that may be in a sub-memory space *)
(* Resolves how an address should be localizedd *)
type cell_loc =
  | Cl_main       (* address in the main memory *)
  | Cl_sub_intern (* internal address in a sub-memory *)
  | Cl_sub_base   (* base address of a sub-memory *)
let cell_loc_2str: cell_loc -> string = function
  | Cl_main       -> "main"
  | Cl_sub_intern -> "sub[intern]"
  | Cl_sub_base   -> "sub[base]"


(** The shape domain *)
module DBuild = functor (Dv: DOM_VALSET) ->
  (struct
    (** Module name *)
    let module_name = "[shape]"
    (** Dom ID *)
    let dom_id: mod_id ref = ref (-1,"shape")

    (** Type of symbolic indexes *)
    type sym_index = int (* int for the graph implementation *)
    type off_sym_index = sym_index * Offs.t

    (** Type of abstract values *)
    type t =
        { t_shape:   graph;      (* shape component *)
          t_num:     Dv.t;       (* numeric component *)
          t_envmod:  svenv_mod;  (* local symvar env modifications *) }

    (** Domain initialization to a set of inductive definitions *)
    let inductives: StringSet.t ref = ref StringSet.empty
    let init_inductives (g: Keygen.t) (s: StringSet.t): Keygen.t =
      let g = Dv.init_inductives g s in
      inductives := s;
      let g, k = Keygen.gen_key g in (* this domain generates keys *)
      if sv_upg then dom_id := k, snd !dom_id;
      g
    let inductive_is_allowed (s: string): bool = StringSet.mem s !inductives

    (** Fixing sets of keys *)
    let sve_sync_bot_up (x: t): t * svenv_mod =
      { x with t_envmod = svenv_empty }, x.t_envmod

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t = { t_shape  = Graph_utils.graph_empty !inductives;
                   t_num    = Dv.bot;
                   t_envmod = svenv_empty; }
    let is_bot (x: t): bool = Dv.is_bot x.t_num
    (* Top element, with empty set of roots *)
    let top (): t =
      { t_shape  = Graph_utils.graph_empty !inductives;
        t_num    = Dv.top;
        t_envmod = svenv_empty; }
    (* Pretty-printing *)
    let t_2stri (ind: string) (x: t): string =
      let sve =
        if !Flags.flag_debug_symvars then
          Printf.sprintf "%sSVE-Dom-shape:\n%s" ind
            (svenv_2stri (ind^"  ") x.t_envmod)
        else "" in
      Printf.sprintf "%s%s%s" (Graph_utils.graph_2stri ind x.t_shape)
        (Dv.t_2stri IntMap.empty ind x.t_num) sve
    let t_2str: t -> string = t_2stri ""
    (* External output *)
    let ext_output (o: output_format) (base: string) (namer: namer) (x: t)
        : unit =
      let visu_opt_of_string = function
        | "CC" -> Connex_component
        | "SUCC" -> Successors
        | "CUTL" -> Cut_leaves
        | s -> failwith ("visu_opt_of_string: " ^ s) in
      match o with
      | Out_dot (vars, opts) ->
          (* don't slow down memcad during benchmarks *)
          if !Flags.very_silent_mode then
            Log.warn "no pdf output in very_silent_mode"
          else
            let dot_fn = Printf.sprintf "%s.dot" base in
            let enc_txt_fn = Printf.sprintf "%s.enc.txt" base in
            let enc_dot_fn = Printf.sprintf "%s.enc.dot" base in
            let enc_pdf_fn = Printf.sprintf "%s.enc.pdf" base in
            let pdf_fn = Printf.sprintf "%s.pdf" base in
            let opts = List.map visu_opt_of_string opts in
            let disj_num = (-1) in (* we don't care about it *)
            if List.mem Connex_component opts && List.mem Successors opts
            then failwith "ext_output: use either CC either SUCC";
            with_out_file dot_fn
              (Graph_visu.pp_graph pdf_fn vars opts x.t_shape namer);
            with_out_file enc_txt_fn
              (Graph_encode.pp_encoded_graph
                disj_num vars x.t_shape namer enc_dot_fn);
            let shape_graph_to_pdf =
              Printf.sprintf "dot -Tpdf %s -o %s" dot_fn pdf_fn in
            ignore (run_command shape_graph_to_pdf);
            let enc_shape_graph_to_pdf =
              Printf.sprintf "dot -Tpdf %s -o %s" enc_dot_fn enc_pdf_fn in
            ignore (run_command enc_shape_graph_to_pdf)

    (** Graph encoding *)
    let encode (disj: int) (l: namer) (x: t)
        : renamed_path list * PairSetSet.t * int =
      Graph_encode.encode disj l x.t_shape

    (** Management of symbolic variables *)

    (* Ensuring consistency of graph nodes wrt numeric value environment *)
    let sve_fix (x: t): t =
      if !Flags.flag_sanity_graph then
        Graph_utils.graph_sanity_check "sve_fix,before" x.t_shape;
      let g0, svm = Graph_utils.sve_sync_bot_up x.t_shape in
      { t_shape  = g0;
        t_num    = Dv.sve_sync_top_down svm x.t_num;
        t_envmod = svenv_join x.t_envmod svm; }
    (* Addition of a fresh node with known id *)
    let add_node (i: sym_index) (nt: ntyp) (na: nalloc) (x: t): t =
      if !Flags.flag_sanity_graph then
        Graph_utils.graph_sanity_check "add_node,before" x.t_shape;
      sve_fix { x with
                t_shape = Graph_utils.sv_add i nt na x.t_shape }
    (* Will that symb. var. creation be allowed by the domain? *)
    let sv_is_allowed ?(attr: node_attribute = Attr_none) (nt: ntyp)
        (na: nalloc) (x: t): bool = true
    (* Add a node, with a newly generated id *)
    let sv_add_fresh ?(attr: node_attribute = Attr_none) ?(root: bool = false)
        (nt: ntyp) (na: nalloc) (x: t): sym_index * t =
      if !Flags.flag_sanity_graph then
        Graph_utils.graph_sanity_check "sv_add_fresh,before" x.t_shape;
      let i, x0 =
        Graph_utils.sv_add_fresh ~attr:attr ~root:root nt na x.t_shape in
      i, sve_fix { x with
                   t_shape = x0 }
    let get_all_nodes (x: t): IntSet.t =
      Graph_utils.get_all_nodes x.t_shape
    (* Recover information about a symbolic variable *)
    let sv_get_info (i: int) (x: t): nalloc option * ntyp option =
      let ni = Graph_utils.node_find i x.t_shape in
      Some ni.n_alloc, Some ni.n_t

    (** Sanity checks *)
    (* A checking function that numeric domain nodes be consistent *)
    let check_nodes (ctxt: string) (x: t): unit =
      if !Flags.flag_sanity_env then
        (* collect nodes in the graph *)
        let snodes = get_all_nodes x in
        if Flags.flag_sanity_env_pp then
          Log.info "sanity_check, memory nodes: { %s }"
            (IntSet.t_2str "; " snodes);
        (* check that the numerical domain speaks about exactly those keys *)
        let is_valid = Dv.symvars_check snodes x.t_num in
        if Flags.flag_sanity_env_pp then
          Log.info "Dom-shape check_nodes(%s): %b" ctxt is_valid;
        if not is_valid then
          begin
            Log.info "check_nodes(%s): inconsistent num keys" ctxt;
            Log.fatal_exn "check_nodes failed"
          end;
        (* optionally, check that consistence was enforced *)
        let _, svm = Graph_utils.sve_sync_bot_up x.t_shape in
        if not (Dom_utils.svenv_is_empty svm) then
          begin
            Log.info "check_nodes(%s): inconsistent abstract" ctxt;
            Log.fatal_exn "check_nodes failed"
          end
    (* Gathering all sanity checks in a same function *)
    let sanity_check (ctxt: string)
        (do_check_nodes: bool) (* whether to check consistency of node names *)
        (do_graph_sanity: bool) (* whether to perform graph sanity check *)
        (x: t): unit =
      if flag_sanity_bshape then
        begin
          if do_check_nodes then
            check_nodes ctxt x;
          if do_graph_sanity && !Flags.flag_sanity_graph then
            Graph_utils.graph_sanity_check ctxt x.t_shape
        end

    (** Utility functions for the manipulation of abstract values *)
    (* Satifying function in the value domain *)
    let sat_val (t: t) (c: n_cons): bool =
      if !Flags.flag_debug_block_sat then
        Log.force "sat called: %s\n%s" (n_cons_2str c)
          (Dv.t_2stri IntMap.empty "      " t.t_num);
      Dv.sat t.t_num c

    (* Garbage collection *)
    let gc (roots: sym_index uni_table) (x: t): t =
      check_nodes "gc-in" x;
      let nshape = Graph_utils.gc roots x.t_shape in
      if !Flags.flag_sanity_graph then
        Graph_utils.graph_sanity_check "gc,ongoing" nshape;
      let o = sve_fix { x with t_shape = nshape } in
      check_nodes "gc-out" o;
      o
    (* Reduction of nodes that denote the same concrete values
     *   returns both the value after reduction, and the renaming *)
    let red_equal_cells (eqreds: PairSet.t) (t: t): t * int IntMap.t =
      let sat = sat_val t in
      (* 1. reduce equalities in the graph *)
      let (n_shape, renaming), isbot =
        try Graph_utils.graph_merge_eq_nodes sat eqreds t.t_shape, false
        with
        | Bottom -> (t.t_shape, IntMap.empty), true in
      (* 2. get the set of equalities to apply in the numerical domain *)
      let n_num =
        if isbot then Dv.bot
        else
          IntMap.fold
            (fun irem ikeep acc ->
              (* reduction: if ikeep was null in the numeric, and if
               *  irem has a points-to edge, reduce to bottom! *)
              let num =
                if Dv.sat acc (Nc_cons (Tcons1.EQ, Ne_var irem, Ne_csti 0))
                    && Graph_utils.node_is_pt ikeep t.t_shape then
                  Dv.bot
                else acc in
              (* apply the equality constraint in the numerical domain *)
              let cons = Nc_cons (Tcons1.EQ, Ne_var ikeep, Ne_var irem) in
              Dv.guard true cons num
            ) renaming t.t_num in
      sve_fix { t with
                t_shape = n_shape;
                t_num   = n_num }, renaming
    (* Reduction of a state with a segment known to be empty *)
    let red_empty_segment (id: nid) (t: t): t * int IntMap.t =
      (* removal of the segment, and the equalities due to it being empty *)
      let n_shape, eqreds = Graph_utils.red_empty_segment id t.t_shape in
      (* reduction of all equalities obtained above *)
      red_equal_cells eqreds { t with t_shape = n_shape }

    (** Comparison and Join operators *)
    (* Function to check constraint satisfaction on a t *)
    let make_sat (x: t) (nn: n_cons): bool =
      if !Flags.flag_sanity_graph then
        Graph_utils.graph_sanity_check "make_sat,before" x.t_shape;
      if false then
        Log.info "Sat, abstract value:\n%s"
          (Dv.t_2stri IntMap.empty "  " x.t_num);
      match nn with
      | Nc_cons (Tcons1.DISEQ, Ne_csti 0, Ne_var i)
      | Nc_cons (Tcons1.DISEQ, Ne_var i, Ne_csti 0) ->
          if Graph_utils.pt_edge_mem (i, Offs.zero) x.t_shape then true
          else Dv.sat x.t_num nn
      | _ ->
          Dv.sat x.t_num nn
    (* Function for converting hints (temporary glue) *)
    let convert_bin_hint (h: sym_index hint_bs): hint_bg =
      { hbg_live = h.hbs_live }
    let convert_uni_hint (h: sym_index hint_us): hint_ug =
      { hug_live = h.hus_live }
    let convert_bin_lint (h: onode lint_bs): lint_bg =
      { lbg_dead = h.lbs_dead }
    (* Checks if the left argument is included in the right one *)
    let is_le (ninj: sym_index bin_table) (_: sym_index bin_table)
        (xl: t) (xr: t): svenv_upd option =
      sanity_check "is_le,l,before" true true xl;
      sanity_check "is_le,r,before" true true xr;
      (* function to test whether a condition is satisfied *)
      let satl: n_cons -> bool = make_sat xl in
      (* launching the graph algorithm and processing its output *)
      let oinj = Graph_is_le.is_le false xl.t_shape None satl xr.t_shape ninj in
      match oinj with
      | None ->
          if !flag_debug_is_le_gen then
            Log.force "Comparison: shape did not conclude le!";
          None
      | Some inj ->
          if !flag_debug_is_le_gen then
            begin
              let smap = IntMap.t_2str "" string_of_int inj in
              Log.force ("Comparison: is_le holds in the shape!\n" ^^
                        "Numerics:\n%sMapping:\n%s")
                (Dv.t_2stri IntMap.empty "  " xr.t_num) smap
            end;
          let inj_rel: (int * Offs.t) node_mapping =
            let nodes = get_all_nodes xl in
            IntMap.fold (fun i j -> add_to_mapping j i) inj
              { nm_map    = IntMap.empty ;
                nm_rem    = nodes;
                nm_suboff = fun _ -> true } in
          if !flag_debug_is_le_gen then
            Log.force "Effective mapping:\n%s"
              (node_mapping_2str inj_rel);
          let n_l = Dv.symvars_srename OffMap.empty inj_rel None xl.t_num in
          let sat_diseq = Graph_utils.sat_graph_diseq xr.t_shape in
          let r =
            if Dv.is_le n_l xr.t_num sat_diseq then
              let svu =
                svenv_upd_embedding
                  { inj_rel with nm_suboff = fun _ -> true } in
              Some svu
            else None in
          if !flag_debug_is_le_gen then
            Log.force "Numeric comparison: %s\nleft:\n%sright:\n%s"
              (if r = None then "false" else "true")
              (Dv.t_2stri IntMap.empty "   " n_l)
              (Dv.t_2stri IntMap.empty "   " xr.t_num);
          r
    (* Generic join *)
    let join (j: join_kind) (hso: sym_index hint_bs option)
        (lso: (onode lint_bs) option)
        (roots_rel: sym_index tri_table) (setroots_rel: sym_index tri_table)
        ((xl, jl): t * join_ele) ((xr, jr): t * join_ele)
        : t * svenv_upd * svenv_upd =
      sanity_check "join-l,before" true true xl;
      sanity_check "join-r,before" true true xr;
      (* Hint conversion *)
      let hgo = Option.map convert_bin_hint hso in
      let lgo = Option.map convert_bin_lint lso in
      (* Computation of the node_relation *)
      let nrel =
        Aa_sets.fold
          (fun (il, ir, io) acc -> Nrel.add acc (il, ir) io)
          roots_rel Nrel.empty in
      if !flag_debug_join_shape then
        Log.force "Relation found:\n%s" (Nrel.nr_2stri "  " nrel);
      (* Creation of the initial graph *)
      let g_init =
        init_graph_from_roots false nrel.n_pi xl.t_shape xr.t_shape in
      (* Satisfaction function *)
      let satl: n_cons -> bool = make_sat xl in
      let satr: n_cons -> bool = make_sat xr in
      (* Computation of graph join, and of new graph relation *)
      let g_out, onrel, instl, instr =
        Graph_join.join false
          (tr_join_arg satl (xl.t_shape, jl)) satl
          (tr_join_arg satr (xr.t_shape, jr)) satr
          hgo lgo nrel false g_init in
      (* Computation of numerical domain join *)
      (* - mappings to be used in the instantiation *)
      let map_l, map_r =
        Gen_join.extract_mappings (Graph_utils.get_all_nodes xl.t_shape)
          (Graph_utils.get_all_nodes xr.t_shape) onrel in
      if !flag_debug_join_num then
        begin
          Log.force "Renaming (left):\n%s%s"
            (Dv.t_2stri IntMap.empty "  " xl.t_num) (node_mapping_2str map_l);
          Log.force "Renaming (right):\n%s%s"
            (Dv.t_2stri IntMap.empty "  " xr.t_num) (node_mapping_2str map_r);
        end;
      (* - saturate instantiation so as to reflect pointers into sub-mems *)
      let saturate (g: graph) (inst: n_instantiation): n_instantiation =
        let f (col: n_collapsing): n_collapsing =
          (* for each predecessor, gather offsets it reaches in the sub-mem *)
          let preds = get_predecessors_of_node col.col_base g in
          let offs =
            IntSet.fold (fun i -> collect_offsets i g) preds OffSet.empty in
          { col with col_extptr = offs } in
        { inst with ins_fold = IntMap.map f inst.ins_fold } in
      let instl = saturate xl.t_shape instl
      and instr = saturate xr.t_shape instr in
      (* - instantiation and renaming function *)
      let instantiate_rename
          (inst: n_instantiation) (* node duplication, submems *)
          (map:  unit node_mapping) (* for renaming *)
          (n: Dv.t): Dv.t =
        (* - add duplicate nodes and associated equalities *)
        let n =
          IntMap.fold
            (fun i ex acc ->
              Dv.guard true (Nc_cons (Lincons1.EQ, Ne_var i, ex))
                (Dv.sv_add i acc)
            ) inst.ins_expr n in
        (* - foldings of sub-memory regions (if any needs folding) *)
        let n =
          IntMap.fold
            (fun nn col ->
              Dv.symvars_merge col.col_stride col.col_base nn
                col.col_block col.col_extptr
            ) inst.ins_fold n in
        (* - renaming *)
        let n =
          (* filtering sub-memory roots in srename, nm_suboff field setting:
           *    we only keep the roots that correspond to actual references
           *    in the output graph *)
          let map = { map with nm_suboff = node_offset_is_referred g_out } in
          let om =
            (* by changing types in the join state record, we may avoid this
             * conversion step *)
            List.fold_left
              (fun acc (o_old, i_new, o_new) ->
                assert (not (OffMap.mem o_old acc));
                OffMap.add o_old (o_new, i_new) acc
              ) OffMap.empty inst.ins_new_off in
          Dv.symvars_srename om map None n in
        (* - return *)
        if !flag_debug_array_blocks then
          Log.force "[sbase] Instantiated:\n%s"
            (Dv.t_2stri IntMap.empty "  " n);
        n in
      let n_l = instantiate_rename instl map_l xl.t_num in
      let n_r = instantiate_rename instr map_r xr.t_num in
      if !flag_debug_join_num then
        begin
          Log.force "[sbase] Renamed left:\n%s"
            (Dv.t_2stri IntMap.empty "  " n_l);
          Log.force "[sbase] Renamed right:\n%s"
            (Dv.t_2stri IntMap.empty "  " n_r);
        end;
      (* - the actual numeric join *)
      let n_out =
        match j with
        | Jjoin | Jwiden -> Dv.upper_bnd j n_l n_r
        | Jdweak ->
            Log.fatal_exn "gen_join does not implement directed weakening" in
      if !flag_debug_join_num then
        Log.force "Numeric join result:\n%s"
          (Dv.t_2stri IntMap.empty "  " n_out);
      (* Result *)
      let g_out, _ = Graph_utils.sve_sync_bot_up g_out in
      let t_out = { t_shape  = g_out;
                    t_num    = n_out;
                    t_envmod = svenv_empty; } in
      check_nodes "join-out" t_out;
      t_out, svenv_upd_embedding map_l, svenv_upd_embedding map_r

    (* Directed weakening; over-approximates only the right element *)
    let directed_weakening (hso: sym_index hint_bs option)
        (roots_rel: sym_index tri_table) (setroots_rel: sym_index tri_table)
        (xl: t) (xr: t): t * svenv_upd =
      sanity_check "dweak-l,before" true true xl;
      sanity_check "dweak-r,before" true true xr;
      (* Hint conversion *)
      let hgo = Option.map convert_bin_hint hso in
      (* Computation of the node_relation *)
      let wi =
        Aa_sets.fold
          (fun (il, ir, io) acc -> Nwkinj.add acc (il, ir) io)
          roots_rel Nwkinj.empty in
      (* Creation of the initial graph *)
      let g_init =
        init_graph_from_roots false wi.wi_img xl.t_shape xr.t_shape in
      (* Satisfaction function *)
      let satr: n_cons -> bool = make_sat xr in
      (* Computation of the directed weakening in the graph *)
      let g_out, wi =
        Graph_dir_weak.directed_weakening
          xl.t_shape xr.t_shape satr hgo wi g_init in
      (* Computation of the numerical weakened abstract value *)
      let map_r = Graph_dir_weak.extract_mapping xr.t_shape wi in
      if !flag_debug_dweak_num then
        Log.force "Renaming:\n%s%s"
          (Dv.t_2stri IntMap.empty "  " xr.t_num) (node_mapping_2str map_r);
      let map_r = { map_r with nm_suboff = fun _ -> Log.info "mapr"; true } in
      let n_r = Dv.symvars_srename OffMap.empty map_r None xr.t_num in
      if !flag_debug_dweak_num then
        Log.force "Renaming result:\n%s"
          (Dv.t_2stri IntMap.empty "  " n_r);
      (* Result *)
      let g_out, _ = Graph_utils.sve_sync_bot_up g_out in
      let t_out = sve_fix { t_shape  = g_out;
                            t_num    = n_r;
                            t_envmod = svenv_empty; } in
      sanity_check "dweak-out" true true t_out;
      t_out, svenv_upd_embedding map_r

    (* Unary abstraction, sort of incomplete canonicalization operator *)
    let local_abstract (ho: sym_index hint_us option) (x: t): t =
      if !Flags.flag_sanity_graph then
        graph_sanity_check "local_abstract,before" x.t_shape;
      (* computation of the hint for underlying *)
      (*  i.e., nodes corresponding to values of hint variables *)
      let hu =
        let t = x.t_shape in
        let f h =
          let h = convert_uni_hint h in
          let svals =
            Aa_sets.fold
              (fun root acc ->
                let nt, pte =
                  pt_edge_extract (sat_val x)
                    (root, Offs.zero) Flags.abi_ptr_size t in
                assert (nt == t);
                assert (Offs.is_zero (snd pte.pe_dest));
                Aa_sets.add (fst pte.pe_dest) acc
              ) h.hug_live h.hug_live in
          { hug_live = svals } in
        Option.map f ho in
      (* weak local abstraction on graphs *)
      let sat: n_cons -> bool = make_sat x in
      let xshape = Graph_abs.graph_abs hu sat x.t_shape in
      (* numeric domain variables need be filtered *)
      let xnodes = Graph_utils.get_all_nodes xshape in
      let xnum   = Dv.symvars_filter xnodes x.t_num in
      let o = { t_shape  = xshape;
                t_num    = xnum;
                t_envmod = svenv_empty; } in
      check_nodes "local-abs" o;
      o

    (** Unfolding support *)
    (* Returns a disjunction of cases *)
    let unfold_gen (uloc: unfold_loc) (udir: unfold_dir) (t: t)
        : (int IntMap.t (* remaning *) * t (* new abstract *)) list =
      let l =
        match uloc with
        | Uloc_main n ->
            check_nodes "unfold-arg" t;
            if !Flags.flag_sanity_graph then
              graph_sanity_check "unfold,before" t.t_shape;
            (* Remove the inductive edge, and extract inductive
             * Perform materialization for each rule *)
            let lrems =
              Graph_materialize.unfold ~submem:false n udir t.t_shape in
            (* Add predicates *)
            List.map
              (fun ur ->
                let t = sve_fix { t with t_shape  = ur.ur_g; } in
                let nnum1 =
                  List.fold_left
                    (fun nacc p -> Dv.guard true p nacc) t.t_num ur.ur_cons in
                let t = { t with t_num = nnum1 } in
                (* reduction of equal cells, determined in unfolding
                 * (in the empty segment case) *)
                let t, renaming = red_equal_cells ur.ur_eqs t in
                check_nodes "unfold-mid" t;
                if !Flags.flag_debug_materialize then
                  Log.force "Numeric value:\n%s"
                    (Dv.t_2stri IntMap.empty "  " nnum1);
                check_nodes "unfold-res" t;
                renaming, t
              ) lrems
        | Uloc_sub (i, n) ->
            let lnum = Dv.unfold i n udir t.t_num in
            List.map (fun (r, num) -> r, { t with t_num = num }) lnum in
      (* Filter out bottom values *)
      let aux msg l =
        Log.info "LLen(%s) %d" msg (List.length l);
        let i = ref 0 in
        List.iter
          (fun (_, x) ->
            Log.info "Unfold %d\n%s" !i (t_2stri "   " x);
            incr i
          ) l in
      if false then aux "pre-filter" l;
      let l = List.filter (fun (_, x) -> not (is_bot x)) l in
      if false then aux "post-filter" l;
      l

    let unfold (n: int) (t: t): t list =
      List.map snd (unfold_gen (Uloc_main n) Udir_fwd t)


    (** Cell operations *)

    (* Addition of a cell *)
    let cell_create ?(attr:node_attribute = Attr_none)
        ((si, so): onode) (sz: Offs.size) (nt: ntyp) (x: t): t =
      if !Flags.flag_sanity_graph then
        graph_sanity_check "cell_create,before" x.t_shape;
      (* creates destination node *)
      let dst, x = sv_add_fresh nt Nnone x in
      let pe = { pe_size = sz ;
                 pe_dest = dst, Offs.zero } in
      let x =
        let bsrc = si, Bounds.of_offs so in
        { x with
          t_shape = pt_edge_block_append bsrc pe x.t_shape } in
      if !Flags.flag_sanity_graph then
        graph_sanity_check "cell_create,after" x.t_shape;
      x

    (* Deletion of a cell *)
    let cell_delete ?(free:bool = false) ?(root:bool = false)
        (i: int) (x: t): t =
      let g = if root then Graph_utils.sv_unroot i x.t_shape else x.t_shape in
      let g0 = Graph_utils.pt_edge_block_destroy i g in
      let g1 = if free then Graph_utils.mark_free i g0 else g0 in
      sve_fix { x with
                t_shape = g1 }

    (* Read and Resolve cells *)
    let cell_read_one ((isrc, osrc) as src: onode) (sz: int) (x: t)
        : t * onode =
      (* determine whether the edge is in a sub-memory region,
       * i.e., whether it source is in a sub-memory range:
       *  (1) or isrc is a negative index [keep going in the same submemory]
       *  (2) either isrc,osrc is in a sub-memory range [go down] *)
      let is_in_submem =
        if isrc < 0 then (* case (1) *)
          Cl_sub_intern
        else if Dv.is_submem_address isrc x.t_num then
          match pt_edge_localize_in_graph (sat_val x) src sz x.t_shape with
          | None ->
              (* base address is sub-memory address, but offset undetermined *)
              Log.warn "LOCALIZATION ISSUE (may fail later; check this out!)";
              Cl_sub_base
          | Some pe -> (* case (2) *)
              if Dv.is_submem_content (fst pe.pe_dest) x.t_num then
                Cl_sub_base
              else
                begin
                  Log.warn "CHECK whether there may be OVERLAPPING";
                  Cl_main
                end
        else Cl_main in
      match is_in_submem with
      | Cl_sub_base ->
          Log.info "\tabout to look in sub-memory %d %s"
            isrc (Offs.t_2str osrc);
          x, Dv.submem_read (sat_val x) isrc osrc sz x.t_num
      | Cl_sub_intern ->
          Log.info "\tabout to dereference a sub-memory node";
          x, Dv.submem_deref (sat_val x) isrc osrc sz x.t_num
      | Cl_main ->
          let nt, pte = pt_edge_extract (sat_val x) src sz x.t_shape in
          if Offs.size_to_int_opt pte.pe_size = Some sz then
            sve_fix { x with t_shape = nt }, pte.pe_dest
          else
            Log.fatal_exn "cell_read: not the right size (%d,%s)"
              sz (Offs.size_2str pte.pe_size)
    (* Read AND resolve in the same time *)
    let cell_read
        (is_loc_equal: bool)
        (src: onode)      (* address of the cell *)
        (sz: int)         (* size of the cell *)
        (x: t)            (* input abstract memory *)
        : (t              (* output, may have changed e.g., when unfolding *)
           * onode        (* address of the cell IN THE OUTPUT abs. memory *)
           * onode option (* Some content if successful, None otherwise *)
          ) list =        (* list of disjuncts *)
      let rec cell_read_exc
          (count: int)
          (src: onode) (x: t)
          : (t * onode * onode option) list =
        if !Flags.flag_sanity_graph then
          graph_sanity_check "cell_read_exc, before" x.t_shape;
        try
          let x, cont = cell_read_one src sz x in
          (* if Unfold_request is not raised, src is unchanged *)
          [ x, src, Some cont ]
        with
        | Graph_sig.No_edge mess ->
            if true then (* add a flag for this print *)
              Log.info "cell_read: No_edge exception caught\n";
            if is_loc_equal then
              let eq_set =
                pt_edge_localize_in_equal (sat_val x) src x.t_shape in
              let x, renaming = red_equal_cells eq_set x in
              let is, os = src in
              cell_read_exc count (IntMap.find is renaming, os) x
            else
              [x, src, None]
        | Graph_sig.Unfold_request (i, dir) ->
            if count > 0 then
              let ncount = count - 1 in
              let l = unfold_gen i dir x in
              if !flag_debug_unfold then
                List.iteri
                  (fun i (_, u) ->
                    Log.force "Unfold<%d>:\n%s" i (t_2stri "  " u);
                  ) l;
              let l = (* apply renaming to src *)
                List.map
                  (fun (r0, u) ->
                    let isrc, osrc = src in
                    let isrc_new =
                      try IntMap.find isrc r0 with Not_found -> isrc in
                    (isrc_new, osrc), u
                  ) l in
              let l =
                List.flatten
                  (List.map
                     (fun (src, u) -> cell_read_exc ncount src u) l) in
              List.iter
                (fun (x, _, _) ->
                  check_nodes "post-cell_read_exc unfold(u)" x;
                  if !Flags.flag_sanity_graph then
                    graph_sanity_check "cell_read_exc, unfold, after" x.t_shape
                ) l;
              l
            else Log.fatal_exn "reached the maximal number of unfolds!" in
      cell_read_exc Flags.max_unfold src x
    (* Cell_resolve *)
    let cell_resolve (src: onode) (size: int) (x: t)
        : (t * onode * bool) list =
      let f (x, src, op_cont) = x, src, op_cont != None in
      List.map f (cell_read true src size x)

    (* Write into a cell *)
    let cell_write (ntyp: ntyp)
        (dst: onode) (size: int) (ne: n_expr) (x: t): t =
      (* a logger that should eventually be removed *)
      let f_log = true in
      let log i s = if f_log then Log.info "LOG[%d]: %s" i s in
      if !flag_debug_assign then
        Log.force
          "cell_write:\n kind: %s\n dest: %s\n size: %d\n expr: %s"
          (Ind_utils.ntyp_2str ntyp) (onode_2str dst) size (n_expr_2str ne);
      (* get the old points-to edge *)
      let get_old_pe (): pt_edge option =
        pt_edge_find_interval (sat_val x) (fst dst) (snd dst) size x.t_shape in
      log 0 "localizing";
      (* characterization of the place where the write should be done
       * (main-memory, or a sub-memory) *)
      let is_cell_sub =
        if fst dst < 0 then (* node is internal to sub-memory *)
          begin
            Log.info "SUBMEM: internal node";
            Cl_sub_intern
          end
        else if Dv.is_submem_address (fst dst) x.t_num then
          (* check if the edge can be localized as part of the content *)
          match get_old_pe () with
          | None -> (* not found, we cannot conclude *)
              (* this case is very unsatisfactory *)
              (* switch flag to try to debug this... *)
              Log.warn "Failed write cell localization";
              if false then
                Log.fatal_exn "localization of cell to cell write fails"
              else Cl_main
          | Some pe ->
              if Dv.is_submem_content (fst pe.pe_dest) x.t_num then Cl_sub_base
              else Cl_main
        else (* we are sure it is not part of a sub-memory *)
          Cl_main in
      log 1 "found if edge is sub";
      if !flag_debug_assign then
        Log.force "write in submem: %s" (cell_loc_2str is_cell_sub);
      (* check that a submemory contents node has only one predecessor
       * (to allow in place write);
       * - for now, we do the check, and abort when it fails
       * - eventually copy the sub-memory contents in the abstract *)
      let is_submem_updatable (i: int) (x: t): unit =
        let n = IntSet.cardinal (node_find i x.t_shape).n_preds in
        if n != 1 then
          Log.fatal_exn "submem is not updateable without a copy" in
      let is_submem_old_edge_updatable (x: t): unit =
        let ope = get_old_pe () in
        let old_dest =
          match ope with
          | None -> Log.fatal_exn "no old points-to edge"
          | Some pe -> fst pe.pe_dest in
        is_submem_updatable old_dest x in
      (* Finishing a write operation into the main memory *)
      let write_in_main (x: t) (nval: onode): t =
        let pte = { pe_size = Offs.size_of_int size;
                    pe_dest = nval } in
        let nt = pt_edge_replace (sat_val x) dst pte x.t_shape in
        sve_fix { x with t_shape = nt } in
      (* Numeric cell write, in main memory *)
      let main_num () =
        (* if the old node is not shared, do not replace it *)
        let is_one_cell =
          match get_old_pe () with
          | Some pe ->
              let ndest = node_find (fst pe.pe_dest) x.t_shape in
              let c = IntSet.cardinal ndest.n_preds in
              let is_size_eq =
                match Offs.size_to_int_opt pe.pe_size with
                | None -> false
                | Some i -> i = size in
              (* report "one_cell" only if sizes matche exactly *)
              if is_size_eq && c = 1 then Some (fst pe.pe_dest) else None
            | None -> None in
        match is_one_cell with
        | Some one_cell ->
            { x with t_num = Dv.assign one_cell ne x.t_num }
        | None ->
            let nn, x = sv_add_fresh ntyp Nnone x in
            write_in_main { x with t_num = Dv.assign nn ne x.t_num }
              (nn, Offs.zero) in
      (* Assignment main := sub, numeric case *)
      let main_sub_var_num (iright: int) =
        let nn, x = sv_add_fresh ntyp Nnone x in
        let ex = Ne_var iright in
        let x = { x with t_num = Dv.assign nn ex x.t_num } in
        write_in_main x (nn, Offs.zero) in
      (* Assignment main := sub, pointer case *)
      let main_sub_ptr (iright: int) =
        match Dv.submem_localize iright x.t_num with
        | Sl_unk -> main_sub_var_num iright
        | Sl_found (ig, off) -> write_in_main x (ig, off)
        | Sl_inblock isub ->
            (* add a node, bind it to an offset, and mutation in main *)
            let nn, x = sv_add_fresh Ntint Nnone x in
            let off = Offs.of_n_expr (Ne_var nn) in
            let nnum, on = Dv.submem_bind isub iright off x.t_num in
            write_in_main { x with t_num = nnum } on in
      let ddst = Sd_env (fst dst, snd dst) in
      log 2 "about to discriminate cases";
      (* Case analysis *)
      match ntyp, ne, is_cell_sub with
      | _, Ne_var iright, Cl_main -> (* main := ... *)
          log 3 "main := ... (mutate)";
          if iright >= 0 then (* main := main *)
            write_in_main x (iright, Offs.zero)
          else if ntyp = Ntaddr then (* main := sub, ptr *)
            main_sub_ptr iright
          else (* main := sub, num *)
            main_sub_var_num iright
      | Ntaddr, _, Cl_main -> (* main := ... *)
          log 3 "main := ... (addr)";
          begin
            match decomp_lin_opt ne with
            | None -> main_num ()
            | Some (iright,eoff) ->
                if iright >= 0 then (* main := main *)
                  write_in_main x (iright, Offs.of_n_expr eoff)
                else Log.todo_exn "cell write, ptr, main:=sub"
          end
      | _, _, Cl_main ->
          log 3 "main := ... (num)";
          main_num () (* numeric, main memory write *)
      | Ntaddr, _, Cl_sub_base -> (* sub := ... *)
          log 3 "sub := ... (addr)";
          (* - check that the submem can be updated in place *)
          is_submem_old_edge_updatable x;
          (* - perform a write in the sub-memory
           *   . after creating a node in the case of sub := main
           *   . without a node creation in the case of sub := sub
           * - schedule no main memory write *)
          begin
            match decomp_lin_opt ne with
            | None -> Log.todo_exn "cell_write, ptr, sub_base, none"
            | Some (iright,eoff) -> (* sub := ... *)
                let rhs =
                  if iright >= 0 then (* sub := main *)
                    Rv_addr (iright, Offs.of_n_expr eoff)
                  else (* sub := sub *)
                    Rv_expr ne in
                { x with t_num = Dv.write_sub ddst size rhs x.t_num }
          end
      | Ntaddr, _, Cl_sub_intern ->
          (* should be very similar to the case below, save for the
           * kind of expression that need be passed to write_sub *)
          log 3 "x_in_sub := ... (ptr)";
          Log.todo_exn "cell_write, in submem, pointer"
      | _, _, Cl_sub_intern ->
          log 3 "x_in_sub := ... (num)";
          Log.info "dest: %s" (onode_2str dst);
          let sv_sub =
            match Dv.submem_localize (fst dst) x.t_num with
            | Sl_unk   -> Log.fatal_exn "sub = ... (num), loc unk"
            | Sl_found (isub, off) ->
                Log.fatal_exn "sub = ... (num), loc-f, %d" isub
            | Sl_inblock isub -> isub in
          is_submem_updatable sv_sub x;
          let ddst = Sd_int (fst dst, snd dst) in
          { x with t_num = Dv.write_sub ddst size (Rv_expr ne) x.t_num }
      | _, _, Cl_sub_base ->
          log 3 "sub := ... (num)";
          (* - check that the submem can be updated in place *)
          is_submem_old_edge_updatable x;
          (* - perform a write in the sub-memory *)
          { x with t_num = Dv.write_sub ddst size (Rv_expr ne) x.t_num }


    (** Transfer functions *)

    (* Condition test *)
    let rec guard (c: n_cons) (x: t): t =
      if !Flags.flag_sanity_graph then
        graph_sanity_check "guard,before" x.t_shape;
      if !flag_debug_guard then
        Log.force "guard: %s\n%s"
          (n_cons_2str c) (Dv.t_2stri IntMap.empty "  " x.t_num);
      let r =
        (* first, apply the guard in the graph if the expression
         * is not a sub-memory expression *)
        let gtest =
          let is_main = n_cons_fold (fun i b -> b && i >= 0) c true in
          if is_main then graph_guard true c x.t_shape
          else Gr_no_info in
        (* then, apply  *)
        match gtest with
        | Gr_bot -> (* test in the graph level yields _|_ *)
            { x with t_num = Dv.bot }
        | Gr_no_info -> (* conventional guard function *)
            { x with t_num = Dv.guard true c x.t_num }
        | Gr_equality (irem, ikeep) -> (* equality reduction *)
            fst (red_equal_cells (PairSet.singleton (irem, ikeep)) x)
        | Gr_emp_seg i ->
            let x, renaming = red_empty_segment i x in
            let c =
              if IntMap.is_empty renaming then c
              else
                n_cons_map
                  (fun i ->
                    try IntMap.find i renaming with Not_found -> i
                  ) c in
            guard c x
        | Gr_emp_ind i ->
            (* this would allow removing inductives corresponding to
             * a empty region, and prevent join imprecisions
             * though, in many cases, it also loses important
             * information about actual inductive arguments, so it
             * cannot be activated yet *)
            { x with
              (*t_shape = ind_edge_rem i tt.t_shape;*)
              t_num   = Dv.guard true c x.t_num } in
      if !flag_debug_guard then
        Log.force "Domshape guard [%s]\n . Before:\n%s\n . After:\n%s"
          (n_cons_2str c) (Dv.t_2stri IntMap.empty "   " x.t_num)
          (Dv.t_2stri IntMap.empty "   " r.t_num);
      let x = sve_fix r in
      if !Flags.flag_sanity_graph then
        graph_sanity_check "guard,after" x.t_shape;
      x

    (* Checking that a constraint is satisfied *)
    let sat (c: n_cons) (x: t): bool =
      if !Flags.flag_sanity_graph then
        graph_sanity_check "sat, before" x.t_shape;
      Dv.sat x.t_num c


    (** Set domain *)
    let setv_add_fresh _ = Log.todo_exn "setv_add_fresh"
    let setv_delete _ = Log.todo_exn "setv_delete"

    (** Assuming and checking inductive edges *)

    (* Unfold *)
    let ind_unfold (u: unfold_dir) ((n,o): onode) (t: t): t list =
      assert (Offs.is_zero o);
      match u with
      | Udir_fwd ->
          if Graph_utils.node_is_ind n t.t_shape then
            (* there is an inductive edge to unfold *)
            unfold n t
          else
            (* there is no edge to unfold, we keep the abstract state as is *)
            [ t ]
      | Udir_bwd ->
          (* unfolding should affect a segment edge TO node n
           *  => thuse we should first localize such a segment
           * nb: fails if there is zero or several choices *)
          let s = seg_edge_find_to n t.t_shape in
          let card = IntSet.cardinal s in
          if card = 1 then
            begin
              Log.info "SUCCESS: %d" (IntSet.min_elt s);
              List.map snd
                (unfold_gen (Uloc_main (IntSet.min_elt s)) Udir_bwd t)
            end
          else (* failure case *)
            begin
              Log.info "FAILURE";
              [ t ]
            end

    (* Prepare parameters for ind_edge  *)
    let prepare_pars
        (tref: t) (* for evaluation of pointer fields *)
        (mayext: bool) (* whether graph may need extension *)
        (ic: onode gen_ind_call)
        (t: t) (* for evaluation of pointer fields *)
      : t (* graph produced *)
        * (nid * n_cons) list
        * int list =
      assert (mayext != (tref == t));
      let ind = Ind_utils.ind_find ic.ic_name in
      (* Allocation of the node arguments, for integer parameters *)
      let comp_t, comp_ipars =
        match ic.ic_pars with
        | None -> t, [ ]
        | Some iii ->
            assert (List.length iii.ic_int = ind.i_ipars);
            List.fold_left
              (fun (accg, accl) -> function
                | Ii_const i ->
                    (* add a fresh node, and generate a constraint
                     * that it be equal to i *)
                    let n, ng = sv_add_fresh Ntint Nnone accg in
                    Log.info "int parameter: |%d| => %d" n i;
                    ng, (n, Nc_cons (Tcons1.EQ, Ne_var n, Ne_csti i)) :: accl
                | Ii_lval _ -> Log.fatal_exn "non supported lval parameter"
              ) (t, [ ]) (List.rev iii.ic_int) in
      (* Reading the location of ptr parameters *)
      let comp_t1, comp_ppars =
        match ic.ic_pars with
        | None -> comp_t, [ ]
        | Some iii ->
            assert (List.length iii.ic_ptr = ind.i_ppars);
            List.fold_left
              (fun ((acct: t), accl) ((n,off): onode) ->
                let nacct =
                  if mayext && not (node_mem n acct.t_shape) then
                    let nn = node_find n tref.t_shape in
                    let nt = sv_add n nn.n_t nn.n_alloc acct.t_shape in
                    { acct with t_shape = nt }
                  else acct in
                assert (Offs.is_zero off);   (* should evaluate to zero off *)
                nacct, n :: accl
              ) (comp_t, [ ]) (List.rev iii.ic_ptr) in
      if not mayext then assert (comp_t1 == comp_t);
      comp_t1, comp_ipars, comp_ppars

    (* Utility function for the assumption and the checking of segments *)
    let make_seg_edge
        (tref: t) (* for evaluation of pointer fields *)
        (mayext: bool) (* whether graph may need extension *)
        (i: nid) (ic: onode gen_ind_call)
        (i_e: nid) (ic_e: onode gen_ind_call)
        (t: t)
        : t (* graph produced *)
          * (nid * n_cons) list
          *  node_emb (* intial mapping, for inclusion *) =
      (* Modification only if different graph for evaluation *)
      assert (mayext != (tref == t));
      assert (ic.ic_name = ic_e.ic_name);
      let ind = Ind_utils.ind_find ic.ic_name in
      (* Allocation of the node arguments, for integer parameters *)
      let comp_t1, comp_ipars, comp_ppars =
        prepare_pars tref mayext ic t in
      let comp_t2, comp_ipars_e, comp_ppars_e =
        prepare_pars tref mayext ic_e comp_t1 in
      (* Construction of the inductive edge *)
      let ie = { se_ind  = ind ;
                 se_sargs = { ia_ptr = comp_ppars ;
                              ia_int = List.map fst comp_ipars };
                 se_dargs = { ia_ptr = comp_ppars_e ;
                              ia_int = List.map fst comp_ipars_e};
                 se_dnode = i_e; } in
      (* Construction of the adequate injection *)
      let inj =
        let f = List.fold_left (fun acc i -> Aa_maps.add i i acc) in
        f (f (Aa_maps.add i_e i_e (Aa_maps.singleton i i)) comp_ppars)
          comp_ppars_e in
      let tn = { comp_t2 with t_shape = seg_edge_add i ie comp_t2.t_shape } in
      tn, List.rev_append comp_ipars comp_ipars_e, inj

    (* Utility function for the assumption and the checking of ind edges *)
    let make_ind_edge
        (tref: t) (* for evaluation of pointer fields *)
        (mayext: bool) (* whether graph may need extension *)
        (i: nid) (ic: onode gen_ind_call) (t: t)
        : t (* graph produced *)
        * (nid * n_cons) list
        * node_emb (* intial mapping, for inclusion *) =
      let ind = Ind_utils.ind_find ic.ic_name in
      let comp_t1, comp_ipars, comp_ppars =
        prepare_pars  tref mayext ic t in
      (* Construction of the inductive edge *)
      let ie = { ie_ind  = ind ;
                 ie_args = { ia_ptr = comp_ppars ;
                             ia_int = List.map fst comp_ipars } } in
      (* Construction of the adequate injection *)
      let inj =
        let f = List.fold_left (fun acc i -> Aa_maps.add i i acc) in
        (* HS: we do not understand the next line *)
        f (f (Aa_maps.singleton i i) comp_ppars) comp_ppars in
      let tn = { comp_t1 with t_shape = ind_edge_add i ie comp_t1.t_shape } in
      tn, comp_ipars, inj

    (* Assume construction: assume an inductive predicate *)
    let assume (op: meml_log_form) (x: t): t =
      match op with
      | SL_set _ -> Log.todo_exn "assume Setprop"
      | SL_ind (ic, (i, off)) ->
          (* Assume construction: assume an inductive predicate *)
          if inductive_is_allowed ic.ic_name then
            begin
              if !Flags.flag_sanity_graph then
                graph_sanity_check "assume,before" x.t_shape;
              assert (Offs.is_zero off);
              (* Generate the arguments (temp: only constants) *)
              let comp_t, comp_ipars, _ = make_ind_edge x false i ic x in
              (* Taking into account all relations *)
              let comp_n =
                List.fold_left
                  (fun acc_n (_, i_ctr) ->
                    Dv.guard true i_ctr acc_n
                  ) comp_t.t_num comp_ipars in
              { t_shape  = comp_t.t_shape;
                t_num    = comp_n;
                t_envmod = svenv_empty; }
            end
          else x
      | SL_seg (ic, (i, off), ic_e, (i_e, off_e)) ->
          (* Assume construction: assume a segment predicate *)
          assert (ic.ic_name = ic_e.ic_name);
          if inductive_is_allowed ic.ic_name then
            begin
              if !Flags.flag_sanity_graph then
                graph_sanity_check "assume,before" x.t_shape;
              assert (Offs.is_zero off);
              assert (Offs.is_zero off_e);
              (* Generate the arguments (temp: only constants) *)
              let comp_t, comp_ipars, _ =
                make_seg_edge x false i ic i_e ic_e x in
              (* Taking into account all relations *)
              let comp_n =
                List.fold_left
                  (fun acc_n (_, i_ctr) ->
                    Dv.guard true i_ctr acc_n
                  ) comp_t.t_num comp_ipars in
              (* Taking into account all relations *)
              { t_shape  = comp_t.t_shape;
                t_num    = comp_n;
                t_envmod = svenv_empty; }
            end
          else x
      | SL_array ->
          { x with t_num = Dv.assume Opd0.SL_array x.t_num }

    let f_trans (inj: int IntMap.t) (j: int): int =
      try IntMap.find j inj
      with Not_found -> Log.fatal_exn "renaming failed (dom_shape) %d" j

    (* part common to ind_check and seg_check *)
    let final_check (tref: t) (comp_ipars: (int * Nd_sig.n_cons) list)
        (inj: (int, int) Aa_maps.t) (x: t): bool =
      let r =
        Graph_is_le.is_le_partial None false false x.t_shape None
          IntSet.empty (make_sat x) tref.t_shape inj in
      match r with
      | Ilr_not_le | Ilr_le_seg _ -> false
      | Ilr_le_ind _ -> Log.fatal_exn "is_le returned an inductive"
      | Ilr_le_rem (_, _, inj, inst) ->
          assert (inst = IntMap.empty);
          (* Renaming and verification of the numeric relations *)
          List.for_all
            (fun (i, cons) ->
              let rcons = n_cons_map (f_trans inj) cons in
              if !Flags.flag_debug_check_ind then
                Log.force "Check constraint %d => %s\nval num:\n%s" i
                  (n_cons_2str rcons) (Dv.t_2stri IntMap.empty "  " x.t_num);
              Dv.sat x.t_num rcons
            ) comp_ipars

    let check (op: meml_log_form) (x: t): bool =
      match op with
      | SL_set _ -> Log.todo_exn "check Setprop"
      | SL_ind (ic, (i, off)) ->
          (* Check construction, that an inductive be there *)
          if !Flags.flag_sanity_graph then
            graph_sanity_check "ind_check,before" x.t_shape;
          if Dv.is_submem_address i x.t_num then
            (* inductive edge checking should be delegated to the sub-memory;
             *  - for now parameters are not handled in inductive to check *)
            if ic.ic_pars != None then
              Log.todo_exn "ind_check, sub-memory, with parameters"
            else Dv.check (Opd0.SL_ind (i, off, ic.ic_name)) x.t_num
          else if not (Offs.is_zero off) then
            Log.fatal_exn "ind_check, main memory, but non zero offset"
          else (* "normal" case, inductive leaving in the main memory *)
            (* Generate the arguments (temp: only constants) *)
            let tref, comp_ipars, inj =
              let t0 = add_node i Ntaddr Nnone (top ()) in
              make_ind_edge x true i ic t0 in
            final_check tref comp_ipars inj x
      | SL_seg (ic, (i, off), ic_e, (i_e, off_e)) ->
          if !Flags.flag_sanity_graph then
            graph_sanity_check "seg_check,before" x.t_shape;
          assert(Offs.is_zero off);
          assert(Offs.is_zero off_e);
          (* we don't deal with submem at the moment *)
          (* Generate the arguments (temp: only constants) *)
          if ic = ic_e && (i, off) = (i_e, off_e) then
            true
          else
            let tref, comp_ipars, inj =
              let t0 = add_node i   Ntaddr Nnone (top ()) in
              let t0 = add_node i_e Ntaddr Nnone t0 in
              make_seg_edge x true i ic i_e ic_e t0 in
            final_check tref comp_ipars inj x
      | SL_array ->
          Dv.check Opd0.SL_array x.t_num
  end : DOM_MEM_LOW)
