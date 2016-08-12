(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_mem_low_list.ml
 **       a simplified inductive domain based on lists
 **       - no arbitrary inductives;
 **       - set parameters.
 ** Xavier Rival, 2014/02/23 *)
open Data_structures
open Flags
open Lib
open Offs

open Dom_sig
open Graph_sig
open Ind_sig
open Inst_sig
open List_sig
open Nd_sig
open Sv_sig
open Svenv_sig
open Ast_sig

open Dom_utils
open Inst_utils
open List_utils
open Nd_utils
open Set_sig
open Set_utils

open Apron

(** Error report *)
module Log =
  Logger.Make(struct let section = "dm_ll___" and level = Log_level.DEBUG end)

(** Simplified functor:
 *  This module supports a lot fewer things than the dom_mem_low_shape does
 *   - simpler cell resolution;
 *   - no sub-memories;
 *   - no backward unfolding;
 **)
module DBuild = functor (Dv: DOM_VALSET) ->
  (struct
    (** Module name *)
    let module_name = "[list]"
    (** Dom ID *)
    let dom_id: mod_id ref = ref (-1, "list")

    (** Type of symbolic indexes *)
    type sym_index = int (* int for the list domain implementation *)
    type off_sym_index = sym_index * Offs.t

    (** Abstract value types *)
    type t =
        { (* memory contents *)
          t_mem:    lmem;
          (* abstraction of values *)
          t_num:    Dv.t;
          (* local modification *)
          t_svemod: svenv_mod }

    (** Domain initialization to a set of inductive definitions *)

    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (g: Keygen.t) (s: StringSet.t): Keygen.t =
      let g, k = Keygen.gen_key g in (* this domain generates keys *)
      if s != StringSet.empty then
        Log.fatal_exn "init_inductives not allowed";
      if sv_upg then dom_id := k, snd !dom_id;
      g
    let inductive_is_allowed (name: string): bool =
      not ((Ind_utils.ind_find name).i_list = None)

    (** Fixing sets of keys *)
    let sve_sync_bot_up (x: t): t * svenv_mod =
      { x with t_svemod = svenv_empty }, x.t_svemod

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t =
      { t_mem    = lmem_empty;
        t_num    = Dv.bot;
        t_svemod = svenv_empty; }
    let is_bot (x: t) = Dv.is_bot x.t_num
    (* Top element, with empty set of roots *)
    let top (): t =
      { t_mem    = lmem_empty;
        t_num    = Dv.top;
        t_svemod = svenv_empty; }

    (** Pretty-printing and output *)
    let t_2stri (ind: string) (x: t): string =
      Printf.sprintf "%s%s" (List_utils.lmem_2stri ind x.t_mem)
        (Dv.t_2stri IntMap.empty ind x.t_num)
    let t_2str: t -> string = t_2stri ""
    (* External output *)
    let ext_output (o: output_format) (base: string) (namer: namer) (x: t)
        : unit =
      Log.todo_exn "ext output"

    (** Sanity checks *)
    let sanity_check (ctxt: string) (x: t): unit =
      (* - collect SVs in the memory abstraction
       * - check that the numerical domain speaks about exacty these SVs *)
      if !Flags.flag_sanity_env then
        let snodes = List_utils.sv_col x.t_mem in
        if Flags.flag_sanity_env_pp then
          Log.info "domlist,sanity_check<%s>, memory nodes: { %s }\n%s"
            ctxt (IntSet.t_2str "; " snodes) (svenv_2stri "  " x.t_svemod);
        let is_valid = Dv.symvars_check snodes x.t_num in
        if Flags.flag_sanity_env_pp then
          Log.info "domlist,sanity_check<%s>: %b" ctxt is_valid;
        if not is_valid then
          begin
            Log.info "check_nodes(%s): inconsistent num keys" ctxt;
            Log.fatal_exn "check_nodes failed"
          end;
        Log.info "domlist,sanity_check<%s>: ok" ctxt

    (** Management of symbolic variables *)
    (* Ensuring consistency of SVs *)
    let sve_fix (msg: string) (x: t): t =
      let loc_debug = false in
      if loc_debug then
        Log.info "Doing sve_fix (%s):\n%s" msg (t_2stri "  " x);
      let m0, svm = List_utils.sve_sync_bot_up x.t_mem in
      if loc_debug then
        Log.info "playing add_rem:\n%s" (svenv_2stri "  " svm);
      { t_mem    = m0;
        t_num    = Dv.sve_sync_top_down svm x.t_num;
        t_svemod = svenv_join x.t_svemod svm }
    (* Check whether an SV can be created in the current domain *)
    let sv_is_allowed ?(attr: node_attribute = Attr_none) (nt: ntyp)
        (na: nalloc) (x: t): bool = true
    (* Addition of a fresh symbolic variable *)
    let sv_add_fresh ?(attr: node_attribute = Attr_none) ?(root: bool = false)
        (nt: ntyp) (na: nalloc) (x: t): sym_index * t =
      (* consider adding a sanity check *)
      let i, m0 = List_utils.sv_add_fresh ~root:root nt x.t_mem in
      i, sve_fix "sv_add_fresh" { x with t_mem = m0 }
    let sv_get_info (i: int) (x: t): nalloc option * ntyp option = 
      Log.warn "sv_get_info imprecise";
      None, None
    let gc (roots: sym_index uni_table) (x: t): t =
      let mem, s = List_utils.gc roots x.t_mem in
      let num = 
        IntSet.fold
          (fun i acc ->
            try
              if Dv.setv_is_root i acc then acc else Dv.setv_rem i acc
            with _ -> acc (* was already removed... *)
          ) s x.t_num in
      sve_fix "gc" { x with 
                     t_mem = mem;
                     t_num = num; }

    (** Management of setvs *)
    let setv_add (setv: int) (t: t): t =
      let mem = setv_add false setv t.t_mem in
      { t with
        t_mem = mem ;
        t_num = Dv.setv_add ~root:false ~name:None setv t.t_num }
    let setv_add_fresh (isroot: bool) (s: string) (t: t): int * t =
      let i, mem = setv_add_fresh isroot None t.t_mem in
      i, { t with
           t_num = Dv.setv_add ~root:isroot ~name:(Some s) i t.t_num;
           t_mem = mem }
    let setv_delete (i: int) (t: t): t =
      { t with
        t_mem = setv_rem i t.t_mem;
        t_num = Dv.setv_rem i t.t_num }
    let setv_delete_non_root (i: int) (x: t): t =
      if Dv.setv_is_root i x.t_num then x
      else setv_delete i x

    (** Utility functions for the manipulation of abstract values *)
    (* Satifying function in the value domain *)
    let sat_val (t: t) (c: n_cons): bool =
      if !Flags.flag_debug_block_sat then
        Log.force "sat called: %s\n%s" (n_cons_2str c)
          (Dv.t_2stri IntMap.empty "      " t.t_num);
      Dv.sat t.t_num c

    (** Graph encoding (used for guiding join) *)
    let encode (disj: int) (n: namer) (x: t)
        : renamed_path list * PairSetSet.t * int =
      Log.todo_exn "encode"

    (** Comparison and Join operators *)
    (* Function to check constraint satisfaction on a t *)
    let make_sat (x: t) (nn: n_cons): bool =
      match nn with
      | Nc_cons (Tcons1.DISEQ, Ne_csti 0, Ne_var i)
      | Nc_cons (Tcons1.DISEQ, Ne_var i, Ne_csti 0) ->
          if List_utils.pt_edge_mem (i, Offs.zero) x.t_mem then true
          else Dv.sat x.t_num nn
      | _ -> Dv.sat x.t_num nn
    let make_setsat (x: t) (sc: set_cons): bool = Dv.set_sat sc x.t_num

    (* set variable collection: containing two parts: collecting all the *
     * set variables from the shape and the root set variables in the set *
     * domain *)   
    let setv_col (x: lmem) (s: 'a): IntSet.t =
      let setv = 
        IntMap.fold
          (fun i n acc -> 
            match n.ln_e with
            | Lhlist ld -> 
                List.fold_left (fun acc i -> IntSet.add i acc) acc ld.lc_args
            | Lhlseg (ld, _) -> 
                List.fold_left (fun acc i -> IntSet.add i acc) acc ld.lc_args
            | _ -> acc
          )  x.lm_mem IntSet.empty in
      IntSet.union (Dv.setv_col_root s) setv

    (* Join and widening *)
    let join (j: join_kind) (hso: sym_index hint_bs option)
        (lso: (onode lint_bs) option)
        (roots_rel: sym_index tri_table) (setroots_rel: sym_index tri_table)
        ((xl, jl): t * join_ele) ((xr, jr): t * join_ele)
        : t * svenv_upd * svenv_upd =
      let loc_debug = false in
      sanity_check "join-l,before" xl; sanity_check "join-r,before" xr;
      (* apparently, the hint has been deprecated; clean it up ? *)
      let hgo = Option.map (fun h -> { hbg_live = h.hbs_live }) hso in
      (* Computation of the node_relation *)
      let nrel =
        Aa_sets.fold
          (fun (il, ir, io) acc -> Graph_utils.Nrel.add acc (il, ir) io)
          roots_rel Graph_utils.Nrel.empty in
      (* Computation of setvar_relation *)
      let srel =
        Aa_sets.fold
          (fun (il, ir, io) acc -> Graph_utils.Nrel.add acc (il, ir) io)
          setroots_rel Graph_utils.Nrel.empty in
      (* Creation of the initial graph *)
      let m_init, toaddl, toaddr, torem =
        init_from_roots nrel.n_pi srel.n_pi xl.t_mem xr.t_mem in
      let xl = IntSet.fold setv_add toaddl xl
      and xr = IntSet.fold setv_add toaddr xr in
      if !flag_debug_join_num || loc_debug then
        Log.force "Homogeneous:\n- left: %s\n%s- right: %s\n%s"
          (intset_2str toaddl) (Dv.t_2stri IntMap.empty "      " xl.t_num)
          (intset_2str toaddr) (Dv.t_2stri IntMap.empty "      " xr.t_num);
      (* Satisfaction function *)
      let satl: n_cons -> bool = make_sat xl in
      let satr: n_cons -> bool = make_sat xr in
      (* Computation of graph join, and of new graph relation *)
      let join_out =
        List_join.join xl.t_mem satl (make_setsat xl) xr.t_mem 
          satr (make_setsat xr) hgo nrel srel false m_init in
      let jo = join_out in
      (* Preparation of the mapping for used to nodes rename *)
      let node_map_l, node_map_r =
        Gen_join.extract_mappings (sv_col xl.t_mem) (sv_col xr.t_mem) 
          join_out.rel in
      (* Complete instantiation of set variables following guesses (if any) *)
      if !flag_debug_join_num || loc_debug then
        Log.force "Before inst/renaming:\n- left:\n%s%s- right:\n%s%s"
          (setv_inst_2stri " " jo.instset_l)
          (Dv.t_2stri IntMap.empty "      " xl.t_num)
          (setv_inst_2stri " " jo.instset_r)
          (Dv.t_2stri IntMap.empty "      " xr.t_num);
      let roots = setv_roots xl.t_mem in
      let instl = setv_inst_complete roots (make_setsat xl) jo.instset_l in
      let instr = setv_inst_complete roots (make_setsat xr) jo.instset_r in
      (* When either instantiation has non bound variables,
       * inherit from the other *)
      let instl = setv_inst_strengthen instr instl in
      let instr = setv_inst_strengthen instl instr in
      (* Instantiation of the set variables *)
      if !flag_debug_join_num || loc_debug then
        Log.force "Strengthened instantiations:\n- left:\n%s- right:\n%s"
          (setv_inst_2stri "   " instl) (setv_inst_2stri "   " instr);
      let f_add_cons (inst: setv_inst) xnum =
        (* - add new setvs *)
        let xnum = Inst_utils.fold_add Dv.setv_add inst xnum in
        (* - add new constraints *)
        let xnum =
          IntMap.fold
            (fun i ex acc ->
              if loc_debug then
                Log.info "Adding_cons: %d |=> %s" i (set_expr_2str ex);
              Dv.set_guard (S_eq (S_var i, ex)) acc
            ) inst.setvi_eqs xnum in
        let xnum =
          List.fold_left (fun acc c -> Dv.set_guard c acc)
            xnum inst.setvi_props in
        (* - verify that the instantiation is admissible *)
        List.iter
          (fun c ->
            if loc_debug then
              Log.info "verifying constraint %s" (set_cons_2str c);
            if not (Dv.set_sat c xnum) then
              Log.fatal_exn "instantiation fails: %s"
                (Set_utils.set_cons_2str c)
          ) inst.setvi_prove;
        (* - remove the deprecated setvs *)
        Log.info "tmp,setv,f_add_cons";
        Inst_utils.fold_rem Dv.setv_rem inst xnum in
      let num_l = f_add_cons instl xl.t_num in
      let num_r = f_add_cons instr xr.t_num in
      if !flag_debug_join_num || loc_debug then
        Log.force "Inst done:\n- left:\n%s- right:\n%s"
          (Dv.t_2stri IntMap.empty "      " num_l)
          (Dv.t_2stri IntMap.empty "      " num_r);
      (* Removing the setvs that are not in the join result *)
      Log.info "tmp,setv,join,num";
      let num_l = IntSet.fold Dv.setv_rem torem num_l in
      let num_r = IntSet.fold Dv.setv_rem torem num_r in
      if !flag_debug_join_num || loc_debug then
        Log.force "Removal done:\n- left:\n%s- right:\n%s"
          (Dv.t_2stri IntMap.empty "      " num_l)
          (Dv.t_2stri IntMap.empty "      " num_r);
      (* Renaming the svs *)
      let instantiate (map: unit node_mapping) (n1: Dv.t) =
        let om = OffMap.empty
        and map = { map with nm_suboff = (fun _ -> false) } in
        Dv.symvars_srename om map None n1 in
      let num_l = instantiate node_map_l num_l in
      let num_r = instantiate node_map_r num_r in
      if !flag_debug_join_num || loc_debug then
        Log.force "Renaming of SV done:\n- left:\n%s- right:\n%s"
          (Dv.t_2stri IntMap.empty "      " num_l)
          (Dv.t_2stri IntMap.empty "      " num_r);
      (* Join in the num + set domain *)
      let n_out =
        match j with
        | Jjoin | Jwiden -> Dv.upper_bnd j num_l num_r
        | Jdweak ->
            Log.fatal_exn "gen_join does not implement directed weakening" in
      if !flag_debug_join_num || loc_debug then
        Log.force "Numeric join result:\n%s"
          (Dv.t_2stri IntMap.empty "  " n_out);
      (* Result *)
      let m_out, _ = List_utils.sve_sync_bot_up join_out.out in
      let m_out = IntSet.fold setv_rem torem m_out in
      let m_out = Inst_utils.fold_rem setv_rem jo.instset_l m_out in
      let t_out = { t_mem    = m_out;
                    t_num    = n_out;
                    t_svemod = svenv_empty } in
      sanity_check "join,after" t_out;
      let t_num =
        Dv.symvars_filter (sv_col t_out.t_mem) 
          ~set_vars:(setv_col t_out.t_mem t_out.t_num) t_out.t_num in
      let t_out = { t_out with t_num = t_num } in
      if loc_debug then Log.info "join-exit:\n%s" (t_2stri "   " t_out);
      t_out, svenv_upd_embedding node_map_l, svenv_upd_embedding node_map_r

    (* Checks if the left argument is included in the right one *)
    let is_le (ninj: sym_index bin_table) (sinj: sym_index bin_table)
        (xl: t) (xr: t): svenv_upd option =
      sanity_check "is_le,l,before" xl;
      sanity_check "is_le,r,before" xr;
      (* function to test whether a condition is satisfied *)
      let satl: n_cons -> bool = make_sat xl in
      let ssatl: set_cons -> bool = make_setsat xl in
      (* launching the graph algorithm and processing its output *)
      let is_le = List_is_le.is_le xl.t_mem satl ssatl xr.t_mem ninj sinj in
      match is_le with
      | `Ilr_not_le -> None
      | `Ilr_le (inj, sinj, s_info)->
          if !flag_debug_is_le_gen then
            begin
              let smap = IntMap.t_2str "" string_of_int inj in
              let setv_map = IntMap.t_2str "" (IntSet.t_2str ";") sinj in
              Log.force "Comparison: is_le holds in the shape!";
              Log.force "Numerics:\n%sMapping:\n%s\n%s"
                (Dv.t_2stri IntMap.empty "  " xr.t_num) smap setv_map
            end;
          let nodes = sv_col xl.t_mem in
          (* instantiation of node relation *)
          let inj_rel: (int * Offs.t) node_mapping =
            IntMap.fold
              (fun i j -> Nd_utils.add_to_mapping j i) inj
              { nm_map    = IntMap.empty ;
                nm_rem    = nodes;
                nm_suboff = fun _ -> true } in
          (* instantiation of the set relation *)
          (* instantiation of set variable relation *)
          let sinj_rel, setv_l =
            IntMap.fold 
              (fun i j (acc_map, acc_set) ->
                IntSet.fold
                  (fun j_e (acc_map, acc_set) ->
                    Set_utils.add_to_mapping j_e i acc_map,
                    IntSet.add i acc_set
                  ) j (acc_map, acc_set)
              ) sinj (Set_utils.setv_mapping_empty, IntSet.empty) in
          let n_l =
            Dv.symvars_srename ~mark:false OffMap.empty inj_rel
              (Some sinj_rel) xl.t_num in
          let b = Dv.is_le n_l xr.t_num (fun i j -> false) in
          let r =
            if b then
              let svu = svenv_upd_embedding { inj_rel with 
                                              nm_suboff = fun _ -> true } in
              Some svu
            else None in
          if !flag_debug_is_le_gen then
            Log.force "Numeric comparison: %s\nleft:\n%sright:\n%s"
              (if r = None then "false" else "true")
              (Dv.t_2stri IntMap.empty "   " n_l)
              (Dv.t_2stri IntMap.empty "   " xr.t_num);
          r
    let directed_weakening _ = Log.todo_exn "dw"
    (* Unary abstraction, sort of incomplete canonicalization operator *)
    let local_abstract (ho: sym_index hint_us option) (x: t): t =
      sanity_check "local_abstract,before" x;
      (* computation of the hint for underlying *)
      (*  i.e., nodes corresponding to values of hint variables *)
      let hu =
        let m = x.t_mem in
        let f h =
          Aa_sets.fold
            (fun root acc ->
              let nm, pte =
                pt_edge_extract (sat_val x)
                  (root, Offs.zero) Flags.abi_ptr_size m in
              assert (nm == m);
              assert (Offs.is_zero (snd pte.pe_dest));
              Aa_sets.add (fst pte.pe_dest) acc
            ) h.hus_live h.hus_live in
        Option.map f ho in
      (* weak local abstraction on graphs *)
      let sat: n_cons -> bool = make_sat x in
      let m, inj, sinj, (*set,*) s_info =
        List_abs.local_abstract ~stop:hu sat (make_setsat x) x.t_mem in
      (* prove set domain imply relation *)
      let svs = List_utils.sv_col m in
      let setvs = setv_col m x.t_num in
      let num = Dv.symvars_filter svs ~set_vars:setvs x.t_num in
      let o = { t_mem    = m;
                t_num    = num;
                t_svemod = svenv_empty; } in
      sanity_check "local_abstract,after" o;
      o

    (** Unfolding support *)
    let unfold (i: int) (x: t): t list =
      let l = List_mat.unfold i x.t_mem in
      let l =
        List.map
          (fun ur ->
            let x = sve_fix "unfold" { x with t_mem = ur.ur_lmem; } in
            let n =
              IntMap.fold (fun i _ -> Dv.setv_add i) ur.ur_newsetvs x.t_num in
            let n =
              List.fold_left (fun n c -> Dv.guard true c n) n ur.ur_cons in
            let n =
              List.fold_left (fun n c -> Dv.set_guard c n) n ur.ur_setcons in
            let n = IntSet.fold Dv.setv_rem ur.ur_remsetvs n in
            let m = IntSet.fold setv_rem ur.ur_remsetvs x.t_mem in
            { x with
              t_mem = m;
              t_num = n }
          ) l in
      let l = List.filter (fun x -> not (is_bot x)) l in
      l

    (* Non local unfolding support *)
    let nonlocal_unfold (i: int) (x: t): t list * IntSet.t =
      let lm = x.t_mem in
      (* Global search through the abstract heap, for a node carrying an
       * inductive or segment predicate, such that SV i may be an
       * element of the structure *)
      (* XR: what happens when there are several solutions ? *)
      let var_set, ld_def_opt =
        IntMap.fold
          (fun key elt (acc, ld_def_opt) ->
            let heap_frag = elt.ln_e in
            match heap_frag with
            | Lhemp
            | Lhpt _ -> (acc, ld_def_opt)
            | Lhlist { lc_def; lc_args }
            | Lhlseg ({ lc_def; lc_args }, _) ->
                match lc_def.ld_set with
                | None      -> (acc, ld_def_opt)
                | Some seti ->
                    match seti.s_uf_seg with
                    | None -> (acc, ld_def_opt)
                    | Some argnum ->
                        let arg = List.nth lc_args argnum in
                        IntMap.add key (arg, heap_frag) acc, Some lc_def
          ) lm.lm_mem (IntMap.empty, None) in
      let ld_def =
        match ld_def_opt with
        | None -> raise (Failure "non_local_unfolding")
        | Some ld_def -> ld_def in
      (* Filters the addresses found at stage 1, where the node could be the
       * address of a block of the right size *)
      let var_sy =
        IntMap.fold
          (fun key elt acc ->
            match elt.ln_e with
            | Lhpt pt_edge_blk -> 
                begin
                  if ld_def.ld_size = Block_frag.byte_size pt_edge_blk then
                    IntSet.add key acc
                  else
                    acc
                end 
            | Lhemp 
            | Lhlist _ 
            | Lhlseg _ -> acc
          ) lm.lm_mem IntSet.empty in
      (* Expression that needs to be satisfied to allow non local unfolding *)
      let set_cons =
        let set_expr =
          IntMap.fold (fun key (elt, _) acc -> S_uplus (S_var elt, acc))
            var_set S_empty in
        let set_expr =
          IntSet.fold
            (fun elt acc -> S_uplus (S_node elt, acc)) var_sy set_expr in
        S_mem (i, set_expr) in
      if Dv.set_sat set_cons x.t_num then
        (* Compute the disjunction of cases *)
        let ret =
          IntMap.fold
            (fun key (arg, heap_frag) acc ->
              let transform lc f f1 =
                let lm, lseg, lind, setcons, setv_torem, setv_add =
                  gen_ind_setpars lm lc in
                let lm = f lind (f1 key lm) in
                let lm = lseg_edge_add key i lseg lm in
                let num = IntSet.fold Dv.setv_add setv_add x.t_num in
                let num =
                  List.fold_left
                    (fun acc c -> Dv.set_guard c acc) num setcons in
                let num = Dv.set_guard (S_mem (i, (S_var arg))) num in
                let xx = (* remove all non root SETVs to remove *)
                  IntSet.fold setv_delete_non_root setv_torem
                    { x with t_mem = lm; t_num = num } in
                xx :: acc in
              match heap_frag with
              | Lhemp
              | Lhpt _ -> Log.fatal_exn "non_local unfold emp/Lhpt"
              | Lhlist lc ->
                  transform lc (list_edge_add i) list_edge_rem
              | Lhlseg (lc, nid) -> 
                  transform lc (lseg_edge_add i nid) lseg_edge_rem
            ) var_set [] in
        (ret, var_sy)
      else
        (* XR: is it sound to return [ ] here ? it seems not to me *)
        ([ ], IntSet.empty)


    (** Cell operations *)
    let cell_create ?(attr:node_attribute = Attr_none) 
        ((si, so): onode) (sz: Offs.size) (nt: ntyp) (x: t): t = 
      sanity_check "create,before" x;
      let dst, x = sv_add_fresh nt Nnone x in (* destination *)
      let pe = { pe_size = sz ; (* new points-to edge *)
                 pe_dest = dst, Offs.zero } in
      let bsrc = si, Bounds.of_offs so in
      let rx = { x with t_mem = pt_edge_block_append bsrc pe x.t_mem } in
      sanity_check "create,after" rx;
      rx
    let cell_delete ?(free:bool = true) ?(root:bool = false)
        (i: int) (x: t): t =
      let m = if root then List_utils.sv_unroot i x.t_mem else x.t_mem in
      let m = List_utils.pt_edge_block_destroy ~remrc:true i m in
      let m = if free then Log.todo_exn "free" else m in
      sve_fix "cell_delete" { x with t_mem = m }
    let cell_read (is_resolve: bool) (src: onode) (sz: int) (x: t)
        : (t * onode * onode option) list =
      sanity_check "cell_read,before" x;
      let cell_read_one (src: onode) (x: t): t * onode =
        let nt, pte = pt_edge_extract (sat_val x) src sz x.t_mem in
        if not (Offs.size_to_int_opt pte.pe_size = Some sz) then
          Log.fatal_exn "cell_read: not the right size (%d,%s)" sz
            (Offs.size_2str pte.pe_size);
        sve_fix "cell_read_one" { x with t_mem = nt }, pte.pe_dest in
      let rec cell_read_exc (count: int) (src: onode) (x: t)
          : (t * onode * onode option) list =
        try 
          let x, cont = cell_read_one src x in
          [ x, src, Some cont ]
        with
        | Graph_sig.No_edge mess ->
            Log.info "cell_read: No_edge exn caught, non local unfold";
            let i, off = src in
            begin
              try
                let ret, new_i = nonlocal_unfold i x in
                (* the node is eqaul to some unfolded node *)
                let sy_eq =
                  IntSet.fold
                    (fun elt acc ->
                      let num =
                        Dv.guard true
                          (Nc_cons (Apron.Tcons1.EQ, Ne_var i, Ne_var elt))
                          x.t_num in
                      let x = { x with t_num = num } in
                      let rl = cell_read_exc Flags.max_unfold (elt, off) x in
                      List.iter
                        (fun (rx,_,_) -> sanity_check "cell_read,after" rx) rl;
                      List.rev_append rl acc
                    ) new_i [ ] in
                let sy_unfold =
                  List.fold_left
                    (fun acc elt ->
                      let rl = cell_read_exc Flags.max_unfold src elt in
                      List.iter
                        (fun (rx,_,_) -> sanity_check "cell_read,after" rx) rl;
                      List.rev_append rl acc
                    ) sy_eq ret in 
                sy_unfold
              with
              | exn ->
                  Log.warn "Exn: %s" (Printexc.to_string exn);
                  [ x, src, None ]
            end
        | Graph_sig.Unfold_request (ul, dir) ->
            let i =
              match ul with
              | Uloc_main i -> i
              | Uloc_sub _ -> Log.fatal_exn "sub-memories not supported" in
            assert (dir = Udir_fwd);
            if count > 0 then
              let ncount = count - 1 in
              let l = unfold i x in
              List.flatten
                (List.map (fun u -> cell_read_exc ncount src u) l)
            else Log.fatal_exn "reached the maximal number of unfoldings" in
      let rl = cell_read_exc Flags.max_unfold src x in
      List.iter (fun (rx,_,_) -> sanity_check "cell_read,after" rx) rl;
      rl
    let cell_resolve (src: onode) (size: int) (x: t)
        : (t * onode * bool) list =
      let f (x, src, op_cont) = x, src, op_cont != None in
      List.map f (cell_read false src size x)
    let cell_write (ntyp: ntyp)
        (dst: onode) (size: int) (ne: n_expr) (x: t): t =
      sanity_check "cell_write,before" x;
      let write_in_main (x: t) (nval: onode): t =
        let pte = { pe_size = Offs.size_of_int size;
                    pe_dest = nval } in
        let nt = pt_edge_replace (sat_val x) dst pte x.t_mem in
        sve_fix "cell_write" { x with t_mem = nt } in
      let non_ptr_assign ( ) =
        let nn, x = sv_add_fresh ntyp Nnone (sve_fix "non_ptr_assign" x) in
        if false then
          Log.info "Non_ptr_assign: %d\n%s" nn (t_2stri "  " x);
        (* Issue: some node stayed there and is allocated again... *)
        write_in_main { x with t_num = Dv.assign nn ne x.t_num }
          (nn, Offs.zero) in
      let rx =
        match ntyp with
        | Ntaddr ->
            begin
              match decomp_lin_opt ne with
              | None -> non_ptr_assign ( )
              | Some (ir, offr) -> write_in_main x (ir, Offs.of_n_expr offr)
            end
        | _ -> non_ptr_assign ( ) in
      sanity_check "cell_write,after" rx;
      rx

    (** Transfer functions *)
    let guard (c: n_cons) (x: t): t =
      { x with t_num = Dv.guard true c x.t_num }
    let sat (c: n_cons) (x: t): bool = Dv.sat x.t_num c

    let tr_setcon (x: svo setprop): set_cons =
      let tr_int i =
        match i with
        | None -> 0
        | Some i -> i in
      match x with
      | Sp_sub (l, r) -> S_subset (S_var l.s_uid, S_var r.s_uid)
      | Sp_mem ((i, o), r) -> (* check the off be zero for now*)
          let o =tr_int (Offs.to_int_opt o) in
          if o = 0 then
            S_mem (i, S_var r.s_uid)
          else Log.fatal_exn "tr_setcon: offset is not eauqal to zero"
      | Sp_emp l -> S_eq (S_empty, S_var l.s_uid)
      | Sp_euplus (l, (i, o), r) ->
          let o = tr_int (Offs.to_int_opt o) in
          if o = 0 then
            S_eq (S_var l.s_uid, S_uplus (S_node i, S_var r.s_uid))
          else Log.fatal_exn "tr_setcon: offset is not eauqal to zero"

    (** Assuming and checking inductive edges *)
    let ind_extract_list (name: string): l_def =
      try StringMap.find name !list_ind_defs
      with Not_found -> Log.fatal_exn "definition: %s not found" name

    let assume (op: meml_log_form) (t: t): t =
      match op with
      | SL_set x ->
          let x = tr_setcon x in
          { t with t_num = Dv.set_guard x t.t_num }
      | SL_ind (ic, (i, off)) ->
          assert (Offs.is_zero off);
          let ld = ind_extract_list ic.ic_name in
          let pars =
            match ic.ic_pars with
            | None -> [ ]
            | Some ind_pars -> List.map (fun i -> i.s_uid) ind_pars.ic_set in
          let lc = { lc_def  = ld;
                     lc_args = pars;} in
          { t with
            t_mem = List_utils.list_edge_add i lc t.t_mem;
            t_num = t.t_num }
      | SL_seg _ ->
          Log.todo_exn "lseg_assume"
      | SL_array ->
          { t with t_num = Dv.assume Opd0.SL_array t.t_num }

    let ind_unfold (u: unfold_dir) ((n,o): onode) (x: t): t list =
      if u != Udir_fwd then Log.fatal_exn "unfold: only forward supported";
      if List_utils.sv_is_ind n x.t_mem then unfold n x
      else [ x ]

    let check (op: meml_log_form) (x: t): bool =
      match op with
      | SL_set sp ->
          let sp = tr_setcon sp in
          Dv.set_sat sp x.t_num
      | SL_seg _ -> Log.todo_exn "lseg_check"
      | SL_ind (ic, (i, off)) ->
          sanity_check "ind_check,before" x;
          assert (gen_ind_call_is_empty ic);
          assert (Offs.is_zero off);
          let tref =
            let ld = ind_extract_list ic.ic_name in
            let pars = 
              match ic.ic_pars with
              | None -> [ ]
              | Some ind_pars -> 
                  List.fold_left (fun acc i -> i.s_uid :: acc)
                    [ ] (List.rev ind_pars.ic_set) in
            let lm = sv_add i Ntraw lmem_empty in
            let lm =
              IntSet.fold (List_utils.setv_add true) x.t_mem.lm_setvroots lm in
            let lm =
              List.fold_left
                (fun lm i ->
                  if IntSet.mem i lm.lm_setvroots then lm
                  else List_utils.setv_add false i lm
                ) lm pars in
            let lc = { lc_def  = ld; lc_args = pars; } in
            list_edge_add i lc lm in
          let inj = Aa_maps.add i i Aa_maps.empty in
          let sinj, init_set = 
            IntSet.fold
              (fun i (inj_acc, set) -> 
                Aa_maps.add i i inj_acc,
                let r1 = Dv.setv_is_root i x.t_num in
                assert r1;
                Dv.setv_add ~root:true i set
              ) (Dv.setv_col_root x.t_num) (Aa_maps.empty, Dv.top) in
          let r =
            List_is_le.is_le_weaken_check x.t_mem IntSet.empty (make_sat x)
              (make_setsat x) tref inj sinj in
          begin
            match r with
            | `Ilr_not_le -> false
            | `Ilr_le_rem (_, _, inj, sinj, setcons) ->
                (* Set constraints are all checked in is_le *)
                Log.info "constraints: %d" (List.length setcons);
                if setcons != [ ] then
                  Log.info "ind_check:\n%s" (t_2stri "   " x);
                List.fold_left
                  (fun acc c ->
                    let fv i = IntMap.find i inj in
                    let fsetv i =
                      let s = IntMap.find i sinj in
                      if s = IntSet.empty then raise Not_found
                      else IntSet.min_elt s in
                    try
                      let cc = s_cons_map fv fsetv c in
                      let is_sat = Dv.set_sat cc x.t_num in
                      if not is_sat then Log.warn "constraint failed";
                      acc && is_sat
                    with Not_found ->
                      Log.warn "not found, discarding constraint!";
                      acc
                  ) true setcons
          end
      | SL_array ->
          Dv.check Opd0.SL_array x.t_num
  end: DOM_MEM_LOW)
