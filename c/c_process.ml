(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_process.ml
 **       processing stages for the "small-C" frontend
 ** Xavier Rival, 2013/07/07 *)
open C_sig
open C_utils
open Data_structures
open Flags
open Graph
open Lib


(** Error handling *)
module Log =
  Logger.Make(struct let section = "c_proc__" and level = Log_level.DEBUG end)

module SS = StringSet

(* find recursive functions in the call graph 'g' when starting at
 * 'entry_point'.
 * recursive functions in the call graph that are not reachable when entering
 * the program through the function 'entry_point' will not be reported *)
let find_rec_calls (entry_point: string) (g: StringGraph.t): StringSet.t =
  (* acc contains the already discovered recursive functions *)
  let rec loop (visited: SS.t) (acc: SS.t) (to_visit: string) =
    let successors = StringGraph.node_successors to_visit g in
    let rec_calls, not_rec_calls =
      SS.partition (fun n -> SS.mem n visited) successors
    in
    let new_acc = SS.union rec_calls acc in
    let new_visited = SS.add to_visit visited in
    let to_visit_next = SS.elements not_rec_calls in
    let other_rec_calls = List.map (loop new_visited acc) to_visit_next in
    List.fold_left SS.union new_acc other_rec_calls in
  loop SS.empty SS.empty entry_point

(* get the list of functions that can be reached when starting execution
   via 'entry_point' *)
let reachable_functions
    (entry_point: string) (g: StringGraph.t): StringSet.t =
  let rec loop (to_visit: SS.t) (acc: SS.t) (visited: SS.t) =
    if SS.is_empty to_visit then acc
    else
      let curr, others = SS.pop_min to_visit in
      let successors = StringGraph.node_successors curr g in
      let new_acc = SS.add curr acc in
      let new_visited = SS.add curr visited in
      let to_visit_next = SS.diff (SS.union others successors) new_visited in
      loop to_visit_next new_acc new_visited in
  loop (SS.singleton entry_point) SS.empty SS.empty

(** Check for absence of recursion *)
let c_prog_check_no_recursion (p: c_prog): unit =
  (* Computation of the call graph *)
  let call_graph =
    let rec aux_call (name: string) (c: c_call) (g: StringGraph.t) =
      match c.cc_fun.cek with
      | Celval lv ->
          begin
            match lv.clk with
            | Clvar v -> StringGraph.edge_add name v.cv_name g
            | _ -> Log.todo_exn "aux_call: check-no-rec, unbound call lval"
          end
      | _ -> Log.todo_exn "aux_call: check-no-rec, unbound call expr"
    and aux_stat (name: string) (s: c_statk) (g: StringGraph.t) =
      match s with
      | Cspcall c | Csfcall (_, c) -> aux_call name c g
      | Csblock b | Cswhile (_, b, _) -> aux_block name b g
      | Csif (_, b0, b1) -> aux_block name b1 (aux_block name b0 g)
      | Csdecl _ | Csassign _ | Csreturn _ | Csbreak | Cscontinue | Csexit
      | Cs_memcad _ | Csassert _ | Csalloc _ | Csfree _ -> g
    and aux_block (name: string) (b: c_block) (g: StringGraph.t) =
      match b with
      | [ ] -> g
      | s0 :: b1 -> aux_block name b1 (aux_stat name s0.csk g) in
    StringMap.fold
      (fun n f a ->
        aux_block n f.cf_body (StringGraph.node_add n a)
      ) p.cp_funs StringGraph.empty in
  (* we look only for rec. calls starting at the same entry point
   * than the analysis *)
  if !Flags.show_reachable_functions then
    let reachable = reachable_functions !Flags.mainfun call_graph in
    Log.info "";
    SS.iter
      (fun fun_name ->
        Log.info "can_reach: %s" fun_name
      ) reachable;
  let rec_funs = find_rec_calls !Flags.mainfun call_graph in
  if StringSet.is_empty rec_funs then ()
  else
    let log =
      if !rec_calls then Log.warn
      else Log.fatal_exn in
    log "found recursive functions: %s" (StringSet.t_2str " " rec_funs)

(** Fixing types *)

let c_prog_fix_types (p: c_prog): c_prog =
  let r_agg: c_aggregate StringMap.t ref = ref p.cp_aggs in
  let add_aggregate ag =
    match ag.cag_name with
    | None -> ( )
    | Some n -> r_agg := StringMap.add n ag !r_agg in
  (* 1. propagates the types through definitions
   *    seen stores already seen type names and aggregate names *)
  let rec c_type_propag (seen: StringSet.t * StringSet.t) (t: c_type): c_type =
    match t with
    | Ctchar | Ctint | Ctvoid | Ctptr None | Ctstring _ -> t
    | Ctnamed nt ->
        let s = nt.cnt_name in
        if StringSet.mem s (fst seen) then t
        else
          let tr =
            try StringMap.find s p.cp_types
            with Not_found ->
              Log.fatal_exn "c_type_propag: type %s not found" s in
          c_type_propag (StringSet.add s (fst seen), snd seen) tr
    | Ctstruct ad -> Ctstruct (c_aggregate_def_propag seen ad)
    | Ctunion  ad -> Ctunion  (c_aggregate_def_propag seen ad)
    | Ctptr (Some t0) -> Ctptr (Some (c_type_propag seen t0))
    | Ctarray (t0, i) -> Ctarray (c_type_propag seen t0, i)
  and c_aggregate_def_propag seen = function
    | Cad_def a ->
        let ag = c_aggregate_propag seen a in
        add_aggregate ag;
        Cad_def ag
    | (Cad_named s) as ad ->
        if StringSet.mem s (snd seen) then ad
        else
          try
            let ag = StringMap.find s p.cp_aggs in
            let ag = c_aggregate_propag seen ag in
            add_aggregate ag;
            Cad_def ag
          with Not_found -> ad
  and c_aggregate_propag (seen: StringSet.t * StringSet.t)
      (a: c_aggregate): c_aggregate =
    let seen =
      match a.cag_name with
      | None -> seen
      | Some s -> fst seen, StringSet.add s (snd seen) in
    { a with cag_fields = List.map (c_agg_field_propag seen) a.cag_fields }
  and c_agg_field_propag seen (f: c_agg_field): c_agg_field =
    { f with caf_typ = c_type_propag seen f.caf_typ } in
  let prop_defs =
    StringMap.mapi
      (fun s -> c_type_propag (StringSet.singleton s, StringSet.empty))
      p.cp_types
  and prop_aggs =
    StringMap.mapi
      (fun s -> c_aggregate_propag (StringSet.empty, StringSet.singleton s))
      !r_agg in
  (* 2. propagate everywhere *)
  let rec do_c_type (t: c_type): c_type =
    match t with
    | Ctchar | Ctint | Ctvoid | Ctptr None | Ctstring _ -> t
    | Ctnamed nt ->
        begin
          let s = nt.cnt_name in
          try StringMap.find s prop_defs
          with Not_found -> Log.fatal_exn "do_c_type: type not found: %s" s
        end
    | Ctstruct ad -> Ctstruct (do_c_aggregate_def ad)
    | Ctunion  ad -> Ctunion  (do_c_aggregate_def ad)
    | Ctptr (Some t0) -> Ctptr (Some (do_c_type t0))
    | Ctarray (t0, i) -> Ctarray (do_c_type t0, i)
  and do_c_aggregate_def (ad: c_aggregate_def): c_aggregate_def =
    match ad with
    | Cad_def a -> Cad_def (do_c_aggregate a)
    | Cad_named s ->
        try Cad_def (StringMap.find s prop_aggs)
        with Not_found ->
          Log.fatal_exn "do_c_aggregate_def: b:aggr not found: %s" s
  and do_c_aggregate (a: c_aggregate): c_aggregate =
    { a with cag_fields = List.map do_c_agg_field a.cag_fields }
  and do_c_agg_field (f: c_agg_field): c_agg_field =
    { f with caf_typ = do_c_type f.caf_typ } in
  let do_c_var (v: c_var): c_var = { v with cv_type = do_c_type v.cv_type } in
  let rec do_c_exprk (e: c_exprk): c_exprk =
    match e with
    | Ceconst _ -> e
    | Celval l -> Celval (do_c_lval l)
    | Ceaddrof l -> Ceaddrof (do_c_lval l)
    | Ceuni (u, e0) -> Ceuni (u, do_c_expr e0)
    | Cebin (b, e0, e1) -> Cebin (b, do_c_expr e0, do_c_expr e1)
  and do_c_expr (e: c_expr): c_expr =
    { cek = do_c_exprk e.cek;
      cet = do_c_type e.cet }
  and do_c_lvalk (l: c_lvalk): c_lvalk =
    match l with
    | Clvar v -> Clvar (do_c_var v)
    | Clfield (l0, f) -> Clfield (do_c_lval l0, f)
    | Clindex (l0, e1) -> Clindex (do_c_lval l0, do_c_expr e1)
    | Clderef e0 -> Clderef (do_c_expr e0)
  and do_c_lval (e: c_lval): c_lval =
    { clk = do_c_lvalk e.clk;
      clt = do_c_type e.clt } in
  let do_c_call (c: c_call): c_call =
    { cc_fun  = do_c_expr c.cc_fun ;
      cc_args = List.map do_c_expr c.cc_args } in
  let rec do_c_stat (s: c_stat): c_stat =
    let sk =
      match s.csk with
      | Csdecl v -> Csdecl (do_c_var v)
      | Cspcall c -> Cspcall (do_c_call c)
      | Csfcall (l, c) -> Csfcall (do_c_lval l, do_c_call c)
      | Csassign (l, e) -> Csassign (do_c_lval l, do_c_expr e)
      | Csblock b -> Csblock (do_c_block b)
      | Csif (e0, b1, b2) -> Csif (do_c_expr e0, do_c_block b1, do_c_block b2)
      | Cswhile (e0, b1, i) -> Cswhile (do_c_expr e0, do_c_block b1, i)
      | Csreturn None | Csbreak | Cscontinue | Csexit | Cs_memcad _ -> s.csk
      | Csreturn (Some e) -> Csreturn (Some (do_c_expr e))
      | Csassert e -> Csassert (do_c_expr e)
      | Csalloc (l, e) -> Csalloc (do_c_lval l, do_c_expr e)
      | Csfree l -> Csfree (do_c_lval l) in
    { s with csk = sk }
  and do_c_block b = List.map do_c_stat b in
  let do_c_fun (f: c_fun): c_fun =
    { f with
      cf_type = do_c_type f.cf_type;
      cf_args = List.map do_c_var f.cf_args;
      cf_body = do_c_block f.cf_body } in
  { cp_vars  = StringMap.map do_c_var p.cp_vars;
    cp_funs  = StringMap.map do_c_fun p.cp_funs;
    cp_types = prop_defs;
    cp_aggs  = p.cp_aggs (* for now *) }

(** Binding variables to unique IDs *)
(* - Maps each variable to a unique ID, in a consistent manner
 * - Ensures consistency of named types (fills type placeholder) *)
type binding_env = (int * (c_type option)) StringMap.t
let max_c_var_id: int ref = ref 0 (* next value is !max_c_var_id + 1 *)
let bind_c_prog (cp: c_prog): c_prog =
  let debug = !Flags.test_verbose in
  (* Managing unique IDs and generating new ones *)
  let generate_id ( ): int =
    let n = ! max_c_var_id + 1 in
    max_c_var_id := n ;
    n in
  let pp_env (m: binding_env): unit =
    Log.info "Env:";
    StringMap.iter (fun s (i, _) -> Log.info "  %s => %d" s i) m in
  (* Variable and function declaration site *)
  let decl_var (m: binding_env) (v: c_var): c_var * binding_env =
    let uid = generate_id ( ) in
    { v with cv_uid = uid }, StringMap.add v.cv_name (uid, Some v.cv_type) m in
  let decl_setvar (m: binding_env) (s: c_memcad_setvar)
      : c_memcad_setvar * binding_env =
    let uid = generate_id ( ) in
    { s with mc_setvar_uid = uid },
    StringMap.add s.mc_setvar_name (uid, None) m in
  let decl_setvars (m: binding_env) (ss: c_memcad_setvar list)
    : c_memcad_setvar list * binding_env =
    List.fold_left
      (fun (acc, m) s ->
         let s, m = decl_setvar m s in
         s :: acc, m
      ) ([], m) (List.rev ss) in
  let decl_fun (m: binding_env) (f: c_fun): c_fun * binding_env =
    let uid = generate_id ( ) in
    { f with cf_uid = uid }, StringMap.add f.cf_name (uid, Some Ctvoid) m in
  (* Variable use site *)
  let bind_var (m: binding_env) (v: c_var): c_var =
    if debug then pp_env m;
    let i, t =
      try StringMap.find v.cv_name m
      with Not_found ->
        Log.fatal_exn "bind_var: variable not found: %s" (c_var_2str v) in
    if debug then Log.info "Var <%s>: %d" v.cv_name i;
    match t with
    | None -> Log.fatal_exn "bind_var: wrong type for program variable"
    | Some t1 ->
        if debug then
          Log.info "bind_var: %s: %s" v.cv_name (c_type_2str t1);
        { v with
          cv_uid  = i ;
          cv_type = t1 } in
  let bind_vars (m: binding_env) (l: c_var list): c_var list =
    List.map (bind_var m) l in
  (* Initialization of globals *)
  let n_gvars, map_glo =
    StringMap.fold
      (fun s v (acc_v, acc_m) ->
        let nv, nm = decl_var acc_m v in
        StringMap.add s nv acc_v, nm
      ) cp.cp_vars (StringMap.empty, StringMap.empty) in
  (* Functions to treat the program *)
  let do_expr_lval (m: binding_env) =
    let rec aux_exprk (e: c_exprk): c_exprk =
      match e with
      | Ceconst _ -> e
      | Celval l -> Celval (aux_lval l)
      | Ceaddrof l -> Ceaddrof (aux_lval l)
      | Ceuni (u, e0) -> Ceuni (u, aux_expr e0)
      | Cebin (b, e0, e1) -> Cebin (b, aux_expr e0, aux_expr e1)
    and aux_expr (e: c_expr): c_expr =
      { e with cek = aux_exprk e.cek }
    and aux_lvalk (l: c_lvalk): c_lvalk =
      match l with
      | Clvar v -> Clvar (bind_var m v)
      | Clfield (l0, f) -> Clfield (aux_lval l0, f)
      | Clderef e0 -> Clderef (aux_expr e0)
      | Clindex (l0, e0) -> Clindex (aux_lval l0, aux_expr e0)
    and aux_lval (l: c_lval): c_lval =
      { l with clk = aux_lvalk l.clk } in
    aux_expr, aux_lval in
  let do_expr (m: binding_env) = fst (do_expr_lval m) in
  let do_lval (m: binding_env) = snd (do_expr_lval m) in
  let do_memcad_iparam (m: binding_env) = function
    | Cmp_const _ as p -> p
    | Cmp_lval lv -> Cmp_lval (do_lval m lv) in
  let do_memcad_sparam (m: binding_env) (v: c_memcad_setvar): c_memcad_setvar =
    if debug then pp_env m;
    let i, t =
      try StringMap.find v.mc_setvar_name m
      with Not_found ->
        Log.fatal_exn "do_memcad_sparam: set variable not found: %s"
          v.mc_setvar_name in
    if debug then Log.info "Var <%s>: %d" v.mc_setvar_name i;
    match t with
    | Some _ ->  Log.fatal_exn "do_memcad_sparam: wrong type for set variable"
    | None -> { v with mc_setvar_uid  = i } in
  let do_memcad_iparams (m: binding_env) (p: c_memcad_iparams) =
    { mc_pptr = List.map (do_memcad_iparam m) p.mc_pptr ;
      mc_pint = List.map (do_memcad_iparam m) p.mc_pint ;
      mc_pset = List.map (do_memcad_sparam m) p.mc_pset } in
  let do_memcad_setexpr (m: binding_env) (p: c_memcad_setexpr) =
    match p with
    | Cmp_subset (l, r) ->
        Cmp_subset (do_memcad_sparam m l, do_memcad_sparam m r)
    | Cmp_mem (v, r) -> Cmp_mem (do_lval m v, do_memcad_sparam m r)
    | Cmp_empty l ->
        Cmp_empty (do_memcad_sparam m l)
    | Cmp_euplus (l, v, r) ->
        Cmp_euplus (do_memcad_sparam m l, do_lval m v, do_memcad_sparam m r) in
  let do_memcad_setexprs (m: binding_env) (set_exprs: c_memcad_setexpr list) =
    (List.map (do_memcad_setexpr m) set_exprs) in
  let do_memcad_numexpr (m: binding_env) ((op, lv, p): c_num_expr) =
    (op, do_lval m lv, do_memcad_iparam m p) in
  let do_memcad_numexprs (m: binding_env) (num_exprs: c_num_expr list) =
    List.map (do_memcad_numexpr m) num_exprs in
  let do_memcad_com (m: binding_env) (mc: c_memcad_com)
      : c_memcad_com * binding_env =
    let do_pars m p =
      match p with
      | None -> None
      | Some p -> Some (do_memcad_iparams m p) in
    match mc with
    | Mc_add_inductive (lv, oi, None) ->
        Mc_add_inductive (do_lval m lv, oi, None), m
    | Mc_add_inductive (lv, oi, Some p) ->
        Mc_add_inductive (do_lval m lv, oi, Some (do_memcad_iparams m p)), m
    | Mc_assume num_exprs ->
        Mc_assume (do_memcad_numexprs m num_exprs), m
    | Mc_add_segment (lv, oi, p, lv_e, oi_e, p_e) ->
        Mc_add_segment (do_lval m lv, oi, do_pars m p,
                        do_lval m lv_e, oi_e, do_pars m p_e), m
    | Mc_check_segment (lv, oi, p, lv_e, oi_e, p_e) ->
        Mc_check_segment (do_lval m lv, oi, do_pars m p,
                          do_lval m lv_e, oi_e, do_pars m p_e), m
    | Mc_check_inductive (lv, oi, None) ->
        Mc_check_inductive (do_lval m lv, oi, None), m
    | Mc_check_inductive (lv, oi, Some p) ->
        Mc_check_inductive (do_lval m lv, oi, Some (do_memcad_iparams m p)), m
    | Mc_unfold lv ->
        Mc_unfold (do_lval m lv), m
    | Mc_unfold_bseg lv ->
        Mc_unfold_bseg (do_lval m lv), m
    | Mc_sel_merge l ->
        Mc_sel_merge (bind_vars m l), m
    | Mc_force_live l ->
        Mc_force_live (bind_vars m l), m
    | Mc_reduce_localize l ->
        Mc_reduce_localize (do_lval m l), m
    | Mc_check_bottomness _
    | Mc_unroll _
    | Mc_merge
    | Mc_output_stdout | Mc_output_ext (Out_dot _)
    | Mc_kill_flow
    | Mc_array_check
    | Mc_array_assume
    | Mc_reduce_eager
    | Mc_comstring _ -> mc, m
    | Mc_add_setexprs l ->
        Mc_add_setexprs (do_memcad_setexprs m l), m
    | Mc_check_setexprs l ->
        Mc_check_setexprs (do_memcad_setexprs m l), m
    | Mc_decl_setvars ss ->
        let ss, m = decl_setvars m ss in
        Mc_decl_setvars ss, m in
  let do_call (m: binding_env) (c: c_call): c_call =
    { cc_fun  = do_expr m c.cc_fun ;
      cc_args = List.map (do_expr m) c.cc_args } in
  let out_block: c_block * 'a -> c_block = function
    | [ { csk = Csblock b; csl = _ } ], _ -> b
    | b, _ -> b in
  let rec do_statk (m: binding_env) (s: c_statk): c_statk * binding_env =
    match s with
    | Csdecl v ->
        let nv, nm = decl_var m v in
        Csdecl nv, nm
    | Csassign (lv, ex) ->
        Csassign (do_lval m lv, do_expr m ex), m
    | Cspcall c ->
        Cspcall (do_call m c), m
    | Csfcall (lv, c) ->
        Csfcall (do_lval m lv, do_call m c), m
    | Csblock b0 ->
        let nb0, _ = do_block m b0 in
        Csblock nb0, m
    | Csif (e0, b1, b2) ->
        let ne0 = do_expr m e0 in
        let nb1 = out_block (do_block m b1) in
        let nb2 = out_block (do_block m b2) in
        Csif (ne0, nb1, nb2), m
    | Cswhile (e0, b1, u) ->
        let ne0 = do_expr m e0 in
        let nb1 = out_block (do_block m b1) in
        Cswhile (ne0, nb1, u), m
    | Csreturn None ->
        Csreturn None, m
    | Csreturn (Some e) ->
        Csreturn (Some (do_expr m e)), m
    | Csbreak -> Csbreak, m
    | Cscontinue -> Cscontinue, m
    | Csexit -> Csexit, m
    | Cs_memcad c ->
        let c, m = do_memcad_com m (parse_memcad_comstring c) in
        Cs_memcad c, m
    | Csassert e0 ->
        Csassert (do_expr m e0), m
    | Csalloc (l0, e1) ->
        Csalloc (do_lval m l0, do_expr m e1), m
    | Csfree l0 ->
        Csfree (do_lval m l0), m
  and do_stat (m: binding_env) (s: c_stat): c_stat * binding_env =
    let nsk, nm = do_statk m s.csk in
    { s with csk = nsk }, nm
  and do_block (m: binding_env): c_block -> c_block * binding_env = function
    | [ ] -> [ ], m
    | s0 :: b1 ->
        let ns0, m0 = do_stat m s0 in
        let nb1, m1 = do_block m0 b1 in
        ns0 :: nb1, m1 in
  (* Binding of function names *)
  let cp, map_glo =
    let bfuns, map_glo =
      StringMap.fold
        (fun name f (funs, m) ->
          let f0, m0 = decl_fun m f in
          StringMap.add name f0 funs, m0
        ) cp.cp_funs (StringMap.empty, map_glo) in
    { cp with cp_funs = bfuns }, map_glo in
  (* Treating all functions *)
  let n_funs =
    StringMap.fold
      (fun n f acc_f ->
        let npars, map_entry =
          List.fold_left
            (fun (acc_p, acc_m) v ->
              let nv, nm = decl_var acc_m v in
              nv :: acc_p, nm
            ) ([ ], map_glo) f.cf_args in
        let nf = { f with
                   cf_args = List.rev npars ;
                   cf_body = fst (do_block map_entry f.cf_body) } in
        StringMap.add n nf acc_f
      ) cp.cp_funs StringMap.empty in
  (* Result *)
  { cp_vars  = n_gvars ;
    cp_funs  = n_funs ;
    cp_types = cp.cp_types ;
    cp_aggs  = cp.cp_aggs }


(** Typing *)
(* This typing routine is far from perfect:
 * - not all types are implemented
 * - rules for promotion are not implemented yet *)
type typing_env =
    { te_vars:  c_var StringMap.t (* local and global vars *) ;
      te_funs:  (c_type * c_type list) StringMap.t (* functions *) ;
      te_types: c_type StringMap.t (* type with names *) }
let type_c_prog (cp: c_prog): c_prog =
  (* Managing type environments *)
  let te_empty: typing_env = { te_vars  = StringMap.empty ;
                               te_funs  = StringMap.empty ;
                               te_types = StringMap.empty } in
  let te_add_var (v: c_var) (t: typing_env): typing_env =
    if v.cv_volatile then Log.warn "Losing volatile info";
    { t with
      te_vars = StringMap.add v.cv_name v t.te_vars } in
  let te_add_fun (f: c_fun) (t: typing_env): typing_env =
    let targs = f.cf_type, List.map (fun a -> a.cv_type) f.cf_args in
    { t with
      te_funs = StringMap.add f.cf_name targs t.te_funs } in
  let te_add_type (n: string) (tp: c_type) (t: typing_env): typing_env =
    { t with
      te_types = StringMap.add n tp t.te_types } in
  (* Initialization of the typing environment *)
  let t_init =
    StringMap.fold (fun _ -> te_add_fun) cp.cp_funs
      (StringMap.fold te_add_type cp.cp_types
         (StringMap.fold (fun _ -> te_add_var) cp.cp_vars te_empty)) in
  (* Typing components of the program *)
  let do_expr_lval (t: typing_env) =
    let rec aux_exprk (e: c_exprk): c_expr =
      match e with
      | Ceconst (Ccint i) ->
          { cek = e;
            cet = Ctint }
      | Ceconst (Ccnull) ->
          { cek = e;
            cet = Ctptr None }
      | Ceconst (Ccstring s) ->
          { cek = e;
            cet = Ctstring (String.length s) }
      | Ceconst (Ccchar _) ->
          { cek = e;
            cet = Ctchar }
      | Celval l ->
          let nl = aux_lval l in
          { cek = Celval nl;
            cet = nl.clt }
      | Ceaddrof l0 ->
          let nl0 = aux_lval l0 in
          { cek = Ceaddrof nl0 ;
            cet = Ctptr (Some nl0.clt) }
      | Ceuni (u, e0) ->
          let ne0 = aux_expr e0 in
          let nt = c_type_unary u ne0.cet in
          { cek = Ceuni (u, ne0) ;
            cet = nt }
      | Cebin (b, e0, e1) ->
          let ne0 = aux_expr e0 and ne1 = aux_expr e1 in
          let nt = c_type_binary b ne0.cet ne1.cet in
          { cek = Cebin (b, ne0, ne1) ;
            cet = nt }
    and aux_expr (e: c_expr): c_expr = aux_exprk e.cek
    and aux_lvalk (l: c_lvalk): c_lval =
      match l with
      | Clvar v ->
          { clk = Clvar v   ;
            clt = v.cv_type }
      | Clfield (l0, f) ->
          let nl0 = aux_lval l0 in
          let t = c_type_read_struct_field nl0.clt f in
          { clk = Clfield (nl0, f) ;
            clt = t }
      | Clderef e0 ->
          let ne0 = aux_expr e0 in
          let t =
            try c_type_read_ptr ne0.cet
            with e ->
              Log.info "failure on expression %s" (c_expr_2str e0);
              raise e in
          { clk = Clderef ne0 ;
            clt = t }
      | Clindex (l0, e0) ->
          let nl0 = aux_lval l0 in
          let ne0 = aux_expr e0 in
          { clk = Clindex (nl0,ne0);
            clt = c_type_read_array nl0.clt ne0.cet; }
    and aux_lval (l: c_lval): c_lval = aux_lvalk l.clk in
    aux_expr, aux_lval in
  let do_expr (t: typing_env) = fst (do_expr_lval t) in
  let do_lval (t: typing_env) = snd (do_expr_lval t) in
  let do_memcad_iparam (t: typing_env) = function
    | Cmp_const _ as p -> p
    | Cmp_lval lv -> Cmp_lval (do_lval t lv) in
  let do_memcad_iparams (t: typing_env) (p: c_memcad_iparams) =
    { mc_pptr = List.map (do_memcad_iparam t) p.mc_pptr ;
      mc_pint = List.map (do_memcad_iparam t) p.mc_pint ;
      mc_pset = p.mc_pset } in
  let do_memcad_setexpr (t: typing_env) (p: c_memcad_setexpr) =
    match p with
    | Cmp_subset (l, r) -> Cmp_subset (l, r)
    | Cmp_mem (v, r) -> Cmp_mem (do_lval t v, r)
    | Cmp_empty l -> Cmp_empty l
    | Cmp_euplus (l, v, r) ->
        Cmp_euplus (l, do_lval t v, r) in
  let do_memcad_setexprs (t: typing_env) (se: c_memcad_setexpr list) =
    List.map (do_memcad_setexpr t) se in
  let do_memcad_numexpr (t: typing_env) ((op, lv, p): c_num_expr) =
    (op, do_lval t lv, do_memcad_iparam t p) in
  let do_memcad_numexprs (t: typing_env) (ne: c_num_expr list) =
    List.map (do_memcad_numexpr t) ne in
  let do_memcad_com (t: typing_env) (mc: c_memcad_com): c_memcad_com =
    let do_pars m p =
      match p with
      | None -> None
      | Some p -> Some (do_memcad_iparams m p) in
    match mc with
    | Mc_add_inductive (lv, oi, None) ->
        Mc_add_inductive (do_lval t lv, oi, None)
    | Mc_add_inductive (lv, oi, Some p) ->
        Mc_add_inductive (do_lval t lv, oi, Some (do_memcad_iparams t p))
    | Mc_assume num_exprs ->
        Mc_assume (do_memcad_numexprs t num_exprs)
    | Mc_add_segment (lv, oi, p, lv_e, oi_e, p_e) ->
        Mc_add_segment (do_lval t lv, oi, do_pars t p, 
                        do_lval t lv_e, oi_e, do_pars t p_e)
    | Mc_check_segment (lv, oi, p, lv_e, oi_e, p_e) ->
        Mc_check_segment (do_lval t lv, oi, do_pars t p, 
                          do_lval t lv_e, oi_e, do_pars t p_e)
    | Mc_check_inductive (lv, oi, None) ->
        Mc_check_inductive (do_lval t lv, oi, None)
    | Mc_check_inductive (lv, oi, Some p) ->
        Mc_check_inductive (do_lval t lv, oi, Some (do_memcad_iparams t p))
    | Mc_unfold lv ->
        Mc_unfold (do_lval t lv)
    | Mc_unfold_bseg lv ->
        Mc_unfold_bseg (do_lval t lv)
    | Mc_reduce_localize lv ->
        Mc_reduce_localize (do_lval t lv)
    | Mc_check_bottomness _
    | Mc_unroll _
    | Mc_merge
    | Mc_output_stdout | Mc_output_ext (Out_dot _)
    | Mc_sel_merge _
    | Mc_force_live _
    | Mc_reduce_eager
    | Mc_array_check
    | Mc_array_assume
    | Mc_kill_flow -> mc
    | Mc_comstring s ->
        Log.fatal_exn "do_memcad_com: typing: yet unparsed memcad string: %s" s
    | Mc_add_setexprs ls ->
        Mc_add_setexprs (do_memcad_setexprs t ls)
    | Mc_check_setexprs ls ->
        Mc_check_setexprs (do_memcad_setexprs t ls)
    | Mc_decl_setvars l ->
        Mc_decl_setvars l in
  let do_call (t: typing_env) (c: c_call): c_call =
    (* Nb: function expressions do not get typed, which is not problematic
     *     at this stage as the AI of function expressions is limited *)
    { cc_fun  = (* do_expr t *) c.cc_fun ;
      cc_args = List.map (do_expr t) c.cc_args } in
  let rec do_statk (t: typing_env) (s: c_statk): c_statk * typing_env =
    match s with
    | Csdecl v -> s, te_add_var v t
    | Csassign (lv, ex) ->
        let is_pointer = function
          | Ctptr _ -> true
          | _ -> false in
        let nlv = do_lval t lv
        and nex = do_expr t ex in
        if is_pointer nlv.clt && nex.cek = Ceconst (Ccint 0) then
          (* pointer type expressions equal to zero transformed into null *)
          let null = { cek = Ceconst Ccnull; cet = nlv.clt } in
          Csassign (nlv, do_expr t null), t
        else if c_type_compat nlv.clt nex.cet then
          Csassign (nlv, nex), t
        else
          Log.fatal_exn "do_statk: incompatible types on assign: %s, %s"
            (c_type_2str nlv.clt) (c_type_2str nex.cet)
    | Cspcall c ->
        Cspcall (do_call t c), t
    | Csfcall (lv, cc) ->
        let nlv = do_lval t lv
        and ncc = do_call t cc in
        let name = c_call_name cc in
        let f = get_function cp name in
        if c_type_compat nlv.clt f.cf_type then
          Csfcall (nlv, ncc), t
        else
          Log.todo_exn
            "do_statk: function call (check assign types are ok): %s" name
    | Csblock b0 ->
        let nb0, _ = do_block t b0 in
        Csblock nb0, t
    | Csif (e0, b1, b2) ->
        let ne0 = do_expr t e0 in
        let nb1, _ = do_block t b1 in
        let nb2, _ = do_block t b2 in
        Csif (ne0, nb1, nb2), t
    | Cswhile (e0, b1, u) ->
        let ne0 = do_expr t e0 in
        let nb1, _ = do_block t b1 in
        Cswhile (ne0, nb1, u), t
    | Csreturn None ->
        Csreturn None, t
    | Csreturn (Some e) ->
        Csreturn (Some (do_expr t e)), t
    | Csbreak -> Csbreak, t
    | Cscontinue -> Cscontinue, t
    | Csexit -> Csexit, t
    | Cs_memcad c ->
        Cs_memcad (do_memcad_com t c), t
    | Csassert e0 ->
        Csassert (do_expr t e0), t
    | Csalloc (l0, e1) ->
        Csalloc (do_lval t l0, do_expr t e1), t
    | Csfree l0 ->
        Csfree (do_lval t l0), t
  and do_stat (t: typing_env) (s: c_stat): c_stat * typing_env =
    let nsk, nt = do_statk t s.csk in
    { s with csk = nsk }, nt
  and do_block (t: typing_env): c_block -> c_block * typing_env = function
    | [ ] -> [ ], t
    | s0 :: b1 ->
        let ns0, t0 = do_stat t s0 in
        let nb1, t1 = do_block t0 b1 in
        ns0 :: nb1, t1 in
  let do_fun (f: c_fun): c_fun =
    let t = List.fold_left (fun acc p -> te_add_var p acc) t_init f.cf_args in
    { f with cf_body = fst (do_block t f.cf_body) } in
  (* Returning the typed program *)
  { cp with cp_funs = StringMap.map do_fun cp.cp_funs }


(** Elaboration of types throughout the syntax tree *)
let c_prog_elaborate (p: c_prog): c_prog =
  c_prog_apply_type_op c_type_elaborate p


(** Syntax post-treatment *)
(* - moving unroll command into while annotation *)
let syntax_post_treat_c_prog (cp: c_prog): c_prog =
  let rec do_stat (s: c_stat): c_stat =
    match s.csk with
    | Csdecl _ | Cspcall _ | Csfcall _ | Csassign _ -> s
    | Csblock b0 ->
        { s with csk = Csblock (do_block b0) }
    | Csif (e, b0, b1) ->
        { s with csk = Csif (e, do_block b0, do_block b1) }
    | Cswhile (e, b0, u) ->
        { s with csk = Cswhile (e, do_block b0, u) }
    | Csreturn _ | Csbreak | Cscontinue | Csexit
    | Cs_memcad _ | Csassert _
    | Csalloc _ | Csfree _ -> s
  and do_block: c_block -> c_block = function
    | [ ] -> [ ]
    | [ s0 ] -> [ do_stat s0 ]
    | s0 :: s1 :: b ->
        match s0.csk, s1.csk with
        | Cs_memcad (Mc_unroll i), Cswhile (e, b0, u) ->
            if u = None then
              { s1 with csk = Cswhile (e, do_block b0, Some i) } :: do_block b
            else Log.fatal_exn "do_block: double unroll spec on loop"
        | _, _ -> do_stat s0 :: do_block (s1 :: b) in
  let do_fun (f: c_fun): c_fun =
    { f with cf_body = do_block f.cf_body } in
  { cp with cp_funs = StringMap.map do_fun cp.cp_funs }


(** Post-treatment *)
let process_c_prog (p: c_prog): c_prog =
  (* 1. check the absence of recursion *)
  if Flags.flag_debug_c_frontend then
    Log.force "Process 1/7: check the absence of recursion...";
  c_prog_check_no_recursion p;
  (* 2. fix types *)
  if Flags.flag_debug_c_frontend then
    Log.force "OK!\nProcess 2/7: fixing types (1)...";
  let p = c_prog_fix_types p in
  (* 3. binding of unique IDs *)
  if Flags.flag_debug_c_frontend then
    Log.force "OK!\nProcess 3/7: binding program variables...";
  let p = bind_c_prog p in
  (* 4. fix types again *)
  if Flags.flag_debug_c_frontend then
    Log.force "OK!\nProcess 4/7: fixing types (2)...";
  let p = c_prog_fix_types p in
  (* 5. typing the program *)
  if Flags.flag_debug_c_frontend then
    Log.force "OK!\nProcess 5/7: propagating types...";
  let p = type_c_prog p in
  (* 6. type elaboration *)
  if Flags.flag_debug_c_frontend then
    Log.force "OK!\nProcess 6/7: elaborate program...";
  let p = c_prog_elaborate p in
  (* 7. syntactic post-treatment (unroll commands) *)
  if Flags.flag_debug_c_frontend then
    Log.force "OK!\nProcess 7/7: post-treatment...";
  let p = syntax_post_treat_c_prog p in
  if Flags.flag_debug_c_frontend then
    Log.force "OK!";
  p
