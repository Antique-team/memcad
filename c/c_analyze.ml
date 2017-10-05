(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_analyze.ml
 **       analysis of C code (very restricted analysis)
 ** Xavier Rival, 2011/07/17 *)
open Lib
open Data_structures
open Ast_sig
open C_sig
open C_utils
open C_analysis_sig
open Disj_sig
open Dom_sig
open Flags

(* Current limitations:
 *  - static variables not handled
 *  - analysis of only a main function
 *  - does not pay attention to parameters
 *  - does not analyze function calls in expressions
 *    (we may leave this limitation forever, and use a kind of
 *     equivalent to the "Graph" in Astree)
 *  - consider merging both sides of the join hints
 *)

(** Error report *)
module Log =
  Logger.Make(struct let section = "c_ana___" and level = Log_level.DEBUG end)
let debug = true


(** The abstract interpreter functor:
 **  - M: DOM_C: contains the whole abstract domain
 **  - P: PRE_ANALYSIS: pre-analysis liveness parameters *)
module Make = functor (M: DOM_C) -> functor (P: PRE_ANALYSIS) ->
  struct
    (** status of the analysis *)
    type t = M.t (* current abstraction *)

    (** Gathering statistics *)
    let stats_accu: Statistics.prog_stats ref = ref IntMap.empty
    let add_stats (loc: int) (x: t): unit =
      let l = try IntMap.find loc !stats_accu with Not_found -> [] in
      stats_accu := IntMap.add loc (M.get_stats x :: l) !stats_accu
    (* Analysis step counter (for debug) *)
    let step = ref 0


    (** Analyzer context *)
    (* Note: we might move this to dom_c, but we keep it here for now, as
     *       it needs be accessed in the interpreter directly to deal with
     *       recursion *)
    type ctxt =
        { ct_funcalls:  StringSet.t ; (* functions currently on the stack *)
          ct_curfun:    string ;      (* current function name *)
          ct_currec:    bool ;        (* is the current call recursive ? *)
          ct_recdepth:  int  ;        (* iters when analyzing a rec. fun *)
          ct_curfix:    bool ;        (* did we reach a fixpoint ? *)
          ct_entry:     t StringMap.t (* abstract states (@ fun. entries) *) }
    let ctxt_empty: ctxt =
      { ct_funcalls = StringSet.empty ;
        ct_curfun   = "" ;
        ct_currec   = false ;
        ct_recdepth = 0 ;
        ct_curfix   = false ;
        ct_entry    = StringMap.empty }
    let ctxt_call (ct: ctxt) (f: string): ctxt =
      if StringSet.mem f ct.ct_funcalls then
        { ct with ct_currec = true }
      else
        { ct with
          ct_funcalls = StringSet.add f ct.ct_funcalls ;
          ct_curfun   = f }
    let ctxt_entry_get (ct: ctxt) (fname: string): t =
      try StringMap.find fname ct.ct_entry
      with Not_found -> Log.fatal_exn "rec-call, entry retrieval failed"
    let ctxt_entry_add (ct: ctxt) (fname: string) (x: t): ctxt =
      { ct with ct_entry = StringMap.add fname x ct.ct_entry }


    (** Over-approximation of a least-fixpoint *)
    (* Abstract iterations status *)
    type iter_status =
        { is_unroll: int; (* number of unroll iterations left *)
          is_dweak:  int; (* number of directed weakening iterations left *)
          is_join:   int; (* number of join iterations left *)
          is_total:  int; (* number of iterations performed so far *) }
    let iter_status_2str (is: iter_status): string =
      Printf.sprintf
        "<%d> (unroll: %d, dweak: %d, join: %d)"
        is.is_total is.is_unroll is.is_dweak is.is_join

    (* Retrieval of live variables at while statement head *)
    let get_live (lc: int): VarSet.t * (var tlval) list =
      let info =  P.live_at lc in
      VarMap.fold
        (fun var paths  (l, d) ->
          VarSet.add var l,
          PathSet.fold (fun p acc -> tr_c_lval (snd p) :: acc) paths d
        ) info (VarSet.empty, [])

    (* Computation of an abstract post-fixpoint *)
    let alfp (loc: loc)
        (h: hint_be)
        (l: var lint_be) (* hint at that loop head point *)
        (n_unrolls: int) (* whether or not to perform unroll iterations *)
        (f: t -> t) (x: t): t =
      (* end of the lfp computation: joins unrolls with current *)
      let join_unroll (acc: t option) (x: t): t =
        match acc with
        | None -> x
        | Some y -> M.join (Some h) (Some l) x y in
      (* end of a new unroll iteration, and join with accumulator *)
      let add_unroll (acc: t option) (x: t): t option =
        Some (join_unroll acc x) in
      let rec aux
          (is: iter_status)
          (acc: t option) (* accumulator for unroll iterations *)
          (xn: t): t =
        if !Flags.flag_debug_iter then
          Log.force "ALFP Iteration @%d %s; status:\n%s"
            loc (iter_status_2str is) (M.t_2stri "    " xn);
        let fxn = f xn in
        if !Flags.flag_debug_iter then
          Log.force "ALFP Output @%d %s\n%s"
            loc (iter_status_2str is) (M.t_2stri "  " fxn);
        (* Testing for stability does not seem to improve on timing *)
        if is.is_unroll > 0 then
          (* unroll iteration:
           *  - currently added to the list of unrolls;
           *  - keep iterating with current *)
          aux { is with
                is_unroll = is.is_unroll - 1;
                is_total  = is.is_total  + 1 } (add_unroll acc xn) fxn
        else if is.is_dweak > 0 then
          (* directed weakening iteration:
           *  - currently added to the list of unrolls
           *  - keep iterating with weakened current
           * NOTE: we may later keep the weakened current instead of current *)
          aux { is with
                is_dweak  = is.is_dweak - 1;
                is_total  = is.is_total + 1 } (add_unroll acc xn)
            (M.directed_weakening (Some h) xn fxn)
        else
          let opname, is =
            if is.is_join > 0 then
              Jjoin, { is with is_join = is.is_join - 1 }
            else Jwiden, is in
          (* get disjunctions kept from widening, and add them to acc *)
          let xnp, k_invar =
            match opname with
            | Jjoin  -> M.join  (Some h) (Some l) xn fxn, None
            | Jwiden -> M.widen (Some h) (Some l) xn fxn
            | Jdweak ->
                Log.fatal_exn "binary operator should be widen or join" in
          let acc =
            match k_invar with
            | None -> acc
            | Some kv -> add_unroll acc kv in
          if !Flags.flag_debug_iter then
            Log.force
              "ALFP Iter performed %s @%d:\nXn:\n%s\nF(Xn):\n%s\nX(n+1):\n%s"
              (Dom_utils.join_kind_2str opname) loc (M.t_2stri "  " xn)
              (M.t_2stri "  " fxn) (M.t_2stri "  " xnp);
          let le = M.is_le xnp xn in
          if !Flags.flag_debug_iter then
            Log.force "ALFP Iter status: %b" le;
          if le then
            begin
              Log.info
                "ALFP Iter status: stable after %d iters, \
                 end of iteration sequence" (is.is_total + 1);
              if not !Flags.very_silent_mode then
                Log.force " Fixpoint:\n%s" (M.t_2stri "   " xnp);
              join_unroll acc xnp
            end
          else
            begin
              Log.info "ALFP Iter status: not stable, keep iterating...";
              aux { is with is_total = is.is_total + 1 } acc xnp
            end in
      aux { is_unroll = n_unrolls;
            is_dweak  = !Flags.dweak_iters;
            is_join   = !Flags.join_iters;
            is_total  = 0 } None x


    (** Some utilities *)
    (* Preparation of an inductive definition, for underlying domain *)
    let prepare_inductive (ctxt: string) (l: c_lval) (oiname: string option)
        (op: c_memcad_iparams option): var tlval gen_ind_call =
      let p_u =
        Option.map
          (fun (p: c_memcad_iparams) ->
            let tr_ptr_param = function
              | Cmp_const i ->
                  Log.fatal_exn "numeric used as a pointer parameter"
              | Cmp_lval lv -> tr_c_lval lv in
            let tr_int_param = function
              | Cmp_const i -> Ii_const i
              | Cmp_lval lv -> Ii_lval (tr_c_lval lv) in
            { ic_ptr = List.map tr_ptr_param p.mc_pptr;
              ic_int = List.map tr_int_param p.mc_pint;
              ic_set = List.map tr_c_setvar p.mc_pset; }
          ) op in
      let iname =
        match oiname with
        | None ->
            let ctname =
              match l.clt with
              | Ctnamed nt -> nt.cnt_name
              | _ -> Log.fatal_exn "%s: not a named type" ctxt in
            Ind_utils.indname_find ctname
        | Some s -> s in
      { ic_name = iname ;
        ic_pars = p_u }
    (* get the name of the struct, if applicable *)
    let get_struct_name (t: c_type): string option =
      match t with
      | Ctstruct (Cad_def c_agg) -> c_agg.cag_name
      | _ -> None
    (* get the name of the c_aggregate, if applicable *)
    let get_c_aggregate_name (l: c_lval): string option =
      match l.clt with
      | ((Ctstruct _) as cts)
      | Ctptr (Some cts) -> get_struct_name cts
      | Ctnamed _
      | Ctint
      | Ctchar
      | Ctvoid
      | Ctunion _
      | Ctptr _
      | Ctarray _
      | Ctstring _ -> None
    let correct_inductive_name (l: c_lval) (oiname: string option)
        : string option =
      if not !Flags.auto_ind then oiname
      else
        match oiname with
        | None -> None
        | Some prev_name ->
            let maybe_new_name = get_c_aggregate_name l in
            match maybe_new_name with
            | None -> oiname
            | Some new_name ->
                Log.warn "correct_inductive_name: ind. %s renamed to %s"
                  prev_name new_name;
                maybe_new_name
    (* insertion of numerical preconditions *)
    let prepare_num_expr ((c, l, v): c_num_expr) =
      let c_memcad_iparam_to_c_expr: c_memcad_iparam -> c_expr = function
        | Cmp_const i -> { cek = Ceconst (Ccint i) ;
                           cet = Ctint             }
        | Cmp_lval clv -> { cek = Celval clv ;
                            cet = clv.clt    } in
      let e1 = c_memcad_iparam_to_c_expr (Cmp_lval l) in
      let e2 = c_memcad_iparam_to_c_expr v in
      tr_c_exprk (Cebin (c, e1, e2)), Tint (Flags.abi_int_size, Tsigned)


    (** Some transfer functions *)
    (* Type of logical assertions *)
    type log_op =
      | LAssume   (* for assume operations (inductives, segments...) *)
      | LVerify   (* for verification operations *)
    (* Pretty-printing *)
    let string_of_log_op = function
      | LAssume -> "assume"
      | LVerify -> "verify"
    (* Analysis of an assume of numerical expressions *)
    let a_assume_num_exprs (num_exprs: c_num_expr list) (x: t): t =
      let assume_num_expr x' num_expr =
        let tc = prepare_num_expr num_expr in
        let no_line_number = 0 in
        M.assert_one "c-analyze: assume" (M.guard no_line_number true tc x') in
      List.fold_left assume_num_expr x num_exprs
    (* Analysis of a verification of a set predicate *)
    let a_check_setexprs (line: int) (sp: c_memcad_setexpr list) (t: t): t =
      let b_res =
        List.for_all (fun x -> M.check t (SL_set (tr_c_setexpr x))) sp in
      Log.info "ASSERTION @%d (structural) %s" line
        (if b_res then "verified" else "failed");
      Lib.log_assert b_res;
      t
    (* Analysis of an add or check an inductive definition *)
    let a_inductive (dir: log_op) (line: int) (l: c_lval)
        (oiname: string option) (op: c_memcad_iparams option) (x: t): t =
      let tl = tr_c_lval l in
      let oiname0 = correct_inductive_name l oiname in
      let msg = string_of_log_op dir ^ "_inductive" in
      let ic = prepare_inductive msg l oiname0 op in
      match dir with
      | LAssume -> M.assume x (SL_ind (ic, tl))
      | LVerify ->
          let b_res = M.check x (SL_ind (ic, tl)) in
          Log.info "ASSERTION @%d (structural) %s" line
            (if b_res then "verified" else "failed");
          Lib.log_assert b_res;
          x
    (* Analysis of an add or check an inductive segment *)
    let a_segment (dir: log_op) (line: int) (l: c_lval) (oiname: string)
        (op: c_memcad_iparams option) (l_e: c_lval) (oiname_e: string)
        (op_e: c_memcad_iparams option)
        (x: t): t =
      let tl = tr_c_lval l in
      let tl_e = tr_c_lval l_e in
      let msg = string_of_log_op dir ^ "_segment" in
      let ic = prepare_inductive msg l (Some oiname) op in
      let ic_e = prepare_inductive msg l_e (Some oiname_e) op_e in
      match dir with
      | LAssume -> M.assume x (SL_seg (ic, tl, ic_e, tl_e))
      | LVerify ->
          let b_res = M.check x (SL_seg (ic, tl, ic_e, tl_e)) in
          Log.info "ASSERTION @%d (structural) %s" line
            (if b_res then "verified" else "failed");
          Lib.log_assert b_res;
          x

    (* Analysis of assignments *)
    let a_assign (loc: location) (lv: c_lval) (ex: c_expr) (x: t): t =
      let tl = tr_c_lval lv and te = tr_c_expr ex in
      let nx = M.assert_one "assign" (M.assign loc tl te x) in
      if debug && not !Flags.very_silent_mode then
        Log.force "Result post assign-expr:\n%s" (M.t_2stri "     " nx);
      nx

    (* Analysis of variable declarations *)
    let a_decl (ct: ctxt) (v: c_var) (x: t): t =
      if ct.ct_currec then Log.fatal_exn "rec-call: variable creation";
      M.unary_op x (UO_env (EO_add_var (tr_c_var v)))

    (* Analysis of blocks entries and exits *)
    let a_block_in (ct: ctxt) (x: t): t =
      if ct.ct_currec then x
      else M.unary_flow_op FO_block_in x
    let a_block_out (ct: ctxt) (x: t): t =
      if ct.ct_currec then x
      else M.unary_flow_op FO_block_out x


    (** Exporting local invariant *)
    let do_export (i: int) (x: t) (vars: string list) (opts: string list): t =
      let base = Printf.sprintf "%s-%d" !filebase i in
      M.ext_output (Out_dot (vars, opts)) base x


    (** Analysis functions *)
    let rec a_stat
        (ct: ctxt)    (* context *)
        (s: c_stat)   (* statement *)
        (x: t)        (* abstract pre-condition *)
        : t (* => abstract post-condition *) =
      (* Logs and outputs *)
      show_sep ();
      if !Flags.very_silent_mode then
        Log.info "ITER: at point %d(%d): %d disjuncts" s.csl !step
          (M.disj_size x)
      else
        begin
          let status =
            if c_stat_do_pp_status s then M.t_2stri "     " x else "[-]" in
          Log.info "ITER: Status at point %d(%d)\n%s\nStatement:\n%s"
            s.csl !step status (c_stat_2stri "     " s);
        end;
      incr step;
      if !enable_stats then add_stats s.csl x;
      let is_mc_output_ext_dot = function
        | Cs_memcad (Mc_output_ext (Out_dot (_, _))) -> true
        | _ -> false in
      let x =
        if !flag_enable_ext_export_all && not (is_mc_output_ext_dot s.csk) then
          do_export s.csl x [] []
        else x in
      (* Analysis of the statement *)
      match s.csk with
      | Csdecl v ->
          a_decl ct v x
      | Csassign (lv, ex) ->
          a_assign s.csl lv ex x
      | Cspcall pc ->
          if M.is_bot x then
            x
          else
            (* 1. dump the return variable *)
            let x0 = M.unary_op x (UO_ret None) in
            (* 2. call the procedure *)
            let x0 = a_proc_call s.csl false ct pc x0 in
            (* 3. restore the previous return variable *)
            let x0 = M.restore_return_var x x0 in
            if Flags.flag_debug_funcalls && not !very_silent_mode then
              Log.force "status before completing procedure call:\n%s"
                (M.t_2stri "  " x0);
            x0
      | Csfcall (lv, pc) ->
          if M.is_bot x then
            x
          else
            (* 1. create the return variable *)
            let tl = tr_c_lval lv in
            let x0 = M.unary_op x (UO_ret (Some (snd tl))) in
            (* 2. call the procedure *)
            let x0 = a_proc_call s.csl true ct pc x0 in
            if Flags.flag_debug_funcalls && not !very_silent_mode then
              Log.force "status at exit:\n%s" (M.t_2stri "  " x0);
            (* 3. perform the assignment from the return variable to lv *)
            let x0 = M.assert_one "call" (M.assign_from_return s.csl tl x0) in
            (* 4. restore the previous return variable *)
            let x0 = M.restore_return_var x x0 in
            if Flags.flag_debug_funcalls && not !very_silent_mode then
              Log.force "status before completing function call:\n%s"
                (M.t_2stri "  " x0);
            x0
      | Csblock b ->
          a_block ct b x
      | Csif (c, b0, b1) ->
          let tc = tr_c_expr c in
          let tnotc = tr_c_expr (c_expr_neg c) in
          let x_true  = M.assert_one "if-t" (M.guard s.csl true tc x) in
          let x_false = M.assert_one "if-f" (M.guard s.csl true tnotc x) in
          let x_true  = M.push_hist_atom (Ah_if (s.csl, true )) x_true  in
          let x_false = M.push_hist_atom (Ah_if (s.csl, false)) x_false in
          begin
            match M.is_bot x_true, M.is_bot x_false with
            |  true,  true -> x (* everything is _|_, nothing to analyze *)
            |  true, false -> a_block ct b1 x_false
            | false,  true -> a_block ct b0 x_true
            | false, false ->
                let y0 = a_block ct b0 x_true in
                let y1 = a_block ct b1 x_false in
                M.join None None y0 y1
          end
      | Cswhile (c, b0, u) ->
          let tc = tr_c_expr c in
          let tnotc = tr_c_expr (c_expr_neg c) in
          let live, dead = get_live s.csl in
          let hint = { hbe_live = live } in
          let lint = { lbe_dead = dead } in
          (* computation of the number of unrolls:
           *  - memcad unroll command overrides anything
           *  - otherwise check if the loop is outer, of it is inner, with
           *    unroll flag on; then use value specified in flags
           *  - otherwise, no unroll *)
          let n_unrolls =
            match u with
            | None -> (* no instruction on the loop; use default strategy *)
                if !Flags.unroll_inner || M.loop_count x = 0 then
                  !Flags.unrolls
                else 0
            | Some u -> u in
          let f_loop_body (xx: t): t =
            (* guard evaluation *)
            let xtrue = M.guard s.csl true tc xx in
            (* addition of the partitioning token *)
            let xtrue = List.map (M.push_hist_atom (Ah_while s.csl)) xtrue in
            (* remove enclosing list out of guard *)
            let xtrue = M.assert_one "loop,t" xtrue in
            let xin = M.unary_flow_op FO_loop_body_in xtrue in
            let xout = a_block ct b0 xin in
            M.unary_flow_op FO_loop_body_out xout in
          let x = M.unary_flow_op FO_loop_in x in
          let x_invar = alfp s.csl hint lint n_unrolls f_loop_body x in
          let x_exit = M.guard s.csl true tnotc x_invar in
          let x_exit =
            M.unary_flow_op FO_loop_out (M.assert_one "loop,f" x_exit) in
          if !Flags.flag_debug_iter then
            Log.force "Loop invariant:\n%s\nLoop exit:\n%s"
              (M.t_2stri "   " x_invar) (M.t_2stri "   " x_exit)
          else if !Flags.very_silent_mode then
            Log.info "Loop invariant calculated!";
          x_exit
      | Csreturn None ->
          M.unary_flow_op FO_branch_return x
      | Csreturn (Some ex) ->
          let te = tr_c_expr ex in
          let x0 =
            match M.assign_to_return s.csl te x with
            | [ ] -> M.bot x (* returns bottom; we keep it *)
            | ret -> M.assert_one "return" ret in
          if not !Flags.very_silent_mode then
            Log.info "status at return:\n%s" (M.t_2stri "  " x0);
          M.unary_flow_op FO_branch_return x0
      | Csbreak ->
          M.unary_flow_op FO_branch_break x
      | Cscontinue ->
          M.unary_flow_op FO_branch_continue x
      | Csexit ->
          M.bot x
      | Cs_memcad com ->
          begin
            match com with
            | Mc_assume num_exprs ->
                a_assume_num_exprs num_exprs x
            (* adding inductive predicates *)
            | Mc_add_inductive (l, oiname, op) ->
                a_inductive LAssume s.csl l oiname op x
            | Mc_add_segment (l, oiname, op, l_e, oiname_e, op_e) ->
                a_segment LAssume s.csl l oiname op l_e oiname_e op_e x
            (* checking inductive predicates *)
            | Mc_check_segment (l, oiname, op, l_e, oiname_e, op_e) ->
                a_segment LVerify s.csl l oiname op l_e oiname_e op_e x
            | Mc_check_inductive (l, oiname, op) ->
                a_inductive LVerify s.csl l oiname op x
            | Mc_check_bottomness b ->
                let res = M.check_bottomness b x in
                Log.info "ASSERTION @%d (bottomness) %s" s.csl
                  (if res then "verified" else "failed");
                Lib.log_assert res;
                x
            | Mc_unfold l ->
                M.ind_unfold s.csl Graph_sig.Udir_fwd (tr_c_lval l) x
            | Mc_unfold_bseg l ->
                M.ind_unfold s.csl Graph_sig.Udir_bwd (tr_c_lval l) x
            | Mc_unroll _ ->
                Log.fatal_exn "unprocessed memcad unroll command"
            | Mc_merge ->
                M.merge x
            | Mc_sel_merge l ->
                let live, dead = get_live s.csl in
                let hint = { hbe_live = live } in
                let lint = { lbe_dead = dead } in
                M.sel_merge (List.map tr_c_var l) (Some hint) (Some lint) x
            | Mc_force_live _ -> x
            | Mc_kill_flow ->
                M.bot x
            | Mc_array_check ->
                Lib.log_assert (M.check x SL_array);
                x
            | Mc_array_assume ->
                M.assume x SL_array
            | Mc_output_ext (Out_dot (vars, opts)) ->
                do_export s.csl x vars opts
            | Mc_output_stdout ->
                Log.info "Abstract state at point %d(%d)\n%s"
                  s.csl !step (c_stat_2stri "     " s);
                x
            | Mc_reduce_localize l ->
                M.reduce_localize (tr_c_lval l) x
            | Mc_reduce_eager ->
                M.reduce_eager x
            | Mc_comstring _ ->
                Log.fatal_exn "unparsed MemCAD command string"
            | Mc_add_setexprs ls ->
                (* FBR: memcad command badly named: this is an assume !!! *)
                List.fold_left
                  (fun acc y ->
                    M.assume acc (SL_set (tr_c_setexpr y))
                  ) x ls
            | Mc_check_setexprs ls ->
                a_check_setexprs  s.csl ls x
            | Mc_decl_setvars ss ->
                List.fold_left (fun acc y ->
                  M.unary_op acc (UO_env (EO_add_setvar (tr_c_setvar y)))
                ) x ss
          end
      | Csassert c ->
          let tc = tr_c_expr c in
          let b_ok = M.sat tc x in
          let name = Printf.sprintf "ASSERTION @%d (assert)" s.csl in
          let success ( ) =
            Log.info "%s verified" name;
            Lib.log_assert true;
            x in
          let failure x_not =
            Log.error "%s failed" name;
            Log.error "Over-approx of failure:\n%s"
              (M.t_2stri "     " x_not);
            Lib.log_assert false;
            M.assert_one "assert-fail" (M.guard s.csl true tc x) in
          if b_ok then success ( )
          else
            let t_not_c = tr_c_expr (c_expr_neg c) in
            let x_not = M.assert_one "assert" (M.guard s.csl true t_not_c x) in
            if M.is_bot x_not then success ( )
            else failure x_not
      | Csalloc (l, e) ->
          let tl = tr_c_lval l in
          let te = tr_c_expr e in
          M.unary_op x (UO_mem (MO_alloc (tl, te)))
      | Csfree l ->
          let tl = tr_c_lval l in
          M.unary_op x (UO_mem (MO_dealloc tl))
    and a_stat_list (ct: ctxt) (b: c_block) (x: t): t =
      match b with
      | [ ] -> x
      | s0 :: b1 -> a_stat_list ct b1 (a_stat ct s0 x)
    and a_block (ct: ctxt) (b: c_block) (x_pre: t): t =
      if M.is_bot x_pre then
        x_pre
      else
        let x_pre = a_block_in ct x_pre in
        let x_post = a_stat_list ct b x_pre in
        a_block_out ct x_post
    and a_proc_call
        (loc: location) (* call site location *)
        (isfun: bool)   (* whether function or procedure *)
        (ct: ctxt)      (* context in the caller *)
        (c: c_call)     (* call expression *)
        (x: t)          (* abstract pre-condition *)
        : t (* => abstract post-condition *) =
      let x_entry = x in
      (* extraction of the function name *)
      let fun_name = c_call_name c in
      Log.info "a_proc_call: %s" fun_name;
      let f = M.get_function fun_name x_entry in
      (* checking for parameters *)
      let cf_args_len = List.length f.cf_args in
      let cc_args_len = List.length c.cc_args in
      if cf_args_len <> cc_args_len then
        Log.fatal_exn "arg length for %s:\ncf_args_len: %d\ncc_args_len: %d"
          fun_name cf_args_len cc_args_len;
      (* looking for recursion *)
      let ctc = ctxt_call ct fun_name in
      if ctc.ct_currec then
        if !rec_calls then
          begin
            if fun_name != ct.ct_curfun then
              Log.fatal_exn "rec-call: complex (fun)";
            if f.cf_args != [ ] then Log.fatal_exn "rec-call: arguments";
            (* simple recursion:
             *  - caller and callee must be the same;
             *  - no return value, no arguments *)
            if ct.ct_curfix then
              x_entry
            else if not ct.ct_currec then (* first recursive call *)
              (* saving current function entry *)
              let ctc = ctxt_entry_add ctc fun_name x_entry in
              let ctc = { ctc with ct_recdepth = ctc.ct_recdepth + 1 } in
              a_block ctc f.cf_body x_entry
            else (* recursive calls 2 and beyond *)
              let x_old_ent = ctxt_entry_get ctc fun_name in
              if M.is_le x_entry x_old_ent then
                let () =
                  if !Flags.very_silent_mode then
                    Log.info "recursive calls fixpoint (%d iters)"
                      ctc.ct_recdepth
                  else
                    Log.info "recursive calls fixpoint (%d iters)\n%s"
                      ctc.ct_recdepth (M.t_2stri "   " x_old_ent) in
                x_old_ent
              else (* widen, and perform one more iteration *)
                (* let live, dead = get_live loc in *) (* UNUSED ?! *)
                let new_ent, ki = M.widen None None x_old_ent x_entry in
                let new_ent = 
                  match ki with
                  | None -> new_ent
                  | Some ki ->  M.join None None new_ent ki in 
                let ctc = ctxt_entry_add ctc fun_name new_ent in
                let ctc = { ctc with ct_recdepth = ctc.ct_recdepth + 1 } in
                let x_exit = a_block ctc f.cf_body new_ent in
                x_exit
          end
        else
          Log.fatal_exn "recursive %s not handled"
            (if isfun then "function" else "procedure")
      else (* non recursive call *)
        (* setting the return flow to bottom *)
        let x_entry = M.unary_flow_op FO_fun_in x_entry in
        (* entry in a new scope *)
        let x_entry = a_block_in ctc x_entry in
        (* parameter passing *)
        let x_entry =
          List.fold_left2
            (fun accx formal actual ->
              let lv = { clk = Clvar formal ;
                         clt = formal.cv_type } in
              a_assign loc lv actual (a_decl ctc formal accx)
            ) x_entry f.cf_args c.cc_args in
        (* analysis of the function body *)
        let x_exit = a_block ctc f.cf_body x_entry in
        (* exit scope of the function *)
        let x_exit = a_block_out ctc x_exit in
        (* resetting the direct and return flows *)
        let x_exit = M.unary_flow_op (FO_fun_out x_entry) x_exit in
        x_exit
    (* Analysis of a function (analysis starting point *)
    let a_fun (fname: string) (x: t): t =
      let f = M.get_function fname x in
      let ct = { ctxt_empty with
                 ct_funcalls = StringSet.singleton fname ;
                 ct_curfun   = fname } in
      M.unary_flow_op (FO_fun_out x)
        (a_block ct f.cf_body (M.unary_flow_op FO_fun_in x))


    (** Main analysis functions *)
    (* This analysis implementation is quite rough;
     * temporary code, to improve soon *)
    let analyze_prog (mainfun: string) (p: c_prog): unit =
      step := 0;
      let _ = P.live_prog mainfun p in
      (* Initialization: add globals to top *)
      let xtop = M.top p in
      let xglo =
        StringMap.fold (fun _ var t -> a_decl ctxt_empty var t)
          p.cp_vars (M.unary_flow_op FO_block_in xtop) in
      (* Analysis launch *)
      let tlast = a_fun mainfun xglo in
      if not !Flags.very_silent_mode then
        Log.force "Last point:\n%s" (M.t_2stri "    " tlast);
      (* Statistics (optional) *)
      if !enable_stats then
        Statistics.print_statistics (IntMap.map List.rev !stats_accu)
  end
