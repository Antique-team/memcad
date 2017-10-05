(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_c.ml
 **       C level abstraction layers
 ** Xavier Rival, 2012/02/02 *)
open Ast_sig
open C_analysis_sig
open C_sig
open Data_structures
open Dom_sig
open Flags
open Lib

(** Error report *)
module Log =
  Logger.Make(struct let section = "d_c_____" and level = Log_level.DEBUG end)

(* Local debug flag *)
let debug_module = false

(** Conditional printing *)
(* FBR: must be replaced by proper log level;
 *      apparently used for debug level messages *)
let log msg =
  if not !Flags.very_silent_mode then
    Log.force "%s" msg

(** The build functor, taking an underlying domain as a parameter *)
(* For now, the C layer should account for various C level features:
 *  - variables scopes;
 *  - return variables
 *  - return branches
 *  - possibly branchings at a later point (e.g., break) *)
module Dom_C = functor (D: DOM_DISJ) ->
  (struct
    let module_name = "dom_c"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name D.module_name (D.config_2str ())
    type flow_ctxt = Fc_fun | Fc_loop
    type stack_tok =
        { st_fname:  string ; (* name of the callee *)
          st_callpt: int      (* call point *) }
    type flows =
        { f_direct:  D.t; (* direct flow *)
          f_return:  D.t; (* goto flow *)
          f_break:   D.t list; (* break flow *)
          f_cont:    D.t list; (* continue flow *) }
    type t =
        { (* C program being analyzed *)
          t_c_prog: c_prog;
          (* call stack *)
          t_stack:  stack_tok list;
          (* stack of scopes *)
          t_scopes: VarSet.t list;
          (* stack of set var scopes *)
          t_set_scopes: SvarSet.t list;
          (* return variable *)
          t_retvar: var option;
          (* number of nested_loops being analyzed;
           * serves as a hint for the number of unrolls *)
          t_nloops: int;
          (* scope depth in loops *)
          t_scopedpth: (flow_ctxt * int) list;
          (* output file number (for LaTeX output) *)
          t_outcnt: int;
          (* underlying domain abstract value *)
          t_u:      flows }

    (* Internal counter for the creation of return variables *)
    let retvar_counter: int option ref = ref None
    let get_retvar_id ( ): int =
      (* Initialization of the counter on the first call *)
      let i =
        match !retvar_counter with
        | None ->
            let k = !C_process.max_c_var_id + 1 in
            retvar_counter := Some k;
            k
        | Some k -> k in
      retvar_counter := Some (i + 1);
      i

    (* Basic debugging functions *)
    let scopedpth_2str (l: (flow_ctxt * int) list): string =
      List.fold_left
        (fun a -> function
          | Fc_fun, i -> Printf.sprintf "%sf.%d :: " a i
          | Fc_loop, i -> Printf.sprintf "%sl.%d :: " a i
        ) "" l

    (* Lift functions *)
    let map_dir (f: D.t -> 'a) (x: t): 'a =
      f x.t_u.f_direct
    let flows_map_all (f: D.t -> D.t) (y: flows): flows =
      { f_direct = f y.f_direct;
        f_return = f y.f_return;
        f_break  = y.f_break;
        f_cont   = y.f_cont; }
    let lift_dir (f: D.t -> D.t) (x: t): t =
      { x with
        t_outcnt = x.t_outcnt + 1;
        t_u      = { x.t_u with
                     f_direct = f x.t_u.f_direct } }
    (* used for join and widen *)
    let map2_ontop (f: D.t -> D.t -> D.t)
        (l0: D.t list) (l1: D.t list): D.t list =
      match l0, l1 with
      | [ ], [ ] -> [ ]
      | [ ], l | l, [ ] -> l
      | x0 :: u0, x1 :: u1 ->
          assert (u0 == u1);
          f x0 x1 :: u0

    (* Bottom element *)
    let bot (x: t): t = { x with t_u = { f_direct = D.bot;
                                         f_return = D.bot;
                                         f_break  = [];
                                         f_cont   = []; } }
    let is_bot (x: t): bool = D.is_bot x.t_u.f_direct

    (* Disjunction size *)
    let disj_size (x: t): int = D.disj_size x.t_u.f_direct

    (* Top element, with provided set of roots *)
    let top (p: c_prog): t =
      { t_c_prog = p;
        t_stack  = [ ];
        t_scopes = [ ];
        t_set_scopes = [ ];
        t_retvar = None;
        t_nloops = 0;
        t_scopedpth = [ Fc_fun, 0 ];
        t_outcnt = 0;
        t_u      = { f_direct = D.top ();
                     f_return = D.bot;
                     f_break  = [];
                     f_cont   = [] } }

    (* Pretty-printing *)
    let t_2stri (ind: string): t -> string =
      map_dir (D.t_2stri ind)
    (* External output *)
    let ext_output (o: output_format) (base: string) (x: t): t =
      D.ext_output o (Printf.sprintf "%s-N%d" base x.t_outcnt) x.t_u.f_direct;
      { x with t_outcnt = x.t_outcnt + 1 }

    (* management of (set) variables *)
    let rec unary_op (x: t) (op: unary_op): t =
      match op with
      | UO_env (EO_add_var v) ->
          let nscopes =
            match x.t_scopes with
            | [ ] -> Log.fatal_exn "add_var: empty_scopes"
            | c :: u ->
                assert (not (VarSet.mem v c)) ;
                VarSet.add v c :: u in
          let f = D.unary_op op in
          { x with
            t_scopes = nscopes ;
            t_outcnt = x.t_outcnt + 1;
            t_u      = flows_map_all f x.t_u }
      | UO_env (EO_add_setvar v) ->
          let nscopes =
            match x.t_set_scopes with
            | [ ] -> Log.fatal_exn "add setvar: empty_scopes"
            | c :: u ->
                assert (not (SvarSet.mem v c));
                SvarSet.add v c :: u in
          { x with
            t_set_scopes = nscopes ;
            t_outcnt     = x.t_outcnt + 1;
            t_u          = flows_map_all (D.unary_op op) x.t_u }
      | UO_ret (Some typ) ->
          (* Creation of a return variable *)
          let vret = { v_name = "#return" ;
                       v_id   = get_retvar_id ( );
                       v_typ  = typ } in
          { (unary_op x (UO_env (EO_add_var vret))) with
            t_outcnt = x.t_outcnt + 1;
            t_retvar = Some vret }
      | UO_ret None ->
          { x with
            t_outcnt = x.t_outcnt + 1;
            t_retvar = None }
      | UO_env (EO_del_var v) ->
          let nscopes =
            match x.t_scopes with
            | [ ] -> Log.fatal_exn "rem_var: empty_scopes"
            | c :: u ->
                assert (VarSet.mem v c) ;
                VarSet.remove v c :: u in
          { x with
            t_scopes = nscopes ;
            t_outcnt = x.t_outcnt + 1;
            t_u      = flows_map_all (D.unary_op op) x.t_u }
      | UO_env (EO_del_setvar v) ->
          let nscopes =
            match x.t_set_scopes with
            | [ ] -> Log.fatal_exn "rem setvar: empty_scopes"
            | c :: u ->
                assert (SvarSet.mem v c);
                SvarSet.remove v c :: u in
          { x with
            t_set_scopes = nscopes ;
            t_outcnt     = x.t_outcnt + 1;
            t_u          = flows_map_all (D.unary_op op) x.t_u }
      | UO_mem (MO_alloc _ | MO_dealloc _) ->
          lift_dir (D.unary_op op) x

    let assume (x: t) (op: state_log_form): t =
      match op with
      | SL_set _
      | SL_ind _
      | SL_seg _ -> lift_dir (D.assume op) x
      | SL_array ->
          let u = { x.t_u with
                    f_direct = D.assume SL_array x.t_u.f_direct } in
          { x with t_u = u }

    let check (x: t) (op: state_log_form): bool =
      D.check op x.t_u.f_direct

    (** Checks that two abstract values are similar; fails otherwise *)
    let are_similar (x0: t) (x1: t): unit =
      let rec cmp_list (l0: (flow_ctxt * int) list) l1 : bool =
        if l0 == l1 then true
        else
          match l0, l1 with
          | [ ], [ ] -> true
          | a0 :: b0, a1 :: b1 -> a0 = a1 && cmp_list b0 b1
          | _, _ -> false in
      assert (x0.t_c_prog == x1.t_c_prog);
      assert (x0.t_retvar == x1.t_retvar);
      assert (x0.t_set_scopes == x1.t_set_scopes);
      assert (x0.t_nloops == x1.t_nloops);
      assert (x0.t_scopes == x1.t_scopes);
      assert (cmp_list x0.t_scopedpth x1.t_scopedpth)

    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    let is_le (x0: t) (x1: t): bool =
      are_similar x0 x1;
      D.is_le x0.t_u.f_direct x1.t_u.f_direct
        && D.is_le x0.t_u.f_return x1.t_u.f_return

    (* Join *)
    let join (hbe: hint_be option) (lbe: (var lint_be) option)
        (x0: t) (x1: t): t =
      are_similar x0 x1;
      let fjoin = D.join hbe lbe in
      let ndir =
        log "join direct";
        fjoin x0.t_u.f_direct x1.t_u.f_direct in
      let nret =
        log "join return";
        fjoin x0.t_u.f_return x1.t_u.f_return in
      let nbreak =
        log "join break";
        map2_ontop fjoin x0.t_u.f_break x1.t_u.f_break in
      let ncont =
        log "join continue";
        map2_ontop fjoin x0.t_u.f_cont x1.t_u.f_cont in
      { x0 with
        t_outcnt = 1 + max x0.t_outcnt x1.t_outcnt;
        t_u      = { f_direct = ndir;
                     f_return = nret;
                     f_break  = nbreak;
                     f_cont   = ncont;} }

    (* Widening:
     *  - does not widen on break flow, assumed not to be part of the loop
     *    (it is on the loop exit edge)
     *  - we could do the same on the return flow *)
    let widen (hbe: hint_be option) (lbe: (var lint_be) option)
        (x0: t) (x1: t): t * t option =
      let fwiden = D.widen hbe lbe in
      are_similar x0 x1;
      assert (x0.t_stack  == x1.t_stack );
      let ndir =
        log "widen direct";
        fwiden x0.t_u.f_direct x1.t_u.f_direct in
      let nret =
        log "widen return";
        fwiden x0.t_u.f_return x1.t_u.f_return in
      (* assert (snd nret = None); *)
      let nbk =
        log (Printf.sprintf "widen break %d-%d"
               (List.length x0.t_u.f_break) (List.length x1.t_u.f_break));
        map2_ontop (D.join hbe lbe) x0.t_u.f_break  x1.t_u.f_break in
      let ncont =
        log (Printf.sprintf "widen continue %d-%d"
               (List.length x0.t_u.f_cont) (List.length x1.t_u.f_cont));
        map2_ontop (D.join hbe lbe) x0.t_u.f_cont  x1.t_u.f_cont in
      let xl =
        { x0 with
          t_outcnt = 1 + max x0.t_outcnt x1.t_outcnt;
          t_u      = { f_direct = fst ndir;
                       f_return = fst nret;
                       f_break  = nbk;
                       f_cont   = ncont; } } in
      match snd ndir, snd nret with
      | None, None -> xl, None
      | Some dir, None ->
          xl, Some { xl with
                     t_u = { xl.t_u with
                             f_direct = dir;
                             f_return = D.bot; } }
      | None, Some ret ->
          xl, Some { xl with
                     t_u = { xl.t_u with
                             f_direct = D.bot;
                             f_return = ret; } }
      | Some dir, Some ret ->
          xl, Some { xl with
                     t_u = { xl.t_u with
                             f_direct = dir;
                             f_return = ret; } }
    (* For the same reason as for widening, directed_weakening extrapolates
     * only on the direct flow *)
    let directed_weakening (hbe: hint_be option) (x0: t) (x1: t): t =
      are_similar x0 x1;
      assert (x0.t_stack  == x1.t_stack );
      let ndir =
        Log.info "widen direct";
        D.directed_weakening hbe x0.t_u.f_direct x1.t_u.f_direct in
      { x1 with
        t_outcnt = 1 + max x0.t_outcnt x1.t_outcnt;
        t_u      = { x1.t_u with
                     f_direct = ndir; } }

    (** Transfer functions for the analysis *)
    (* Assignment operator *)
    let assign (loc: location) (lv: var tlval) (ex: var texpr) (x: t): t list =
      List.map
        (fun y -> { x with
                    t_outcnt = x.t_outcnt + 1;
                    t_u = { x.t_u with
                            f_direct = y } }
        ) (D.assign loc lv ex x.t_u.f_direct)
    (* Condition test *)
    let guard (loc: location) (b: bool) (lv: var texpr) (x: t): t list =
      List.map
        (fun y -> { x with
                    t_outcnt = x.t_outcnt + 1;
                    t_u = { x.t_u with
                            f_direct = y } }
        ) (D.guard loc b lv x.t_u.f_direct)
    (* Checking that a constraint is satisfied; returns over-approx sat *)
    let sat (lv: var texpr): t -> bool =
      map_dir (D.sat lv)

    (** Set expressions conditions *)
    (* Check that a set constraint is proved by current abstract state *)
    let check_setprops (x: t) (l: var tlval setprop list): bool =
      List.for_all (fun y -> check x (SL_set y)) l

    (** Assuming and checking inductive edges *)
    (* Unfold *)
    let ind_unfold (loc: location)
        (u: Graph_sig.unfold_dir) (lv: var tlval): t -> t =
      lift_dir (D.ind_unfold loc u lv)

    (** Regression testing *)
    (* Check invariant bottomness *)
    let check_bottomness (b: bool) (t: t): bool =
      if is_bot t then b else not b

    (** Management of disjunctions *)
    let merge (x: t): t =
      lift_dir D.merge_disjuncts x
    let sel_merge (l: var list) (hbe: hint_be option)
        (lbe: (var lint_be) option) (x: t): t =
      lift_dir (D.sel_merge l hbe lbe) x
    let assert_one (msg: string) (t: t list): t =
      match t with
      | [ y ] -> y
      | [ ] -> Log.fatal_exn "assert one (%s): returns _|_" msg
      | _ :: _ :: _ -> Log.fatal_exn "illegal state in assert one [%s] %d"
                         msg (List.length t)
    (* Adding an abs_hist_atom *)
    let push_hist_atom (ah: Disj_sig.abs_hist_atom): t -> t =
      lift_dir (D.push_hist_atom ah)

    (** Analysis control *)
    (* Reduction + node relocalization *)
    let reduce_localize (lv: var tlval) (x: t): t =
      lift_dir (D.reduce_localize lv) x
    (* Eager reduction *)
    let reduce_eager (x: t): t = lift_dir D.reduce_eager x


    (** Auxilliary functions for handling flows and C operations *)

    (* Destruction of variables in scope defined by c,s *)
    let aux_destroy_scope_u (c, s) (u: D.t): D.t =
      let u =
        VarSet.fold
          (fun v acc ->
            if !Flags.flag_debug_scopes then
              Log.force "destroy_scope removes var %s"
                (Ast_utils.var_2str v);
            D.unary_op (UO_env (EO_del_var v)) acc) c u in
      SvarSet.fold
        (fun v acc ->
          if !Flags.flag_debug_scopes then
            Log.force "destroy_scope removes set var %s"
              v.s_name;
          D.unary_op (UO_env (EO_del_setvar v)) acc) s u

    (* Dig up a series of scopes *)
    let aux_destroy_scopes (fc, n) (vs, ss) (u: D.t): D.t =
      if fc = Fc_fun then Log.fatal_exn "destroy_scopes: no break zone";
      let rec aux (vs, ss) i u =
        assert (i >= 0);
        if i = 0 then u
        else
          match vs, ss with
          | [ ], _ | _, [ ] ->
              Log.fatal_exn "destroy_scopes: not enough scopes"
          | vs0 :: vs1, ss0 :: ss1 ->
              Log.info "destroying one scope";
              aux (vs1, ss1) (i-1) (aux_destroy_scope_u (vs0, ss0) u) in
      aux (vs, ss)(*(x.t_scopes, x.t_set_scopes)*) n (*x.t_u.f_direct*)u

    (* Function calls *)
    let get_function (fname: string) (x: t): c_fun =
      C_utils.get_function x.t_c_prog fname
    let restore_return_var (x_pre: t) (x: t): t =
      match x.t_retvar with
      | None      -> { x with t_retvar = x_pre.t_retvar }
      | Some vret ->
          { (unary_op x (UO_env (EO_del_var vret))) with
            t_retvar = x_pre.t_retvar }
    (* Assign to the return variable *)
    let assign_to_return (loc: location) (ex: var texpr) (x: t): t list =
      match x.t_retvar with
      | None -> []
      | Some vret -> assign loc (Lvar vret, snd ex) ex x
    let assign_from_return (loc: location) (lv: var tlval) (x: t): t list =
      let vret =
        match x.t_retvar with
        | None -> Log.fatal_exn "assign_from_return: no return variable"
        | Some v -> v in
      assign loc lv (Elval (Lvar vret, snd lv), snd lv) x

    let enter_break_zone (x: t): t =
      if debug_module then
        Log.debug "enter_bz scope: %s" (scopedpth_2str x.t_scopedpth);
      { x with
        t_u = { x.t_u with
                f_break = D.bot :: x.t_u.f_break } }
    let exit_break_zone (x: t): t =
      if debug_module then
        Log.debug "exit_bz scope: %s" (scopedpth_2str x.t_scopedpth);
      match x.t_u.f_break with
      | [] -> Log.fatal_exn "exit_break_zone, with empty break stack"
      | bt :: bu ->
          { x with
            t_u = { x.t_u with
                    f_direct = D.join None None x.t_u.f_direct bt;
                    f_break  = bu } }


    (** Unary flow operations *)

    (* Enter a block:
     *  - updates the scope stacks *)
    let do_block_in (x: t) =
      if debug_module then
        Log.debug "in_scope scope: %s" (scopedpth_2str x.t_scopedpth);
      let sd =
        match x.t_scopedpth with
        | [ ] -> Log.fatal_exn "in_scope"
        | (fc, i) :: b -> (fc, i + 1) :: b in
      { x with
        t_scopes     = VarSet.empty :: x.t_scopes;
        t_scopedpth  = sd;
        t_set_scopes = SvarSet.empty :: x.t_set_scopes }

    (* Exit out of a block:
     *  - dispose the variables that are not visible anymore
     *  - updates the scope stacks *)
    let do_block_out (x: t) =
      if debug_module then
        Log.debug "out_scope scope: %s" (scopedpth_2str x.t_scopedpth);
      match x.t_scopes, x.t_scopedpth, x.t_set_scopes with
      | [ ], _, _ | _, [ ], _ | _, _, [ ] -> Log.fatal_exn "out_scope"
      | c :: u, (fc0, i0) :: sd1, s :: l ->
          let sd = (fc0, i0 - 1) :: sd1 in
          let x =
            VarSet.fold
              (fun v acc ->
                if !Flags.flag_debug_scopes then
                  Log.force "out_scope removes var %s"
                    (Ast_utils.var_2str v);
                unary_op acc (UO_env (EO_del_var v))) c x in
          let x =
            SvarSet.fold
              (fun v acc ->
                if !Flags.flag_debug_scopes then
                  Log.force "out_scope removes set var %s"
                    v.s_name;
                unary_op acc (UO_env (EO_del_setvar v))
              ) s x in
          { x with
            t_scopes     = u;
            t_scopedpth  = sd;
            t_set_scopes = l }

    (* Enter a function:
     *  - return flow becomes bottom;
     *  - no loop in the current function *)
    let do_fun_in (x: t): t =
      { x with
        t_scopedpth = (Fc_fun, 0) :: x.t_scopedpth;
        t_u = { x.t_u with f_return = D.bot } }

    (* Exit of a function:
     *  - return flow is joined into direct flow;
     *  - old return flow reinstalled;
     *  - loop scope depth popped as well *)
    let do_fun_out (x_pre: t) (x: t): t =
      if x.t_scopedpth = [ ] then Log.fatal_exn "fun_end: no scope";
      { x with
        t_scopedpth = List.tl x.t_scopedpth;
        t_u = { x.t_u with
                f_direct = D.join None None x.t_u.f_return x.t_u.f_direct;
                f_return = x_pre.t_u.f_return; } }

    (* Entry into a loop statement:
     *  - increments loop depth;
     *  - enters break zone *)
    let do_loop_in (x: t): t =
      enter_break_zone { x with t_nloops = x.t_nloops + 1 }

    (* Exit out of a loop statement:
     *  - decreements loop depth;
     *  - exits break zone *)
    let do_loop_out (x: t): t =
      exit_break_zone { x with t_nloops = x.t_nloops - 1 }

    (* Loop body entry:
     *  - continue flow initialized to _|_
     *  - stop point in the stack of scopes
     *  -  *)
    let do_loop_body_in (x: t): t =
      { x with
        t_u = { x.t_u with
                f_cont = D.bot :: x.t_u.f_cont };
        t_scopedpth = (Fc_loop, 0) :: x.t_scopedpth }

    (* Loop body exit:
     *  - continue flow joined into the direct flow and removed
     *  - remove the stop point in the stack of scopes *)
    let do_loop_body_out (x: t): t =
      let sd =
        match x.t_scopedpth with
        | [ ] | (Fc_fun, _) :: _ ->
            Log.fatal_exn "loop_body_out: no loop scope"
        | (Fc_loop, _) :: sd0 -> sd0 in
      match x.t_u.f_cont with
      | [] -> Log.fatal_exn "loop_body_out: empty continue stack"
      | bt :: bu ->
          { x with
            t_u = { x.t_u with
                    f_direct = D.join None None x.t_u.f_direct bt;
                    f_cont   = bu };
            t_scopedpth = sd }

    (* Follow a break:
     *  - kill scopes on the break stack in the direct flow
     *  - direct flow joined into the break flow, after scope exits *)
    let do_branch_break (x: t): t =
      match x.t_u.f_break, x.t_scopedpth with
      | [ ], _ -> Log.fatal_exn "branch_break: empty break stack"
      | _, [ ] -> Log.fatal_exn "branch_break: no scope depth"
      | bt :: bu, (fc, n) :: _ ->
          let break_flow =
            aux_destroy_scopes (fc, n)
              (x.t_scopes, x.t_set_scopes) x.t_u.f_direct in
          { x with
            t_u = { x.t_u with
                    f_direct = D.bot;
                    f_break  = D.join None None break_flow bt :: bu } }

    (* Follow a continue:
     *  - kill scopes on the break stack in the direct flow
     *  - direct flow joined into the continue flow, after scope exits *)
    let do_branch_continue (x: t): t =
      match x.t_u.f_cont, x.t_scopedpth with
      | [ ], _ -> Log.fatal_exn "branch_continue: empty continue stack"
      | _, [ ] -> Log.fatal_exn "branch_continue: no scope depth"
      | bt :: bu, (fc, n) :: _ ->
          let cont_flow =
            aux_destroy_scopes (fc, n)
              (x.t_scopes, x.t_set_scopes) x.t_u.f_direct in
          { x with
            t_u = { x.t_u with
                    f_direct = D.bot;
                    f_cont  = D.join None None cont_flow bt :: bu } }

    (* Follow a return:
     *  - direct flow joined into the return flow *)
    let do_branch_return (x: t): t =
      { x with
        t_u = { x.t_u with
                f_direct = D.bot;
                f_return = D.join None None x.t_u.f_return x.t_u.f_direct; } }

    (* Generic unary flow operation *)
    let unary_flow_op (f: t flow_op) (x: t): t =
      if debug_module then
        Log.debug "order scope %s: %s"
          (flow_op_2str f) (scopedpth_2str x.t_scopedpth);
      match f with
      | FO_block_in        -> do_block_in x
      | FO_block_out       -> do_block_out x
      | FO_fun_in          -> do_fun_in x
      | FO_fun_out xold    -> do_fun_out xold x
      | FO_loop_in         -> do_loop_in x
      | FO_loop_out        -> do_loop_out x
      | FO_loop_body_in    -> do_loop_body_in x
      | FO_loop_body_out   -> do_loop_body_out x
      | FO_branch_break    -> do_branch_break x
      | FO_branch_continue -> do_branch_continue x
      | FO_branch_return   -> do_branch_return x

    (* Managing loop count *)
    let loop_beg (x: t): t =
      enter_break_zone { x with t_nloops = x.t_nloops + 1 }
    let loop_end (x: t): t =
      exit_break_zone { x with t_nloops = x.t_nloops - 1 }
    let loop_count (x: t): int = x.t_nloops


    (** Statistics *)
    let get_stats (x: t): Statistics.ainv_stats =
      let nbreaks =
        List.fold_left (fun acc u -> acc + D.get_stats u) 0 x.t_u.f_break in
      { Statistics.as_dir_disjuncts   = D.get_stats x.t_u.f_direct;
        Statistics.as_break_disjuncts = nbreaks; }

  end: DOM_C)
