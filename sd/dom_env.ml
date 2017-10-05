(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_env.ml
 **       the environment abstract domain
 ** Xavier Rival, 2011/05/29 *)
open Data_structures
open Flags
open Lib

open Ast_sig
open Dom_sig
open Graph_sig
open Graph_encode
open Ind_sig
open Svenv_sig

open Ast_utils
open Dom_utils


(* To consider:
 * there is quite a bit of code duplication in the following codes:
 * - merge make_setroots_rel into make_roots_rel
 * - merge table_setroots_compute into table_roots_compute *)


(** Error report *)
module Log =
  Logger.Make(struct let section = "d_env___" and level = Log_level.DEBUG end)


(** Functor lifting a shape domain into an environment domain *)
module Dom_env = functor (D: DOM_MEM_EXPRS) ->
  (struct
    (** Name *)
    (* For timing tags *)
    let module_name: string = "Env"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name D.module_name (D.config_2str ())

    (** Type of abstract values *)
    type t =
        { (* map each variable into a NODE ID and a typ *)
          t_vi:   (int * typ) VarMap.t ;
          (* map each set variable into an Id *)
          t_si:   int  SvarMap.t;
          (* underlying abstract value *)
          t_u:    D.t }

    (** Basic components and functions *)
    (* Bottom element *)
    let bot (t: t): t = { t with t_u = D.bot }
    let is_bot (t: t): bool = D.is_bot t.t_u
    (* Top element, with provided set of roots *)
    let top (): t =
      { t_vi  = VarMap.empty ;
        t_si  = SvarMap.empty ;
        t_u   = D.top () }
    (* Pretty-printing *)
    let t_2stri (ind: string) (t: t): string =
      if is_bot t then
        Printf.sprintf "%s_|_" ind
      else
        let ii = "  "^ind in
        let s_vi =
          VarMap.fold
            (fun v (id, tp) ->
              let name = v.v_name in
              if tp = Tunk then
                begin
                  Log.warn "environment contains [unknown-type]";
                  Printf.sprintf "%s&%s(%d) -> %d\n%s" ii name v.v_id id
                end
              else
                Printf.sprintf "%s&%s(%d): %s -> %d\n%s" ii name v.v_id
                  (typ_2str tp) id
            ) t.t_vi "" in
        let s_si =
          SvarMap.fold
            (fun setv i ->
              Printf.sprintf "%sSetv: %s => %d\n%s" ii setv.s_name i
            ) t.t_si "" in
        let s_u  = D.t_2stri ii t.t_u in
        Printf.sprintf "%s{\n%s%s%s%s}" ind s_vi s_si s_u ind
    let t_2str: t -> string = t_2stri ""
    (* External output *)
    let ext_output (o: output_format) (base: string) (x: t): unit =
      let roots =
        VarMap.fold (fun v (i, _) -> IntMap.add i (v.v_name, v.v_id))
          x.t_vi IntMap.empty in
      D.ext_output o base (fun i -> IntMap.find i roots) x.t_u
    (* SVE fixing *)
    let sve_fix (t: t): t =
      let roots =
        VarMap.fold (fun _ (i, _) -> Aa_sets.add i) t.t_vi Aa_sets.empty in
      (* get rid of sym var env pending synchros, that should have been
       * processed, after checking none of the variable addresses corresponds
       * to one of the removed or modified keys
       * (added is ok, when roots are created) *)
      let t_u, svm = D.sve_sync_bot_up t.t_u in
      let f_check ctxt s =
        PSet.iter
          (fun i ->
            if PSet.mem i s then
              Log.fatal_exn "root %d have been %s!" i ctxt
          ) roots in
      f_check "removed" svm.svm_rem;
      f_check "modified" svm.svm_mod;
      (* result with no synchronization to take into account *)
      { t with t_u = t_u }

    (* Garbage collection *)
    let gc (t: t): t =
      let roots =
        VarMap.fold (fun _ (i, _) -> Aa_sets.add i) t.t_vi Aa_sets.empty in
      sve_fix { t with t_u = D.gc roots t.t_u }
(*
      (* get rid of sym var env pending synchros, that should have been
       * processed, after checking none of the variable addresses corresponds
       * to one of the removed or modified keys
       * (added is ok, when roots are created) *)
      let t_u, svm = D.sve_sync_bot_up t_u0 in
      let sync_keys = PSet.union svm.svm_rem svm.svm_mod in
      PSet.iter
        (fun i ->
          if PSet.mem i sync_keys then
            Log.fatal_exn "root %d have been removed or modified" i
        ) roots;
      (* result with no synchronization to take into account *)
      { t with t_u = t_u }
*)

    (** Management of variables *)

    (* Get a variable *)
    let var_find (t: t) (v: var): int =
      try fst (VarMap.find v t.t_vi)
      with Not_found -> Log.fatal_exn "var %s not found" v.v_name
    let setvar_find (t: t) (v: setvar): int =
      try SvarMap.find v t.t_si
      with Not_found -> Log.fatal_exn "set var %s not found" v.s_name

    (* Add a new variable *)
    let unary_op (op: env_op) (x: t): t =
      match op with
      | EO_add_var v ->
          let n_address, u = D.create_mem_var v.v_typ x.t_u in
          assert (not (VarMap.mem v x.t_vi));
          let x = sve_fix { t_vi = VarMap.add v (n_address, v.v_typ) x.t_vi ;
                            t_si = x.t_si;
                            t_u  = u } in
          Array_node.varm := x.t_vi; (* XR: seems like a gross hack *)
          x
      | EO_add_setvar s ->
          assert (not (SvarMap.mem s x.t_si));
          let sid, u = D.gen_setvar s.s_name x.t_u in
          let t_si =  SvarMap.add s sid  x.t_si in
          { x with
            t_si = t_si ;
            t_u = u }
      | EO_del_var v ->
          let sv = var_find x v in
          gc { t_vi = VarMap.remove v x.t_vi ;
               t_si = x.t_si;
               t_u  = D.delete_mem_var sv x.t_u }
      | EO_del_setvar v ->
          let sv = setvar_find x v in
          gc { x with
               t_si = SvarMap.remove v x.t_si;
               t_u  = D.del_setvar sv x.t_u }

    (** Comparison and Join operators *)
    (* Injection from right to left pre-computation *)
    let make_roots_rel (x0: t) (x1: t): int bin_table =
      VarMap.fold
        (fun v (n0,tp0) acc ->
          let n1,tp1 =
            try VarMap.find v x1.t_vi
            with Not_found ->
              Log.fatal_exn "incompatible environments in roots_compute" in
          assert (tp0 = tp1); (* real type equality! *)
          Aa_maps.add n1 n0 acc
        ) x0.t_vi Aa_maps.empty
    (* Injection from right set var to left set var pre_compution *)
    let make_setroots_rel (x0: t) (x1: t): int bin_table =
      SvarMap.fold
        (fun v n0 acc ->
          let n1 =
            try SvarMap.find v x1.t_si
            with
            | Not_found ->
                Log.fatal_exn
                  "incompatible environments in set_roots_compute" in
          Aa_maps.add n1 n0 acc
        ) x0.t_si Aa_maps.empty

    (* encode of graph *)
    let encode (disj: int) (l: var list) (x: t)
        : renamed_path list * PairSetSet.t * int =
      let var_map =
        if l = [] then
          VarMap.fold
            (fun var (nid, _) acc ->
              if not !Flags.very_silent_mode then
                Log.info "var: %s" var.v_name;
              IntMap.add nid (var.v_name, var.v_id) acc
            ) x.t_vi IntMap.empty
        else
          List.fold_left
            (fun acc var ->
              let nid = var_find x var in
              IntMap.add nid (var.v_name, var.v_id) acc
            ) IntMap.empty l in
      let namer = fun nid -> IntMap.find nid var_map in
      D.encode disj namer x.t_u

    (* Checks if the left argument is included in the right one *)
    let is_le (xl: t) (xr: t): bool =
      if !Flags.flag_debug_is_le_gen then
        Log.force "[Env,al] start is_le\n%s\n%s"
          (t_2stri "  " xl) (t_2stri "  " xr);
      (* Gather roots *)
      let roots_rel = make_roots_rel xl xr in
      let setroots_rel = make_setroots_rel xl xr in
      (* Underlying domain comparison *)
      let b = D.is_le roots_rel setroots_rel xl.t_u xr.t_u in
      if !Flags.flag_debug_is_le_gen then
        Log.force "[Env,al] return is_le: %b" b;
      b
    (* Root pre-computation *)
    let table_roots_compute (x0: t) (x1: t)
        : (int * typ) VarMap.t * int tri_table =
      if x0.t_vi == x1.t_vi then
        (* return the same table, without a physical modification *)
        let r =
          VarMap.fold
            (fun _ (i,_) acc ->
              Aa_sets.add (i, i, i) acc
            ) x0.t_vi Aa_sets.empty in
        x0.t_vi, r
      else
        (* - roots will be consistent with the left argument
         * - table is computed accordingly *)
        let r =
          VarMap.fold
            (fun v (n0,tp0) accr ->
              let n1,tp1 =
                try VarMap.find v x1.t_vi
                with Not_found ->
                  Log.fatal_exn "incompatible environments in roots_compute" in
              assert (tp0 = tp1); (* real type equality! *)
              Aa_sets.add (n0, n1, n0) accr
            ) x0.t_vi Aa_sets.empty in
        x0.t_vi, r
    (* Set Root pre-computation *)
    let table_setroots_compute (x0: t) (x1: t)
        : int SvarMap.t * int tri_table =
      if x0.t_si == x1.t_si then
        (* return the same table, without a physical modification *)
        let r =
          SvarMap.fold
            (fun _ i acc ->
              Aa_sets.add (i, i, i) acc
            ) x0.t_si Aa_sets.empty in
        x0.t_si, r
      else
        (* - roots will be consistent with the left argument
         * - table is computed accordingly *)
        let r =
          SvarMap.fold
            (fun v n0 accr ->
              let n1 =
                try SvarMap.find v x1.t_si
                with Not_found ->
                  Log.fatal_exn
                    "incompatible environments in set roots_compute" in
              Aa_sets.add (n0, n1, n0) accr
            ) x0.t_si Aa_sets.empty in
        x0.t_si, r

    (* Hint translation *)
    let compute_hint_bin (x0: t) (x1: t) (he: hint_be): int hint_bs =
      let s =
        VarSet.fold
          (fun cv acc ->
            try
              let il, _ = VarMap.find cv x0.t_vi in
              let ir, _ = VarMap.find cv x1.t_vi in
              Aa_maps.add ir il acc
            with
            | Not_found ->
                Log.fatal_exn "hint-bin, variable %s not found" cv.v_name
          ) he.hbe_live Aa_maps.empty in
      { hbs_live = s }

    (* Lint translation *)
    let compute_lint_bin (x0: t) (x1: t) (dv: VarSet.t) (le: var lint_be)
      : (int tlval) lint_bs =
      let dead =
        VarSet.fold (fun ele acc -> (Lvar ele, ele.v_typ) :: acc)
          dv le.lbe_dead in
      let s =
        List.fold_left
          (fun acc lv ->
            try
              let lv1_u = map_tlval (var_find x0) lv in
              let lv2_u = map_tlval (var_find x1) lv in
              Aa_maps.add lv1_u lv2_u acc
            with
            | Not_found ->
                Log.fatal_exn "lint-bin, lval %s not found" (vtlval_2str lv)
          ) Aa_maps.empty  dead in
      { lbs_dead = s }

    (* translate the encode graph *)
    let tr_encode (x: t) (g: abs_graph): abs_graph =
      let g_i, n_i, disj_i = Graph_encode.reduce_to_seg g in
      let t_vi = VarMap.fold (fun var (nid, _)  acc ->
        IntMap.add var.v_id nid acc) x.t_vi IntMap.empty in
      let rename (n: PairSet.t) (m: PairSet.t PairSetMap.t) =
        try PairSetMap.find n m, m
        with Not_found ->
          let r_n = PairSet.fold
              (fun (off, uid) acc ->
                try
                  let nid = IntMap.find uid t_vi in
                  PairSet.add (off, nid) acc
                with Not_found -> Log.fatal_exn "tr_encode, var not found"
              ) n PairSet.empty in
          r_n, PairSetMap.add n r_n m in
      let g_i, _ =
        List.fold_left
          (fun (acc, m) (sc, p, dt) ->
            let r_sc, m = rename sc m in
            let r_dt, m = rename dt m in
            (r_sc,p, r_dt)::acc, m
          )  ([], PairSetMap.empty)  g_i in
      let n_i =
        List.fold_left
          (fun acc (sc, _, dt ) ->
            PairSetSet.add sc (PairSetSet.add dt acc)
          ) PairSetSet.empty g_i in
      (g_i, n_i, disj_i)

    (* Generic function for join and widening *)
    let gen_join (j: join_kind) (ho: hint_be option) (lo: (var lint_be) option)
        ((x0, je0): t * join_ele) ((x1, je1): t * join_ele): t =
      if !Flags.flag_debug_join_gen then
        Log.force
          "[Env,al] start %s\n%s\n%s"
          (join_kind_2str j) (t_2stri "  " x0) (t_2stri "  " x1);
      let all_var =
        VarMap.fold
          (fun var _ acc -> VarSet.add var acc) x0.t_vi VarSet.empty in
      let dead_var = match ho with
        | None -> VarSet.empty
        | Some ho -> VarSet.diff all_var ho.hbe_live in
      (* Hint for the underlying domain *)
      let hu = Option.map (compute_hint_bin x0 x1) ho in
      let lu = Option.map (compute_lint_bin x0 x1 dead_var) lo in
      (* translate encode graph *)
      let inl =
        x0.t_u,
        ext_graph (Option.map (tr_encode x0) je0.abs_gi)
          (Option.map (tr_encode x0) je0.abs_go) in
      let inr =
        x1.t_u,
        ext_graph (Option.map (tr_encode x1) je1.abs_gi)
           (Option.map (tr_encode x1) je1.abs_go) in
      (* Gather the roots association table *)
      let ntable, roots_rel = table_roots_compute x0 x1 in
      let stable, setroots_rel = table_setroots_compute x0 x1 in
      (* Underlying domain (graph+num) join *)
      let under =
        if j = Jdweak then
          D.directed_weakening hu roots_rel setroots_rel x0.t_u x1.t_u
        else
          D.join j hu lu roots_rel setroots_rel inl inr in
      (* Output construction *)
      let res = { t_vi = ntable ;
                  t_si = stable ;
                  t_u  = under } in
      if !Flags.flag_debug_join_gen then
        Log.force "[Env,al] return %s\n%s"
          (join_kind_2str j) (t_2stri "    " res);
      res
    (* Join and widening *)
    let join (ho: hint_be option) (lo: (var lint_be) option)
        (x0: t * join_ele) (x1: t * join_ele): t =
      gen_join Jjoin ho lo x0 x1
    let widen (ho: hint_be option) (lo: (var lint_be) option)
        (x0: t *join_ele ) (x1: t *join_ele): t =
      gen_join Jwiden ho lo x0 x1
    (* Directed weakening; over-approximates only the right element *)
    let directed_weakening (ho: hint_be option) (x0: t) (x1: t): t =
      gen_join Jdweak ho None
        (x0, ext_graph None None) (x1, ext_graph None None)

    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    let local_abstract (ho: hint_ue option) (t: t): t =
      let t = gc t in
      (* computation of a hint for the underlying domain *)
      let hu =
        let f h =
          let s =
            VarSet.fold
              (fun cv acc ->
                try Aa_sets.add (fst (VarMap.find cv t.t_vi)) acc
                with Not_found -> acc
              ) h.hue_live Aa_sets.empty in
          { hus_live = s } in
        Option.map f ho in
      (* this is very temporary: numeric domain gets modified *)
      let n_u = D.local_abstract hu t.t_u in
      let tt = gc { t with t_u = n_u } in
      if !Flags.flag_debug_abs_env then
        Log.force "Local_abstract result:\n%s" (t_2stri "  " tt);
      tt

    (** Transfer functions for the analysis *)
    (* Assignment operator *)
    let assign (lv: var tlval) (ex: var texpr) (t: t): t list =
      let f: var -> int = var_find t in
      let lv_u = map_tlval f lv and ex_u = map_texpr f ex in
      let lt_u = D.assign lv_u ex_u t.t_u in
      List.map
        (fun u ->
          let t1 = { t with t_u = u } in
          if Flags.do_gc_on_assign then gc t1
          else t1
        ) lt_u
    (* Condition test *)
    let guard (b: bool) (ex: var texpr) (t: t): t list =
      let ex_u = map_texpr (var_find t) ex in
      let lt_u = D.guard b ex_u t.t_u in
      List.map (fun u -> sve_fix { t with t_u = u }) lt_u
    (* Checking that a constraint is satisfied; returns over-approx sat *)
    let sat (ex: var texpr) (t: t): bool =
      let ex_u = map_texpr (var_find t) ex in
      D.sat ex_u t.t_u
    (* Memory alloc/free *)
    let memory (op: var_mem_op) (t: t): t list =
      let to_map =
        match op with
        | MO_alloc (lv, ex) ->
            let lv_u = map_tlval (var_find t) lv in
            let ex_u = map_texpr (var_find t) ex in
            D.memory (MO_alloc (lv_u, ex_u)) t.t_u
        | MO_dealloc lv ->
            let lv_u = map_tlval (var_find t) lv in
            D.memory (MO_dealloc lv_u) t.t_u in
      List.map (fun u -> sve_fix { t with t_u = u }) to_map

    (** Set domain *)
    let fvar (t: t): var -> int = var_find t
    let fsetvar (t: t): setvar -> int = setvar_find t
    (* Guard and sat functions for set properties *)
    let prepare_setprop (t: t) (ls: var tlval setprop): int tlval setprop =
      map_setprop (fvar t) (fsetvar t) ls
    let prep_log_form t = function
      | SL_set ls ->
          let ls = prepare_setprop t ls in
          SL_set ls
      | SL_ind (ic, lv) ->
          let lv_u = map_tlval (fvar t) lv in
          let ic_u =
            map_gen_ind_call (map_tlval (fvar t)) ~g:(fsetvar t) ic in
          SL_ind (ic_u, lv_u)
      | SL_seg (ic, lv, ic_e, lv_e) ->
          let lv_u, lv_ue = map_tlval (fvar t) lv, map_tlval (fvar t) lv_e in
          let ic_u, ic_ue =
            map_gen_ind_call (map_tlval (fvar t)) ~g:(fsetvar t) ic,
            map_gen_ind_call (map_tlval (fvar t)) ~g:(fsetvar t) ic_e in
          SL_seg (ic_u, lv_u, ic_ue, lv_ue)
      | SL_array ->
          SL_array
    let assume (op: state_log_form) (t: t): t =
      { t with t_u = D.assume (prep_log_form t op) t.t_u }
    let check (op: state_log_form) (t: t): bool =
      D.check (prep_log_form t op) t.t_u

    (** Analysis control *)
    (* Reduction + node relocalization *)
    let reduce_localize (lv: var tlval) (x: t): t option =
      Log.todo_exn "reduce_localize"
(*      let lv_u = map_tlval (var_find x) lv in
      match D.reduce_localize lv_u x.t_u with
      | None -> None
      | Some n_u -> Some { x with t_u = n_u } *)
    (* Eager reduction *)
    let reduce_eager (x: t): t list =
      Log.todo_exn "reduce_eager"
(*      let n_u = D.reduce_eager x.t_u in
      List.map (fun u -> { x with t_u = u }) n_u *)

    (** Assuming and checking inductive edges *)
    (* Unfold *)
    let ind_unfold (u: unfold_dir) (lv: var tlval) (x: t): t list =
      let lv_u = map_tlval (var_find x) lv in
      let l_u = D.ind_unfold u  lv_u x.t_u in
      List.map (fun u -> { x with t_u = u }) l_u
    (* Assume construction *)
    (* Check construction, that an inductive be there *)

    (** Temporary, to short-cut disjunctions *)
    let assert_one (lx: t list): t =
      match lx with
      | [ x ] -> x
      | [ ] | _ :: _ :: _ -> Log.fatal_exn "assert_one"

  end: DOM_ENV)


(** Timer instance of the environment domain (act as a functor on top
 ** of the domain itself) *)
module Dom_env_timing = functor (De: DOM_ENV) ->
  (struct
    module T = Timer.Timer_Mod( struct let name = "Env" end )
    let module_name = "dom_env_timing"
    let config_2str = T.app1 "config_2str" De.config_2str
    type t = De.t
    let bot = T.app1 "bot" De.bot
    let is_bot = T.app1 "is_bot" De.is_bot
    let top = T.app1 "top" De.top
    let t_2stri = T.app2 "t_2stri" De.t_2stri
    let t_2str = T.app1 "t_2str" De.t_2str
    let ext_output = T.app3 "ext_output" De.ext_output
    let gc = T.app1 "gc" De.gc
    let encode = T.app3 "encode" De.encode
    let is_le = T.app2 "is_le" De.is_le
    let gen_join = T.app5 "gen_join" De.gen_join
    let join = T.app4 "join" De.join
    let widen = T.app4 "widen" De.widen
    let directed_weakening = T.app3 "directed_weakening" De.directed_weakening
    let local_abstract = T.app2 "local_abstract" De.local_abstract
    let assign = T.app3 "assign" De.assign
    let guard = T.app3 "guard" De.guard
    let sat = T.app2 "sat" De.sat
    let memory = T.app2 "memory" De.memory
    let unary_op = T.app2 "unary_op" De.unary_op
    let assume = T.app2 "assume" De.assume
    let check = T.app2 "check" De.check
    let reduce_localize = T.app2 "reduce_localize" De.reduce_localize
    let reduce_eager = T.app1 "reduce_eager" De.reduce_eager
    let ind_unfold = T.app3 "ind_unfold" De.ind_unfold
    let assert_one = T.app1 "assert_one" De.assert_one
  end: DOM_ENV)
