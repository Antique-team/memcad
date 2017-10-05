(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_pre_analyze.ml
 **       pre-analysis, to tune the analyzer
 ** Xavier Rival, 2011/10/14 *)
open Ast_sig
open C_sig
open C_analysis_sig
open C_utils
open Data_structures
open Flags
open Lib

(** Improvements to consider:
 **  - replace the current liveness analysis with a more general one,
 **    which may use more complex access paths
 **)


(** Error report *)
module Log =
  Logger.Make(struct let section = "c_prea__" and level = Log_level.DEBUG end)


(** Pre-analysis domain based on access paths *)
module Path_liveness =
  (struct
    type paths = PathSet.t
    (* map from live variable from non-available access paths *)
    type var_paths = paths VarMap.t
    let empty = VarMap.empty
    let t_paths (t: var_paths): PathSet.t VarMap.t = t  
    let t_2str (vs: var_paths): string =
      Printf.sprintf "{ %s }" 
        (VarMap.t_2str ";"
           (fun ele -> Printf.sprintf "{%s}" (PathSet.t_2str ";" ele)) vs)

    let rec is_pre_path p1 p2 =
      match p1, p2 with
      | [], _ -> true
      | _, [] -> false
      | h1::t1, h2::t2 -> h1 = h2 && (is_pre_path t1 t2)

    (* merge two paths set of one live variable *)
    let paths_merge (pl: paths) (pr: paths): paths =
      let compress ll =
        if PathSet.is_empty ll then ll
        else 
          let min_elt = PathSet.min_elt ll in
          let ll = PathSet.remove min_elt ll in
          let rep, acc =
            PathSet.fold
              (fun ele (rep, acc) ->
                if is_pre_path (fst rep) (fst ele) then
                  (rep, acc)
                else (ele, PathSet.add rep acc)
              ) ll (min_elt, PathSet.empty) in
          PathSet.add rep acc in
      let p0 = PathSet.union pl pr in
      compress p0

    (* merge two liveness information *)
    let read_merge (r1: var_paths) (r2: var_paths): var_paths =
      let f k a b =
        match a, b with
        | None, None -> None
        | Some a, None -> Some a
        | None, Some b -> Some b
        | Some a, Some b -> Some (paths_merge a b) in
      VarMap.merge f r1 r2

    (* live_out - def *)
    let merge_out_write (out: var_paths) (write: var_paths): var_paths =
      let reduce_paths (po: paths) (pw: paths): paths = 
        if PathSet.is_empty pw then PathSet.empty 
        else 
          let po =
            PathSet.fold
              (fun ele acc ->
                let b =
                  PathSet.exists
                    (fun ele1 -> is_pre_path (fst ele) (fst ele1)) pw in
                if b then acc 
                else PathSet.add ele acc
              ) po PathSet.empty in
          PathSet.union po pw in 
      let f k a b =
        match a, b with
        | None, None -> None
        | Some a, None -> Some a
        | None, Some b -> if PathSet.is_empty b then None else Some b
        | Some a, Some b -> 
            let p = reduce_paths a b in
            if PathSet.is_empty p then None else Some p in
      VarMap.merge f out write

    (* live_out + in *)
    let merge_out_read (out: var_paths) (read: var_paths): var_paths =
      let reduce_paths (po: paths) (pr: paths): paths = 
        PathSet.fold
          (fun ele acc ->
            let b =
              PathSet.exists
                (fun ele1 -> is_pre_path (fst ele) (fst ele1)) pr in
            if b then acc 
            else PathSet.add ele acc
          ) po PathSet.empty in
      let f k a b =
        match a, b with
        | None, None -> None
        | Some a, None -> Some a
        | None, Some b -> Some (PathSet.empty)
        | Some a, Some b ->
            let p = reduce_paths a b in
            Some p in
      VarMap.merge f out read

    let add_a_path (read: var_paths) (ap: a_path) (lv: c_lval): var_paths =
      VarMap.map
        (fun paths ->
          if PathSet.is_empty paths then PathSet.singleton ([ap], lv)
          else
            PathSet.fold
              (fun (ele, _) acc -> PathSet.add (ele @ [ ap ], lv) acc)
              paths PathSet.empty
        ) read
    let remove_deref (read: var_paths): var_paths =
      VarMap.map
        (fun paths ->
          PathSet.fold
            (fun path acc ->
              if fst path = [] then
                PathSet.add path acc
              else if List.hd (fst path) = Deref then
                PathSet.add (List.tl (fst path), snd path) acc
              else PathSet.add path acc
            ) paths PathSet.empty
        ) read

    (* dereference an expr *)
    let deref_expr (read: var_paths) (lv: c_lval): var_paths =
      add_a_path read Deref lv
    (* access a field of an expr *)
    let field_expr (read: var_paths) (f: string) (lv: c_lval): var_paths =
      add_a_path read (Field f) lv
    (* reference an expression *)
    let addr_expr (read: var_paths): var_paths =
      remove_deref read
    (* add/remove var *)
    let unary_op (op: var_paths unary_operand): var_paths =
      match op with
      | Add_var (v, read) -> VarMap.add v PathSet.empty read
      | Remove_var (v, read) -> VarMap.remove v read
    (* check inclusion *)
    let is_inclusion (rl: var_paths) (rr: var_paths): bool =
      VarMap.for_all
        (fun k ele ->
          try 
            let eler = VarMap.find k rr in
            PathSet.subset ele eler || PathSet.equal ele eler
          with Not_found -> false
        ) rl
  end: DOM_LIVENESS)

(** Pre-analysis domain based on variables (access paths are ignored) *)
module Var_liveness =
  (struct
    type paths = bool
    type var_paths = paths VarMap.t
    let empty = VarMap.empty
    let t_paths (t: var_paths): PathSet.t VarMap.t = 
      VarMap.fold (fun var p acc ->
        VarMap.add var PathSet.empty acc) t VarMap.empty
    let t_2str (vs: var_paths): string =
      Printf.sprintf "{ %s }" 
        (VarMap.t_2str "; " (fun ele -> "") vs)      
    let read_merge (r1: var_paths) (r2: var_paths): var_paths =
      let f k a b =
        match a, b with
        | None, None -> None
        | Some a, None -> Some a
        | None, Some b -> Some true
        | Some a, Some b -> Some true in
      VarMap.merge f r1 r2

    let merge_out_write (out: var_paths) (write: var_paths): var_paths =
      let f k a b =
        match a, b with
        | None, None -> None
        | Some a, None -> Some a
        | None, Some b -> if b then Some b else None 
        | Some a, Some b -> if b then Some b else None  in
      VarMap.merge f out write

    let merge_out_read (out: var_paths) (read: var_paths): var_paths =
      read_merge out read 

    let read_live (read: var_paths): var_paths =
      VarMap.map (fun paths -> true) read
    let deref_expr (read: var_paths) (lv: c_lval): var_paths =
      read_live read
    let field_expr (read: var_paths) (f: string) (lv: c_lval): var_paths =
      read_live read
    let addr_expr (read: var_paths): var_paths =
      read_live read
    let unary_op (op: var_paths C_analysis_sig.unary_operand): var_paths =
      match op with
      | Add_var (v, read) -> VarMap.add v false read
      | Remove_var (v, read) -> VarMap.remove v read
    let is_inclusion (rl: var_paths) (rr: var_paths): bool =
      VarMap.for_all
        (fun k ele ->
          try if ele then VarMap.find k rr else true
          with Not_found -> false
        ) rl
  end: DOM_LIVENESS)

(** Functor to construct the pre-analysis *)
module Gen_pre_analysis = functor (D: DOM_LIVENESS) ->
  (struct
    type var_paths = D.var_paths
    (* Analysis result:
     *   stmt -> set of variables that are "live" *
     *   and set of paths that are dead from each live variable*) 
    type live = var_paths IntMap.t 
    type live_status =
        { lv_p:   c_prog ;  (* C program *)
          pths:   int;      (* numbers of paths *)
          lv_inv: live ;    (* live variables right after statement *)
          lv_cur: var_paths (* current invariant *) }   
    (* Effect of an expression/l-value *)
    type read = var_paths (* variables that are read *)
    let read_empty = D.empty
    let live_status_empty (p: c_prog) = 
      { lv_p   = p ;
        pths   = 1; 
        lv_inv = IntMap.empty ;
        lv_cur = read_empty }

    (* Pretty-printing of live sets *)      
    let read_2str (r: read): string =
      Printf.sprintf "{ %s\n }" (D.t_2str r)
    let live_2str (l: live): string =
      IntMap.fold
        (fun i vs acc -> Printf.sprintf "%s%d: %s\n" acc i (D.t_2str vs) ) l ""
    (* Reference to store the result of the analysis *)
    let live_vars: live ref = ref IntMap.empty
    (* Extraction of live variables *)
    let live_at (l: c_loc): PathSet.t VarMap.t =
      let var_paths =
        try IntMap.find l !live_vars
        with Not_found -> read_empty in
      D.t_paths var_paths
    
    (* Read in lvalues *)
    let rec vread_lval (clval: c_lval): read =
      aux_lvalk read_empty clval
    and l_aux_expr (cexpr: c_expr): read =
      l_aux_exprk read_empty cexpr
    and l_aux_exprk (acc: read) (cexpr: c_expr): read =
      match cexpr.cek with
      | Ceconst _ | Ceuni _ | Cebin _  ->
          Log.fatal_exn "not allowed expression in left side"
      | Celval c_lval ->
          let read = vread_lval c_lval in
          D.read_merge read acc
      | Ceaddrof c_lval ->
          let read = vread_lval c_lval in
          let read = D.addr_expr read in
          D.read_merge read acc  
    and aux_lvalk (acc: read) (clval: c_lval): read =
      match clval.clk with
      | Clvar cvar -> 
          D.unary_op (Add_var (tr_c_var cvar, acc))
      | Clfield (c_lval, f) ->
          let read = vread_lval c_lval in
          let read = D.field_expr read f clval in
          D.read_merge read acc
      | Clderef c_expr ->
          let read = l_aux_expr c_expr in
          let read = D.deref_expr read clval in
          D.read_merge read acc
      | Clindex (c_lval, c_expr) ->
          let read = vread_lval c_lval in
          D.read_merge read acc

    (* Read in expressions *)
    let rec vread_rexpr (cexpr :c_expr): read =
      aux_exprk read_empty cexpr.cek 
    and aux_exprk (acc: read) (c_exprk: c_exprk): read =
      match c_exprk with
      | Ceconst _ -> acc
      | Celval lv ->
          let read = vread_lval lv in
          D.read_merge read acc
      | Ceuni (_, e0) ->
          aux_exprk acc e0.cek
      | Cebin (_, e0, e1) ->
          aux_exprk (aux_exprk acc e0.cek) e1.cek
      | Ceaddrof lv ->
          let read = vread_lval lv in
          D.read_merge read acc

    (* Effect of a declaration *)
    let live_decl (ls: live_status) (v: c_var): live_status =
      { ls with lv_cur = D.unary_op (Remove_var (tr_c_var v, ls.lv_cur)) }

    (* The "use" pre-analysis *)
    let rec live_stat (oc: StringSet.t) (ls: live_status) (s: c_stat)
        : live_status =
      match s.csk with
      | Csdecl d -> live_decl ls d
      | Csassign (lv, ex) ->
          let rl = vread_lval lv in
          let se = vread_rexpr ex in
          (* keep vars read after and not written here or read here *)
          let mow = D.merge_out_write ls.lv_cur rl in
          let mor = D.merge_out_read mow se in
          { ls with lv_cur = mor }
      | Cspcall pc ->
          live_proc_call oc ls pc
      | Csfcall (lv, pc) ->
          let rl = vread_lval lv in
          let read = D.merge_out_write ls.lv_cur rl in
          live_proc_call oc { ls with lv_cur = read } pc
      | Csblock bl ->
          live_block oc ls bl
      | Csif (e0, b1, b2) ->
          let ls2 = live_block oc ls b2 in
          let ls1 = live_block oc { ls with lv_inv = ls2.lv_inv } b1 in
          let lsj = { ls1 with 
                      lv_cur = D.read_merge ls1.lv_cur ls2.lv_cur;
                      pths = ls2.pths + ls1.pths } in
          let read = vread_rexpr e0 in
          let lv_cur =  D.merge_out_read lsj.lv_cur read in
          { lsj with lv_cur = lv_cur }
      | Cswhile (e0, b1, _) ->
          (* we compute the least-fixpoint at the end of the loop body
           *  (same invariant as point right before the loop) *)
          let read0 = vread_rexpr e0 in
          let tmp = live_block oc ls b1 in
          (* effect of one iteration:
           *  evaluation of the effect of the body + the condition *)
          let f (lls: live_status): live_status =
            let ls1 = live_block oc lls b1 in
            { ls1 with lv_cur = D.merge_out_read ls1.lv_cur read0 } in
          let rls = ref { ls with lv_cur = D.merge_out_read ls.lv_cur read0 } in
          let fp = ref true in
          while !fp do
            let next = f !rls in
            fp := not (D.is_inclusion next.lv_cur !rls.lv_cur);
            rls := { next with lv_cur = D.read_merge !rls.lv_cur next.lv_cur };
          done;
          { !rls with pths = tmp.pths + ls.pths }
      | Csreturn oe ->
          (* the liveness pre-analysis is not sound wrt brancing statements *)
          Log.warn "liveness analysis, possibly unsound result: return";
          let se =
            match oe with
            | None -> read_empty
            | Some ex -> vread_rexpr ex in
          let read = D.merge_out_read ls.lv_cur se in
          { ls with lv_cur = read }
      | Csbreak
      | Cscontinue
      | Csexit ->
          (* the liveness pre-analysis is not sound wrt brancing statements *)
          Log.warn
            "liveness analysis, possibly unsound result: break/continue/exit";
          ls
      | Cs_memcad mc ->
          begin
            let read_it oip lv =
              let read = vread_lval lv in
              match oip with
              | None -> read
              | Some ip ->
                  let f read l =
                    List.fold_left
                      (fun acc -> function
                        | Cmp_const _ -> acc
                        | Cmp_lval v -> D.read_merge (vread_lval v) acc
                      ) read l in
                  f read ip.mc_pptr in
            match mc with
            | Mc_add_inductive _ (* maybe consider a write *)
            | Mc_add_segment _
            | Mc_assume _
            | Mc_unfold _
            | Mc_unfold_bseg _
            | Mc_unroll _
            | Mc_merge
            | Mc_output_stdout
            | Mc_output_ext (Out_dot _)
            | Mc_check_bottomness _
            | Mc_kill_flow
            | Mc_array_check
            | Mc_array_assume
            | Mc_reduce_eager
            | Mc_reduce_localize _ 
            | Mc_add_setexprs _
            | Mc_decl_setvars _ 
            | Mc_check_setexprs _ ->
                ls
            | Mc_check_inductive (lv, _, oip) ->
                let read = read_it oip lv in
                { ls with lv_cur = D.merge_out_read ls.lv_cur read }
            | Mc_check_segment (lv, _, oip, lv_e, _, oip_e) ->
                let read = read_it oip lv in
                let read_e = read_it oip_e lv_e in
                let read = D.read_merge read read_e in
                { ls with lv_cur = D.merge_out_read ls.lv_cur read }
            | Mc_sel_merge l ->
                ls
            | Mc_force_live l ->
                let read =
                  List.fold_left
                    (fun acc v -> D.unary_op (Add_var (tr_c_var v, acc)))
                    read_empty l in
                { ls with lv_cur = D.read_merge ls.lv_cur read }
            | Mc_comstring _ ->
                Log.fatal_exn "MemCAD command string left"
          end
      | Csassert ex ->
          let read = vread_rexpr ex in
          { ls with lv_cur = D.read_merge ls.lv_cur read }
      | Csalloc (lv, e) ->
          let rl = vread_lval lv in
          let se = vread_rexpr e in
          (* keep vars read after and not written here or read here *)
          let mow = D.merge_out_write ls.lv_cur rl in
          let mor = D.merge_out_read mow se in
          { ls with lv_cur = mor }    
      | Csfree lv ->
          let r = vread_lval lv in
          { ls with lv_cur = D.merge_out_write ls.lv_cur r }
    and live_proc_call (oc: StringSet.t) (ls: live_status) (c: c_call)
        : live_status =
      let f = get_function ls.lv_p (c_call_name c) in
      if !Flags.flag_debug_live_analysis then
        Log.force "live_call: %s!" f.cf_name;
      if StringSet.mem f.cf_name oc then
        (* recursive call, giving up *)
        ls
      else
        let l1 = live_block (StringSet.add f.cf_name oc) ls f.cf_body in
        let l2 = List.fold_left live_decl l1 f.cf_args in
        let read =
          List.fold_left
            (fun lr ex ->
              D.read_merge (vread_rexpr ex) lr
            ) read_empty c.cc_args in
        { l2 with lv_cur = D.merge_out_read l2.lv_cur read}  
    and live_block (oc: StringSet.t) (ls: live_status) (b: c_block)
        : live_status =
      match b with
      | [ ] -> ls
      | s0 :: b1 ->
          (* block effect *)
          let l1 = live_block oc ls b1 in
          let l0 = live_stat  oc l1 s0 in
          if !Flags.flag_debug_live_analysis then
            Log.force "Point %d: cur=%s" s0.csl (read_2str l0.lv_cur);
          (* invariant saving *)
          let oi =
            try IntMap.find s0.csl l0.lv_inv
            with Not_found -> read_empty in
          let ni = D.read_merge oi l0.lv_cur in
          { l0 with lv_inv = IntMap.add s0.csl ni l0.lv_inv }
    let live_prog (fname: string) (p: c_prog): live =
      Log.info "Liveness analysis...";
      let f = get_function p fname in
      let l =
        let lv = live_block StringSet.empty (live_status_empty p) f.cf_body in
        lv.lv_inv in
      if !Flags.flag_debug_live_analysis then
        Log.force "Results of the liveness analysis:\n%s" (live_2str l);
      live_vars := l;
      Log.info "OK!";
      l
  end: PRE_ANALYSIS)


(** TODO XR => JL: add comments to these definitions *)
module Materialization =
  (struct 
    type visit = 
      | ReadAssign
      | ReadTest
      | WriteAssign

    let visit_2str (v: visit): string =
      match v with
      | ReadAssign -> "ReadAssign"
      | ReadTest -> "ReadTest"
      | WriteAssign -> "WriteAssign"
 
    type state = visit VarMap.t 

    let state_2str (s: state): string  =
      VarMap.t_2str ";" visit_2str s 
      
    type postState = 
      | Single of state
      | Branch of state * state

    type t =
        { t_cur: state;
          t_statm: string;
          t_acc: postState; }

    let binding (pro: VarSet.t * VarSet.t) (f: var -> int)
        : IntSet.t * IntSet.t =
      let get_id (vs: VarSet.t ): IntSet.t  =
        VarSet.fold (fun v a -> IntSet.add (f v) a) vs IntSet.empty in
      let ls, rs = pro in
      get_id ls, get_id rs

    let empty =
      { t_cur   = VarMap.empty;
        t_statm = "";
        t_acc   = Single VarMap.empty}
       
    let t_2str (x: t): string =
      let cur_stat = Printf.sprintf ": %s\n" x.t_statm in
      let cur_str = Printf.sprintf ": %s\n " (state_2str x.t_cur)in
      let acc_str =
        match x.t_acc with
        | Single vv ->
            Printf.sprintf "Post State {Single}: \n %s" (state_2str vv)
        | Branch (tv,fv) ->
            Printf.sprintf "Post State {Branch}:\n True: %s\nFalse: %s"
              (state_2str tv) (state_2str fv) in
      cur_stat^cur_str^acc_str

    let resolve (x: t): VarSet.t * VarSet.t =
      match x.t_acc with
      | Single post ->
          let l =
            VarMap.fold
              (fun var stat acc ->
                if VarMap.mem var post then
                  let pstat = VarMap.find var post in
                  match stat,pstat with
                  | WriteAssign, _ -> acc
                  | _, _ -> VarSet.add var acc
                else
                  acc
              ) x.t_cur VarSet.empty in
          l, VarSet.empty
      | Branch (pl,pr) ->
          VarMap.fold
            (fun var stat (acl,acr) ->
              let acl,acr =
                if VarMap.mem var pl then
                  let pstat = VarMap.find var pl in
                  match stat, pstat with
                  | ReadTest, WriteAssign ->
                      VarSet.add var acl, VarSet.add var acr
                  | ReadTest, _ ->
                      VarSet.add var acl, acr
                  | _, _ -> Log.fatal_exn "unexpected case in resolve"
                else acl, acr in
              if VarMap.mem var pr then
                let pstat = VarMap.find var pr in
                match stat,pstat with
                | ReadTest, WriteAssign ->
                    VarSet.add var acl, VarSet.add var acr
                | ReadTest, _ -> acl, VarSet.add var acr
                | _,_ -> Log.fatal_exn "unexpected case in resolve"
              else
                acl,acr
            ) x.t_cur (VarSet.empty, VarSet.empty)

    let rec read_lv (lv: c_lval) (pre: VarSet.t): VarSet.t =
      match lv.clk with
      | Clfield (c_lv,_) -> read_lv c_lv pre
      | Clindex (_,c_ex) ->
          begin
            match c_ex.cek with
            | Celval { clk = (Clvar cv); clt = _ } ->
                VarSet.add (tr_c_var cv) pre
            | _ -> pre
          end
      | _ -> pre
  
    let rec read_ex (ex: c_expr) (pre: VarSet.t): VarSet.t =
      match ex.cek with
      | Celval lv -> read_lv lv pre
      | Ceuni (_,ce) -> read_ex ce pre
      | Cebin (_,ce1,ce2) -> read_ex ce1 (read_ex ce2 pre)
      | _ -> VarSet.empty
          
    let rec write_lv (lv: c_lval) : VarSet.t * VarSet.t =
      match lv.clk with
      | Clvar cv -> (VarSet.singleton (tr_c_var cv)),VarSet.empty
      | Clfield (c_lv,_) -> write_lv c_lv
      | Clindex (_,ce) ->
          begin
            match ce.cek with
            | Celval {clk = (Clvar cv);clt = _}->
                VarSet.empty,(VarSet.singleton (tr_c_var cv))
            | _ -> Log.fatal_exn "index is not a pure variable"
          end
      | _ -> VarSet.empty,VarSet.empty

    let visit_merge (v1: visit) (v2: visit): visit =
      match v1,v2 with
      | WriteAssign, _ -> WriteAssign
      | _, WriteAssign -> WriteAssign
      | a, b -> a

    let atom_merge (key: VarMap.key) (v1: visit option) (v2: visit option)
        : visit option =
      match v1,v2 with
      | None,Some iv -> Some iv
      | Some iv1,Some iv2 -> Some (visit_merge iv1 iv2)
      | Some iv, None -> Some iv
      | None, None -> None

    let self_merge (cur: state) (acc: postState): state =
      let post =
        match acc with
        | Single s -> s 
        | Branch (s1,s2) -> VarMap.merge atom_merge s1 s2 in
      VarMap.merge atom_merge post cur

    let map_update (vs: VarSet.t) (vm: visit VarMap.t) (v: visit) =
      VarSet.fold (fun ele acc -> VarMap.add ele v acc) vs vm

    (* todo : this function need to be revised *)
    let merge (l: t) (r: t): t = 
      let visit_equal a b =
        match a,b with
        | ReadAssign,ReadAssign
        | ReadTest,ReadTest
        | WriteAssign,WriteAssign -> true
        | _ -> false in
      (* Format.printf "l is %s, r is %s"  (t_2str l) (t_2str r); *)
      assert (VarMap.equal visit_equal l.t_cur r.t_cur);
      let acc =
        match l.t_acc,r.t_acc with
        | Single la,Single ra -> Single (VarMap.merge atom_merge la ra)
        | Branch (la1,la2), Branch (ra1,ra2) ->
            Branch (VarMap.merge atom_merge la1 ra1,
                    VarMap.merge atom_merge la2 ra2)
        | _ -> l.t_acc in
      { t_cur   = l.t_cur;
        t_statm = l.t_statm;
        t_acc   = acc; }

    let assign (lv: c_lval) (ex: c_expr) (x: t): t =
      let read_array = read_ex ex VarSet.empty in
      let write_var,write_array = write_lv lv in
      let npost = self_merge x.t_cur x.t_acc in
      let npost = VarSet.fold VarMap.remove write_var npost in
      let n_cur = map_update read_array VarMap.empty ReadAssign in
      let n_cur = map_update write_array n_cur WriteAssign in
      { t_cur   = n_cur;
        t_statm = Printf.sprintf "%s=%s" (c_lval_2str lv) (c_expr_2str ex);
        t_acc   = Single npost; }

    let guard (ex:c_expr) (x1: t) (x2: t): t =
      let read_array = read_ex ex VarSet.empty in
      let post1 = self_merge x1.t_cur x1.t_acc in
      let post2 = self_merge x2.t_cur x2.t_acc in
      { t_cur   = map_update read_array VarMap.empty ReadTest;
        t_statm = (c_expr_2str ex);
        t_acc   = Branch (post1,post2); }
      
    let decl (c: c_var) (x: t): t =
      let post = self_merge x.t_cur x.t_acc in
      let post = VarMap.remove (tr_c_var c) post in
      { t_cur   = VarMap.empty;
        t_statm = Printf.sprintf "decl %s" (c_var_2str c);
        t_acc   = Single post; }

    let alloc (lv:c_lval) (ex:c_expr) (x: t):t =
      assign lv ex x

    let free (lv: c_lval) (x: t): t = 
      let post = self_merge x.t_cur x.t_acc in
      { t_cur   = VarMap.empty;
        t_statm = Printf.sprintf "free %s" (c_lval_2str lv);
        t_acc   = Single post; }
      
    let assertion (ex: c_expr) (x: t): t = 
      let read_array = read_ex ex VarSet.empty in
      let npost = self_merge x.t_cur x.t_acc in
      let n_cur = map_update read_array VarMap.empty ReadAssign in
      { t_cur   = n_cur;
        t_statm = Printf.sprintf "assertion: %s" (c_expr_2str ex);
        t_acc   = Single npost; }

    (* could be more precise by analyze the arguments of function calls *)
    let pcall (c: c_call) (f: c_fun) (x: t): t = 
      let post = self_merge x.t_cur x.t_acc in
      { t_cur   = VarMap.empty;
        t_statm = Printf.sprintf "pcall %s" (c_expr_2str c.cc_fun);
        t_acc   = Single post;}
      
    let fcall (lv:c_lval) (c: c_call) (f: c_fun) (x: t): t =
      let write_var,write_array = write_lv lv in
      let npost = self_merge x.t_cur x.t_acc in
      let npost = VarSet.fold VarMap.remove write_var npost in
      let n_cur = map_update write_array VarMap.empty WriteAssign in
      { t_cur   = n_cur;
        t_statm = Printf.sprintf "%s=%s" (c_lval_2str lv)(c_expr_2str c.cc_fun);
        t_acc   = Single npost; }
 
    let return (oe: c_expr option) (x: t) : t =
      let n_cur =
        match oe with
        | None -> VarMap.empty
        | Some ce ->   
            let read_array = read_ex ce VarSet.empty in
            map_update read_array VarMap.empty ReadAssign in    
      { t_cur   = n_cur;
        t_statm ="return";
        (* Attention, we could be more precise *)
        t_acc   = Single VarMap.empty; }
  
    let memcad (mem: c_memcad_com) (x: t) : t = 
      let post = self_merge x.t_cur x.t_acc in
      { t_cur   = VarMap.empty;
        t_statm = "memcad";
        t_acc   = Single post; }
  end: DOM_PRE_PROPERTY)




(** TODO XR => JL: add comments to these definitions *)
(** Functor to construct the pre-analysis *)
module Gen_path_sensitive_pre_analysis 
    (D: DOM_PRE_PROPERTY): PRE_PATH_SENSITIVE_ANALYSIS with type elt = D.t =
  struct
    (* Analysis result:
     *   stmt -> set of variables that are "live" *
     *   and set of paths that are dead from each live variable*) 

    type elt = D.t
    type t =
        { t_pro:   c_prog ;  (* C program *)
          t_cur:   D.t;
          t_acc:   D.t IntMap.t ;   }
    (* Effect of an expression/l-value *)

    let empty (p: c_prog) = 
      { t_pro   = p ;
        t_cur   = D.empty; 
        t_acc   = IntMap.empty;}
        
    let t_2str (x: t): string = 
      IntMap.fold
        (fun key ele acc -> 
          let ele_string =
            Printf.sprintf "\n loc is %d, %s\n" key (D.t_2str ele) in
          acc^ele_string
        ) x.t_acc "Materialization result is:"

    (* The "use" pre-analysis *)
    let rec pre_stat (dhead: D.t) (ppost: t) (dtail: D.t) (s: c_stat): t =
      let collect_state (line: int) (cur: D.t) (x: t): t = 
        { x with
          t_cur = cur;
          t_acc = IntMap.add line cur x.t_acc} in        
      let state_merge (key: int)(l: D.t option) (r: D.t option):
          D.t option  =
        match l ,r with
        | None, Some d    -> Some d
        | Some d, None    -> Some d
        | Some d1,Some d2 -> Some (D.merge d1 d2);
        | None,None       -> Log.fatal_exn "ocaml mistake in Map.merge" in
      match s.csk with
      | Csdecl d -> 
          collect_state s.csl (D.decl d ppost.t_cur) ppost
      | Csassign (lv, ex) ->
          collect_state s.csl (D.assign lv ex ppost.t_cur) ppost
      | Cspcall pc ->
          let f = get_function ppost.t_pro (c_call_name pc) in
          Log.info "pre_analysis_proc_call: %s" f.cf_name;
          let pre = pre_block D.empty ppost D.empty f.cf_body in
          let dpre = D.pcall pc f pre.t_cur in
          collect_state s.csl dpre pre
      | Csfcall (lv, pc) ->
          let f = get_function ppost.t_pro (c_call_name pc) in
          Log.info "pre_analysis_proc_call: %s" f.cf_name;
          let pre = pre_block D.empty ppost D.empty f.cf_body in
          let dpre = D.fcall lv pc f pre.t_cur in
          collect_state s.csl dpre pre
      | Csblock bl ->
          pre_block dhead ppost dtail bl
      | Csif (e0, b1, b2) ->
          let ptrue = pre_block D.empty ppost D.empty b1 in
          let pfalse = pre_block D.empty ppost D.empty b2 in
          let pacc = IntMap.merge state_merge ptrue.t_acc pfalse.t_acc in
          let dcur = D.guard e0 ptrue.t_cur pfalse.t_cur in
          collect_state s.csl dcur {ptrue with t_acc = pacc}
      | Cswhile (e0, b1, _) ->
          let dhead0 = D.guard  e0 D.empty ppost.t_cur in
          let phead0 = collect_state s.csl dhead0 ppost in
          let unroll  (idhead: D.t) (iphead: t)  (idtail: D.t) = 
            let ipposthead = pre_block idhead iphead idtail b1 in
            let idhead = D.guard e0 ipposthead.t_cur idtail in
            collect_state s.csl idhead ipposthead in
          let phead1 = unroll dhead0 phead0 ppost.t_cur in
          unroll phead1.t_cur phead1 ppost.t_cur
      | Csreturn oe ->
          collect_state s.csl (D.return oe ppost.t_cur) ppost
      | Csbreak ->
          collect_state s.csl dtail ppost
      | Cscontinue ->
          collect_state s.csl dhead ppost
      | Csexit ->
          ppost
      | Cs_memcad mc ->
          collect_state s.csl (D.memcad mc ppost.t_cur) ppost
      | Csassert ex ->
          collect_state s.csl (D.assertion ex ppost.t_cur) ppost
      | Csalloc (lv, e) ->
          collect_state s.csl (D.alloc lv e ppost.t_cur) ppost
      | Csfree lv ->
          collect_state s.csl (D.free lv ppost.t_cur) ppost
    and pre_block (dhead: D.t)  (ppost: t) (dtail: D.t) (b: c_block): t =
      List.fold_right 
        (fun ele acc ->
          pre_stat dhead acc dtail ele
        ) b ppost
    let pre_prog (fname: string) (p: c_prog): t =
      Log.info "Pre analysis begin...";
      let f = get_function p fname in
      let acc = pre_block D.empty (empty p) D.empty f.cf_body in
      Log.info "OK!";
      acc
    let mat_resolve (x: t): (VarSet.t * VarSet.t) IntMap.t =
      IntMap.map D.resolve x.t_acc
  end





(* HS: this may be deleted *)
(** Live variables analysis
 * A backwarnd analysis of live variables *)

(* Effect of an expression/l-value *)
type read =
    { vread: VarSet.t ; (* variables that are read *)
      vmain: VarSet.t   (* variables that may be deref or addr used *) }
let read_empty: read =
  { vread = VarSet.empty ;
    vmain = VarSet.empty }
(* Analysis result:
 *   stmt -> set of variables that are "live" *)
type live = VarSet.t IntMap.t

(* Pretty-printing of live sets *)
let varset_2str (vs: VarSet.t): string =
  Printf.sprintf "{ %s }" (VarSet.t_2str "; " vs)
let read_2str (r: read): string =
  Printf.sprintf "{ read: %s\n  main: %s }"
    (varset_2str r.vread) (varset_2str r.vmain)
let live_2str (l: live): string =
  IntMap.fold
    (fun i vs acc ->
      Printf.sprintf "%s%d: %s\n" acc i (varset_2str vs)
    ) l ""
(* Reference to store the result of the analysis *)
let live_vars: live ref = ref IntMap.empty
(* Extraction of live variables *)
let live_at (l: c_loc): VarSet.t =
  try IntMap.find l !live_vars
  with Not_found -> VarSet.empty

(* Analysis status:
 *   live information (already computed) + currently live *)
type live_status =
    { lv_p:   c_prog ;  (* C program *)
      lv_inv: live ;    (* live variables right after statement *)
      lv_cur: VarSet.t (* current invariant *) }
let live_status_empty p =
  { lv_p   = p ;
    lv_inv = IntMap.empty ;
    lv_cur = VarSet.empty }

(* Case where all variables found may be read *)
let read_all (r: read): VarSet.t = VarSet.union r.vread r.vmain

(* Read in expressions and lvalues *)
let (vread_expr: c_expr -> read),
  (vread_lval: c_lval -> read) =
  let rec aux_exprk (acc: read): c_exprk -> read = function
    | Ceconst _ -> acc
    | Celval lv ->
        let r = aux_lval acc lv in
        { vread = VarSet.union r.vread r.vmain ;
          vmain = VarSet.empty }
    | Ceuni (_, e0) ->
        aux_expr acc e0
    | Cebin (_, e0, e1) ->
        aux_expr (aux_expr acc e0) e1
    | Ceaddrof lv ->
        aux_lval acc lv
  and aux_expr (acc: read) (ex: c_expr): read =
    aux_exprk acc ex.cek
  and aux_lvalk (acc: read): c_lvalk -> read = function
    | Clvar v ->
        { acc with
          vmain = VarSet.add (tr_c_var v) acc.vmain }
    | Clfield (lv, _) ->
        aux_lval acc lv
    | Clderef ex ->
        aux_expr acc ex
    | Clindex (lv,ex) -> aux_expr (aux_lval acc lv) ex
  and aux_lval (acc: read) (lv: c_lval): read =
    aux_lvalk acc lv.clk in
  aux_expr read_empty, aux_lval read_empty
(* Effect of a declaration *)
let live_decl (ls: live_status) (v: c_var): live_status =
  { ls with lv_cur = VarSet.remove (tr_c_var v) ls.lv_cur }
(* The "use" pre-analysis *)
let rec live_stat (oc: StringSet.t) (ls: live_status) (s: c_stat): live_status =
  match s.csk with
  | Csdecl d -> live_decl ls d
  | Csassign (lv, ex) ->
      let rl = vread_lval lv in
      let se = read_all (vread_expr ex) in
      (* keep vars read after and not written here or read here *)
      let reada = VarSet.union se rl.vread in
      let readb = VarSet.diff ls.lv_cur rl.vmain in
      let readc = VarSet.union readb reada in
      { ls with lv_cur = readc }
  | Cspcall pc ->
      live_proc_call oc ls pc
  | Csfcall (lv, pc) ->
      let rl = vread_lval lv in
      let read = VarSet.diff (VarSet.union ls.lv_cur rl.vread) rl.vmain in
      live_proc_call oc { ls with lv_cur = read } pc
  | Csblock bl ->
      live_block oc ls bl
  | Csif (e0, b1, b2) ->
      let ls2 = live_block oc ls b2 in
      let ls1 = live_block oc { ls with lv_inv = ls2.lv_inv } b1 in
      let lsj = { ls1 with lv_cur = VarSet.union ls1.lv_cur ls2.lv_cur } in
      let read = read_all (vread_expr e0) in
      { lsj with lv_cur = VarSet.union lsj.lv_cur read }
  | Cswhile (e0, b1, _) ->
      (* we compute the least-fixpoint at the end of the loop body
       *  (same invariant as point right before the loop) *)
      let read0 = read_all (vread_expr e0) in
      (* effect of one iteration:
       *  evaluation of the effect of the body + the condition *)
      let f (lls: live_status): live_status =
        let ls1 = live_block oc lls b1 in
        { ls1 with lv_cur = VarSet.union ls1.lv_cur read0 } in
      let rls = ref { ls with lv_cur = VarSet.union ls.lv_cur read0 } in
      let fp = ref true in
      while !fp do
        let next = f !rls in
        fp := not (VarSet.subset next.lv_cur !rls.lv_cur);
        rls := { next with lv_cur = VarSet.union !rls.lv_cur next.lv_cur };
      done;
      !rls
  | Csreturn oe ->
      (* the liveness pre-analysis is not sound wrt brancing statements *)
      Log.warn "liveness analysis may not return a sound result: return";
      let se =
        match oe with
        | None -> VarSet.empty
        | Some ex -> read_all (vread_expr ex) in
      let read = VarSet.union se ls.lv_cur in
      { ls with lv_cur = read }
  | Csbreak
  | Cscontinue
  | Csexit->
      (* the liveness pre-analysis is not sound wrt brancing statements *)
      Log.warn
        "liveness analysis may not return a sound result: break/continue/exit";
      ls
  | Cs_memcad mc ->
      begin
        let read_it oip lv =
          let lexp = { cek = Celval lv;
                       cet = Ctptr (Some lv.clt) } in
          let read = read_all (vread_expr lexp) in
          match oip with
          | None -> read
          | Some ip ->
              let f read l =
                List.fold_left
                  (fun acc -> function
                     | Cmp_const _ -> acc
                     | Cmp_lval v ->
                         let lexp = { cek = Celval lv;
                                      cet = Ctptr (Some lv.clt) } in
                         VarSet.union (read_all (vread_expr lexp)) acc
                  ) read l in
              f read ip.mc_pptr in
        match mc with
        | Mc_add_inductive _ (* maybe consider a write *)
        | Mc_add_segment _
        | Mc_assume _
        | Mc_unfold _
        | Mc_unfold_bseg _
        | Mc_unroll _
        | Mc_merge
        | Mc_output_stdout
        | Mc_output_ext (Out_dot _)
        | Mc_check_bottomness _
        | Mc_kill_flow
        | Mc_array_check
        | Mc_array_assume
        | Mc_reduce_eager
        | Mc_reduce_localize _ 
        | Mc_add_setexprs _
        | Mc_decl_setvars _ 
        | Mc_check_setexprs _ ->
            ls
        | Mc_check_inductive (lv, _, oip) ->
            let read = read_it oip lv in
            { ls with lv_cur = VarSet.union ls.lv_cur read }
        | Mc_check_segment (lv, _, oip, lv_e, _, oip_e) ->
            let read = read_it oip lv in
            let read_e = read_it oip_e lv_e in
            let read = VarSet.union ls.lv_cur read in
            { ls with lv_cur = VarSet.union read read_e }
        | Mc_sel_merge l ->
            ls
        | Mc_force_live l ->
            let read =
              List.fold_left
                (fun acc v -> VarSet.add (tr_c_var v) acc) VarSet.empty l in
            { ls with lv_cur = VarSet.union ls.lv_cur read }
        | Mc_comstring _ ->
            Log.fatal_exn "MemCAD command string left"
      end
  | Csassert ex ->
      let read = read_all (vread_expr ex) in
      { ls with lv_cur = VarSet.union ls.lv_cur read }
  | Csalloc (lv, e) ->
      let rl = vread_lval lv in
      let se = read_all (vread_expr e) in
      (* keep vars read after and not written here or read here *)
      let reada = VarSet.union se rl.vread in
      let readb = VarSet.diff ls.lv_cur rl.vmain in
      let readc = VarSet.union readb reada in
      { ls with lv_cur = readc }
  | Csfree lv ->
      let r = vread_lval lv in
      if r.vread != VarSet.empty then
        Log.info "free: %s" (read_2str r);
      let read = VarSet.union r.vread (VarSet.diff ls.lv_cur r.vmain) in
      { ls with lv_cur = read }
and live_block (oc: StringSet.t) (ls: live_status) (b: c_block): live_status =
  match b with
  | [ ] -> ls
  | s0 :: b1 ->
      (* block effect *)
      let l1 = live_block oc ls b1 in
      let l0 = live_stat oc l1 s0 in
      if !Flags.flag_debug_live_analysis then
        Log.force "Point %d: cur=%s" s0.csl (varset_2str l0.lv_cur);
      (* invariant saving *)
      let oi =
        try IntMap.find s0.csl l0.lv_inv
        with Not_found -> VarSet.empty in
      let ni = VarSet.union oi l0.lv_cur in
      { l0 with lv_inv = IntMap.add s0.csl ni l0.lv_inv }
and live_proc_call (oc: StringSet.t) (ls: live_status)
    (c: c_call): live_status =
  let f = get_function ls.lv_p (c_call_name c) in
  if !Flags.flag_debug_live_analysis then
    Log.force "\nlive_call: %s" f.cf_name;
  if StringSet.mem f.cf_name oc then
    (* recursive call, giving up *)
    ls
  else
    let l1 = live_block (StringSet.add f.cf_name oc) ls f.cf_body in
    let l2 = List.fold_left live_decl l1 f.cf_args in
    let read =
      List.fold_left
        (fun lr ex ->
          VarSet.union (read_all (vread_expr ex)) lr
        ) VarSet.empty c.cc_args in
    { l2 with lv_cur = VarSet.union l2.lv_cur read }
let live_prog (fname: string) (p: c_prog): live =
  Log.info "Liveness analysis...";
  let f = get_function p fname in
  let l =
    let lv = live_block StringSet.empty (live_status_empty p) f.cf_body in
    lv.lv_inv in
  if !Flags.flag_debug_live_analysis then
    Log.force "Results of the liveness analysis:\n%s" (live_2str l);
  live_vars := l;
  l
