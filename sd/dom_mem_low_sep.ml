(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_mem_low_sep.ml
 **       Basis for a separating product of shape abstraction
 ** Xavier Rival, Antoine Toubhans, 2013/04/11 *)
open Data_structures
open Flags
open Lib

open Ast_sig
open Dom_sig
open Dom_utils
open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig
open Svenv_sig

open Ast_utils

open Dom_dictionary

module Log =
  Logger.Make(struct let section = "dm_lsep_" and level = Log_level.DEBUG end)

(** The separating product domain ( D1 * D2 ) *)
module Dom_sep_dic =
  functor (DIC: DIC) -> (* dictionary *)
    functor (D1: DOM_MEM_LOW) -> (* first shape component *)
      functor (D2: DOM_MEM_LOW) -> (* second shape component *)
  (struct
    (** Module name *)
    let module_name = Printf.sprintf "(%s * %s)" D1.module_name D2.module_name

    (** Type of abstract values *)
    type t =
        { (* bindings from local symvar to underlying symvars *)
          t_dic:    DIC.t;
          (* first shape component *)
          t_fst:    D1.t;
          (* second shape component *)
          t_snd:    D2.t;
          (* equalities between symb. var. of different shape component *)
          t_eqs:    (int, int) Dom_eqs.t;
          (* local symvar env modifications *)
          t_envmod:  svenv_mod; }

    (** Domain initialization to a set of inductive definitions *)
    (* Domain initialization to a set of inductive definitions *)
    let init_inductives _ (s: StringSet.t): Keygen.t =
      Log.fatal_exn "init_inductives should not be called"
    let inductive_is_allowed (ind: string): bool =
      D1.inductive_is_allowed ind || D2.inductive_is_allowed ind

    (** Fixing sets of keys *)
    let sve_sync_bot_up (x: t): t * svenv_mod =
      { x with t_envmod = svenv_empty }, x.t_envmod

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t = { t_dic    = DIC.empty;
                   t_fst    = D1.bot;
                   t_snd    = D2.bot;
                   t_eqs    = Dom_eqs.empty;
                   t_envmod = svenv_empty; }

    let is_bot (x: t): bool =
      D1.is_bot x.t_fst || D2.is_bot x.t_snd

    (* Top element, with empty set of roots *)
    let top (): t = { t_dic    = DIC.empty;
                      t_fst    = D1.top ();
                      t_snd    = D2.top ();
                      t_eqs    = Dom_eqs.empty;
                      t_envmod = svenv_empty; }

    (* Pretty-printing *)
    let eqs_2stri ind eqs =
      let pp loc i = Printf.sprintf "(%s, %i)" (dic_side_2str loc) i in
      Dom_eqs.t_2stri (pp Dic_fst) (pp Dic_snd) ind eqs

    let t_2stri (ind: string) (x: t): string =
      let nind = ind^"\t" in
      let str_name = Printf.sprintf "%sSEPARATED PRODUCT %s\n" ind module_name
      and str_dic =
        Printf.sprintf "%sDIC{\n%s%s}\n"
          ind (DIC.t_2stri nind x.t_dic) ind
      and str_eqs =
        Printf.sprintf "%sEQS{\n%s%s}\n"
          ind (eqs_2stri nind x.t_eqs) ind
      and str_1 =
        Printf.sprintf "%sD1%s{\n%s%s}\n"
          ind D1.module_name (D1.t_2stri nind x.t_fst) ind
      and str_2 =
        Printf.sprintf "%sD2%s{\n%s%s}\n"
          ind D2.module_name (D2.t_2stri nind x.t_snd) ind
      and sve =
        if !Flags.flag_debug_symvars then
          Printf.sprintf "%sSVE-Dom-sep:\n%s" ind
            (svenv_2stri (ind^"  ") x.t_envmod)
        else "" in
      str_name ^ str_dic ^ str_eqs ^ str_1 ^ str_2 ^ sve
    let t_2str: t -> string = t_2stri ""

    (* External output *)
    let ext_output (o: output_format) (base: string) (namer: namer) (x: t)
        : unit =
      Log.todo_exn "ext output"

    (* Sanity check *)
    let sanity_check (mess: string) (x: t): unit =
      if flag_sanity_sshape then
        begin
          Dom_eqs.sanity_check mess x.t_eqs;
          DIC.sanity_check mess x.t_dic
        end

    (* Sve_fix: ensure consistency of underlying shape's symbolic
     * variables, dictionary and numerical equality components *)
    let sve_fix (x: t): t =
      sanity_check "dom_mem_low_sep, sve_fix" x;
      (* 0. bring up svenv modifications from shape values *)
      let x1, svm1 = D1.sve_sync_bot_up x.t_fst
      and x2, svm2 = D2.sve_sync_bot_up x.t_snd in
      (* 1. update equalities, remove some bindings *)
      let eqs = Aa_sets.fold (Dom_eqs.forget_a) svm1.svm_mod x.t_eqs in
      let eqs = Aa_sets.fold (Dom_eqs.forget_b) svm2.svm_mod eqs in
      let eqs = Aa_sets.fold (Dom_eqs.forget_a) svm1.svm_rem eqs in
      let eqs = Aa_sets.fold (Dom_eqs.forget_b) svm2.svm_rem eqs in
      (* 2. add added symb. vars in the dictionary *)
      let dic =
        Aa_maps.fold
          (fun i1 _ senv -> snd (DIC.add_fresh (Dic_fst, i1) senv))
          svm1.svm_add x.t_dic in
      let dic =
        Aa_maps.fold
          (fun i2 _ senv -> snd (DIC.add_fresh (Dic_snd, i2) senv))
          svm2.svm_add dic in
      (* 3. create the local env modifications *)
      let svm_from1 = svenv_map (DIC.fst2local dic) svm1
      and svm_from2 = svenv_map (DIC.snd2local dic) svm2 in
      let svm = svenv_join svm_from1 svm_from2 in
      (* 4. remove removed symb. vars in local environment *)
      let dic = Aa_sets.fold DIC.rem svm.svm_rem dic in
      (* 5. return the new abstract value *)
      { t_dic    = dic;
        t_fst    = x1;
        t_snd    = x2;
        t_eqs    = eqs;
        t_envmod = svenv_join x.t_envmod svm; }

    (** Tools for converting symbolic variables, expressions and conditions
     ** from separating product into underlying shapes symbolic variables *)

    (* convert from sep to D1 *)
    let sv_convert_local2fst (x: t) (i: int): int option =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 -> Some i1
      | Dic_snd, i2 -> Dom_eqs.find_eq_b i2 x.t_eqs

    (* convert from sep to D2 *)
    let sv_convert_local2snd (x: t) (i: int): int option =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 -> Dom_eqs.find_eq_a i1 x.t_eqs
      | Dic_snd, i2 -> Some i2

    (* convert a sv in SEP to a expression in D1 *)
    let sv2nexpr1 (x: t) (i: int): n_expr =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 -> Ne_var i1
      | Dic_snd, i2 ->
          match Dom_eqs.find_eq_b i2 x.t_eqs with
          | Some i1 -> Ne_var i1
          | None -> (* check wether it is null *)
              if D2.sat (Nc_cons (Apron.Tcons1.EQ, Ne_var i2, Ne_csti 0)) x.t_snd
              then Ne_csti 0 else Ne_rand

    (* convert a sv in SEP to a expression in D2 *)
    let sv2nexpr2 (x: t) (i: int): n_expr =
      match DIC.local2under x.t_dic i with
      | Dic_snd, i2 -> Ne_var i2
      | Dic_fst, i1 ->
          match Dom_eqs.find_eq_a i1 x.t_eqs with
          | Some i2 -> Ne_var i2
          | None ->
              if D1.sat (Nc_cons (Apron.Tcons1.EQ, Ne_var i1, Ne_csti 0)) x.t_fst
              then Ne_csti 0 else Ne_rand

    (* convert from D1 to D2, eventually create a new symbolic variable in D2 *)
    let sv_convert_fst2snd (x: t) (i1: int): t * int =
      match Dom_eqs.find_eq_a i1 x.t_eqs with
      | Some i2 -> x, i2
      | None    -> (* create a new sv in D2 *)
          (* 1. recover info about i1 in D1 *)
          let op_na, op_nt = D1.sv_get_info i1 x.t_fst in
          let na =
            match op_na with
            | Some na -> na
            | None    ->
                Log.fatal_exn "sv_convert_fst2snd: can't recover nalloc" in
          let nt =
            match op_nt with
            | Some nt -> nt
            | None    ->
                Log.fatal_exn "sv_convert_fst2snd: can't recover ntyp" in
          (* 2. create new sv in D2 *)
          let i2, x2 = D2.sv_add_fresh nt na x.t_snd in
          (* 3. fix environement, for sv environment consistency *)
          let x = sve_fix { x with t_snd = x2 } in
          (* 4. write equality *)
          { x with t_eqs = Dom_eqs.write_eq i1 i2 x.t_eqs }, i2

    (* convert from D2 to D1, eventually create a new symbolic variable in D1 *)
    let sv_convert_snd2fst (x: t) (i2: int): t * int =
      match Dom_eqs.find_eq_b i2 x.t_eqs with
      | Some i1 -> x, i1
      | None    -> (* create a new sv in D1 *)
          (* 1. recover info about i2 in D2 *)
          let op_na, op_nt = D2.sv_get_info i2 x.t_snd in
          let na =
            match op_na with
            | Some na -> na
            | None    ->
                Log.fatal_exn "sv_convert_snd2fst: can't recover nalloc" in
          let nt =
            match op_nt with
            | Some nt -> nt
            | None    ->
                Log.fatal_exn "sv_convert_snd2fst: can't recover ntyp" in
          (* 2. create new sv in D1 *)
          let i1, x1 = D1.sv_add_fresh nt na x.t_fst in
          (* 3. fix environement, for sv environment consistency *)
          let x = sve_fix { x with t_fst = x1 } in
          (* 4. write equality *)
          { x with t_eqs = Dom_eqs.write_eq i1 i2 x.t_eqs }, i1

    (* convert numerical expression from sep to D1 *)
    let n_expr_local2fst (x: t) (ne: n_expr): n_expr =
      let f i =
        match sv2nexpr1 x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_expr_subst f ne with Stop -> Ne_rand

    (* convert numerical expression from sep to D2 *)
    let n_expr_local2snd (x: t) (ne: n_expr): n_expr =
      let f i =
        match sv2nexpr2 x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_expr_subst f ne with Stop -> Ne_rand

    (* convert numerical condition from sep to D1 *)
    let n_cons_local2fst (x: t) (nc: n_cons): n_cons =
      let f i =
        match sv2nexpr1 x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_cons_subst f nc with Stop -> Nc_rand

    (* convert numerical condition from sep to D2 *)
    let n_cons_local2snd (x: t) (nc: n_cons): n_cons =
      let f i =
        match sv2nexpr2 x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_cons_subst f nc with Stop -> Nc_rand

    (** Management of symbolic variables *)

    (* Will that symb. var. creation be allowed by the domain? *)
    let sv_is_allowed ?(attr: node_attribute = Attr_none) (nt: ntyp)
        (na: nalloc) (x: t): bool =
      D1.sv_is_allowed ~attr: attr nt na x.t_fst ||
      D2.sv_is_allowed ~attr: attr nt na x.t_snd

    (* Add a node, with a newly generated id *)
    let sv_add_fresh ?(attr: node_attribute = Attr_none) ?(root: bool = false)
        (nt: ntyp) (na: nalloc) (x: t): int * t =
      (* 0. determine in which component
       *    the fresh symbolic variable will be created *)
      let loc =
        if D1.sv_is_allowed ~attr:attr nt na x.t_fst then Dic_fst
        else Dic_snd in
      if true then (* TODO: add a flag, or reuse one? *)
        Log.info "Dom_mem_low_sep.sv_add_fresh %s %s %s: %s"
          (Graph_utils.node_attribute_2str attr)
          (Ind_utils.ntyp_2str nt)
          (Graph_utils.nalloc_2str na)
          (dic_side_2str loc);
      match loc with
      | Dic_fst ->
          (* 1.1 create fresh symb.variable in the first component *)
          let i1, x1 = D1.sv_add_fresh ~attr:attr ~root:root nt na x.t_fst in
          (* 1.2 fix env to ensure environment consistency *)
          let x = sve_fix { x with t_fst = x1 } in
          (* 1.3 returns the fresh symbolic variable *)
          DIC.fst2local x.t_dic i1, x
      | Dic_snd ->
          (* 1.1 create fresh symb.variable in the second component *)
          let i2, x2 = D2.sv_add_fresh ~attr:attr ~root:root nt na x.t_snd in
          (* 1.2 fix env to ensure environment consistency *)
          let x = sve_fix { x with t_snd = x2 } in
          (* 1.3 returns the fresh symbolic variable *)
          DIC.snd2local x.t_dic i2, x

    (* Recover information about a symbolic variable *)
    let sv_get_info (i: int) (x: t): nalloc option * ntyp option =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 -> D1.sv_get_info i1 x.t_fst
      | Dic_snd, i2 -> D2.sv_get_info i2 x.t_snd

    (** Management of the memory: add/destroy cells *)

    (* Garbage collection *)
    (* AT: consider doing a fixpoint here? it'd be costly but more precise *)
    let gc (roots: int uni_table) (x: t): t =
      (* 1. compute roots for underlying shapes *)
      let roots1, roots2 =
        Aa_sets.fold
          (fun r (s1, s2) ->
            match DIC.local2under x.t_dic r with
            | Dic_fst, r1 -> Aa_sets.add r1 s1, s2
            | Dic_snd, r2 -> s1, Aa_sets.add r2 s2
           ) roots (Aa_sets.empty, Aa_sets.empty) in
      (* 2. do gc on first shape component *)
      let x = sve_fix { x with
                        t_fst = D1.gc roots1 x.t_fst } in
      (* 3. increase set of roots2 and do gc on second shape component *)
      let roots2 =
        Dom_eqs.fold
          (fun _ l2 r2 ->
            (* symvars that appear in right side of an equality
             *  are reachable hence added in roots2 *)
            List.fold_left (fun r2 i2 -> Aa_sets.add i2 r2) r2 l2
          ) x.t_eqs roots2 in
      sve_fix { x with
                t_snd = D2.gc roots2 x.t_snd }


    (** Graph encoding (used for guiding join) *)
    let encode (disj: int) (n: namer) (x: t) =
      Log.todo_exn "encode"


    (** Comparison and Join operators *)

    (* Hints translators *)
    let opt_hint_us_local2under (x: t): int hint_us option ->
      int hint_us option * int hint_us option = function
        | None -> None, None
        | Some hu ->
            let l1, l2 =
              Aa_sets.fold
                (fun i (l1, l2) ->
                  match DIC.local2under x.t_dic i with
                  | (Dic_fst, i1) -> Aa_sets.add i1 l1, l2
                  | (Dic_snd, i2) -> l1, Aa_sets.add i2 l2
                ) hu.hus_live (Aa_sets.empty, Aa_sets.empty) in
            Some { hus_live = l1 }, Some { hus_live = l2 }
    let opt_hint_bs_local2under (xl: t) (xr: t): int hint_bs option ->
      int hint_bs option * int hint_bs option = function
        | None -> None, None
        | Some hb ->
            let t1, t2 =
              Aa_maps.fold
                (fun ir il (t1, t2) ->
                  match DIC.local2under xl.t_dic il, DIC.local2under xr.t_dic ir with
                  | (Dic_fst, il1), (Dic_fst, ir1) -> Aa_maps.add ir1 il1 t1, t2
                  | (Dic_snd, il2), (Dic_snd, ir2) -> t1, Aa_maps.add ir2 il2 t2
                  | _ -> t1, t2 (* TODO: try to do sthg with t_eqs *)
                ) hb.hbs_live (Aa_maps.empty, Aa_maps.empty) in
            Some { hbs_live = t1 }, Some { hbs_live = t2 }

    (* Roots translators *)
    let bin_table_local2under (xl: t) (xr: t)
        (roots: int bin_table): int bin_table * int bin_table =
      Aa_maps.fold
        (fun ir il (r1, r2) ->
          match DIC.local2under xl.t_dic il, DIC.local2under xr.t_dic ir with
          | (Dic_fst, il1), (Dic_fst, ir1) ->
              Aa_maps.add ir1 il1 r1, r2
          | (Dic_snd, il2), (Dic_snd, ir2) ->
              r1, Aa_maps.add ir2 il2 r2
          | _ -> r1, r2
        ) roots (Aa_maps.empty , Aa_maps.empty)
    let tri_table_local2under (xl: t) (xr: t)
        (roots: int tri_table): int tri_table * int tri_table =
      Aa_sets.fold
        (fun (il, ir, io) (r1, r2) ->
          match
            DIC.local2under xl.t_dic il,
            DIC.local2under xr.t_dic ir,
            DIC.local2under xl.t_dic io with
          | (Dic_fst, il1), (Dic_fst, ir1), (Dic_fst, io1) ->
              Aa_sets.add (il1, ir1, io1) r1, r2
          | (Dic_snd, il2), (Dic_snd, ir2), (Dic_snd, io2) ->
              r1, Aa_sets.add (il2, ir2, io2) r2
          | _ -> r1, r2
        ) roots (Aa_sets.empty , Aa_sets.empty)

    (* Compose svenv_upd *)
    let svenv_upd_under2local
        (senvl: DIC.t) (senvr: DIC.t)
        (svu1: svenv_upd) (svu2: svenv_upd): svenv_upd =
      let sv_upd_map f = function
        | Svu_mod (i, s) ->
            let sf = IntSet.fold (fun i -> IntSet.add (f i)) s IntSet.empty in
            Svu_mod (f i, sf)
        | Svu_rem -> Svu_rem in
      fun il ->
        match DIC.local2under senvl il with
        | Dic_fst, il1 -> sv_upd_map (DIC.fst2local senvr) (svu1 il1)
        | Dic_snd, il2 -> sv_upd_map (DIC.snd2local senvr) (svu2 il2)

    (* Checks if the left argument is included in the right one *)
    let is_le
        (roots: int bin_table) (setroots: int bin_table)
        (xl: t) (xr: t): svenv_upd option =
      (* 0. distribute arguments *)
      let roots1, roots2 = bin_table_local2under xl xr roots in
      (* 1. check is_le on D1 *)
      match D1.is_le roots1 setroots xl.t_fst xr.t_fst with
      | None -> None
      | Some svu1 ->
          (* 2. augment roots2 *)
          let roots2 =
            Dom_eqs.fold
              (fun lst1l lst2l roots2 ->
                List.fold_left
                  (fun roots2 i1l ->
                    let set1r = sv_upd_2set (svu1 i1l) in
                    IntSet.fold
                      (fun i1r roots2 ->
                        match Dom_eqs.find_eq_a i1r xr.t_eqs with
                        | None -> roots2
                        | Some i2r -> Aa_maps.add i2r (List.hd lst2l) roots2
                      ) set1r roots2
                  ) roots2 lst1l
              ) xl.t_eqs roots2 in
          match D2.is_le roots2 setroots xl.t_snd xr.t_snd with
          | None -> None
          | Some svu2 ->
              let svu = svenv_upd_under2local xl.t_dic xr.t_dic svu1 svu2 in
              Some svu

    (* Generic comparison (does both join and widening) *)
    let join
        (jk: join_kind)
        (hbo: int hint_bs option)
        (lbo: (onode lint_bs) option)
        (roots: int tri_table) (setroots: int tri_table)
        ((xl, jl): t * join_ele) ((xr, jr): t * join_ele)
        : t * svenv_upd * svenv_upd =
      assert(svenv_is_empty xl.t_envmod);
      assert(svenv_is_empty xr.t_envmod);
      (* 0. distribute arguments *)
      let hbo1, hbo2 = opt_hint_bs_local2under xl xr hbo in
      let roots1, roots2 = tri_table_local2under xl xr roots in
      (* 1. join in D1 *)
      let xo1, svu1l, svu1r =
        D1.join jk hbo1 None roots1 setroots (xl.t_fst, jl) (xr.t_fst, jr) in
      (* 2. compute the join equalities and augment roots2 *)
      let eqs, roots2 =
        let ll =
          Dom_eqs.fold
            (fun lst1l lst2l l ->
              let set1o =
                List.fold_left
                  (fun s i1l -> IntSet.union s (sv_upd_2set (svu1l i1l)))
                  IntSet.empty lst1l in
              (set1o, List.hd lst2l)::l
            ) xl.t_eqs []
        and lr =
          Dom_eqs.fold
            (fun lst1r lst2r l ->
              let set1o =
                List.fold_left
                  (fun s i1r -> IntSet.union s (sv_upd_2set (svu1r i1r)))
                  IntSet.empty lst1r in
              (set1o, List.hd lst2r)::l
            ) xr.t_eqs [] in
        List.fold_left
          (fun (eqs, roots2) (set1_froml, rep2l) ->
            List.fold_left
              (fun (eqs, roots2) (set1_fromr, rep2r) ->
                let set1 = IntSet.inter set1_froml set1_fromr in
                try
                  let i1 = IntSet.choose set1 in
                  (* like in table roots_compute in Dom_env module *)
                  let i2 = rep2l in
                  (* L, R, O *)
                  let roots2 = Aa_sets.add (rep2l, rep2r, i2) roots2
                  and eqs = Dom_eqs.write_eq i1 i2 eqs in
                  eqs, roots2
                with Not_found -> eqs, roots2
              ) (eqs, roots2) lr
          ) (Dom_eqs.empty, roots2) ll in
      (* 3. join in D2 *)
      let xo2, svu2l, svu2r =
        D2.join jk hbo2  None roots2 setroots (xl.t_snd, jl) (xr.t_snd, jr) in
      (* 4. compute the join sep environement *)
      (* TODO: fix this (issue with roots preservation) *)
      let senv =
        DIC.fold
          (fun _ und_i senv ->
            match und_i with
            | Dic_fst, i1 ->
                let set_i1 = sv_upd_2set (svu1l i1) in
                IntSet.fold
                  (fun i1 senv ->
                    let _, senv = DIC.add_fresh (Dic_fst, i1) senv in senv
                  ) set_i1 senv
            | Dic_snd, i2 ->
                let set_i2 = sv_upd_2set (svu2l i2) in
                IntSet.fold
                  (fun i2 senv ->
                    let _, senv = DIC.add_fresh (Dic_snd, i2) senv in senv
                  ) set_i2 senv
          ) xl.t_dic DIC.empty in
      let x = { t_dic = senv;
                t_fst = xo1;
                t_snd = xo2;
                t_eqs = eqs;
                t_envmod = svenv_empty } in
      let svul = svenv_upd_under2local xl.t_dic x.t_dic svu1l svu2l
      and svur = svenv_upd_under2local xr.t_dic x.t_dic svu1r svu2r in
      x, svul, svur

    (* Directed weakening; over-approximates only the right element *)
    (* TODO: augment roots *)
    let directed_weakening
        (hbo: int hint_bs option)
        (roots: int tri_table) (setroots: int tri_table)
        (xl: t) (xr: t): t * svenv_upd =
      assert(svenv_is_empty xl.t_envmod);
      (* 0. distribute arguments *)
      let hbo1, hbo2 = opt_hint_bs_local2under xl xr hbo in
      let roots1, roots2 = tri_table_local2under xl xr roots in
      (* 1. dir. weakening in D1 and D2 *)
      let xo1, svu1 =
        D1.directed_weakening hbo1 roots1 setroots xl.t_fst xr.t_fst
      and xo2, svu2 =
        D2.directed_weakening hbo2 roots2 setroots xl.t_snd xr.t_snd in
      (* 2. compute the equalities *)
      let eqs = Log.todo_exn "eqs" in
      (* 3. compute the sep env *)
      let senv =
        DIC.fold
          (fun _ und_i senv ->
            match und_i with
            | Dic_fst, i1 ->
                let set_i1 = sv_upd_2set (svu1 i1) in
                IntSet.fold
                  (fun i1 senv ->
                    let _, senv = DIC.add_fresh (Dic_fst, i1) senv in senv
                  ) set_i1 senv
            | Dic_snd, i2 ->
                let set_i2 = sv_upd_2set (svu2 i2) in
                IntSet.fold
                  (fun i2 senv ->
                    let _, senv = DIC.add_fresh (Dic_snd, i2) senv in senv
                  ) set_i2 senv
          ) xl.t_dic DIC.empty in
      let x = { t_dic = senv;
                t_fst = xo1;
                t_snd = xo2;
                t_eqs = eqs;
                t_envmod = svenv_empty } in
      let svu = svenv_upd_under2local xl.t_dic x.t_dic svu1 svu2 in
      x, svu

    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    let local_abstract (huo: int hint_us option) (x: t): t =
      let huo1, huo2 = opt_hint_us_local2under x huo in
      sve_fix { x with
                t_fst = D1.local_abstract huo1 x.t_fst;
                t_snd = D2.local_abstract huo2 x.t_snd }

    (** Cell operations *)

    (* Addition of a cell *)
    let cell_create ?(attr:node_attribute = Attr_none)
        ((src, off): onode) (sz: Offs.size) (nt: ntyp) (x: t): t =
      match DIC.local2under x.t_dic src with
      | Dic_fst, src1 ->
          sve_fix { x with
                    t_fst = D1.cell_create (src1, off) sz nt x.t_fst }
      | Dic_snd, src2 ->
          sve_fix { x with
                    t_snd = D2.cell_create (src2, off) sz nt x.t_snd }

    (* Remove a cell *)
    let cell_delete ?(free: bool = true) ?(root:bool = false)
        (i: int) (x: t): t =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 ->
          sve_fix { x with
                    t_fst = D1.cell_delete ~free:free ~root:root i1 x.t_fst }
      | Dic_snd, i2 ->
          sve_fix { x with
                    t_snd = D2.cell_delete ~free:free ~root:root i2 x.t_snd }


    (* Read *)
    let cell_read (is_resolve: bool) ((i, off): onode) (sz: int) (x: t)
        : (t * onode * onode option) list =
      let onode_fst2local x (i1, off) = DIC.fst2local x.t_dic i1, off
      and onode_snd2local x (i2, off) = DIC.snd2local x.t_dic i2, off in
      let rec cell_read_aux
          (count: int)
          (acc_done: (t * onode * onode option) list) (* already treated *)
          : (t
             * dic_side (* where the cell need to be read *)
             * onode    (* the address of the cell *)
             * bool     (* whether cell has already unsuccessfully read *)
            ) list      (* acc todo *)
        -> (t * onode * onode option) list = function
          | [] -> acc_done
          | (x, Dic_fst, (i1, off), b)::acc_todo ->
              (* 0. if countdown is over, stop the resolution *)
              if count = 0 then
                Log.fatal_exn "reached the maximal number of cell_read!";
              (* 1. call cell read in D1 *)
              let l1 = D1.cell_read false (i1, off) sz x.t_fst in
              (* 2. move successful reading in acc_done and
               *    unsuccessful to acc_todo in D2 *)
              let acc_done, acc_todo =
                match b, l1 with
                | true, [ x1, (i1, off), op_cont1 ] ->
                    (* reading was attempted in D1 and D2
                     * => put the result whatever it is in acc_done *)
                    let x = sve_fix { x with t_fst = x1 } in
                    let addr = onode_fst2local x (i1, off)
                    and op_cont = Option.map (onode_fst2local x) op_cont1 in
                    (x, addr, op_cont)::acc_done, acc_todo
                | _ ->
                    List.fold_left
                      (fun (acc_done, acc_todo) (x1, (i1, off), op_cont1) ->
                        let x = sve_fix { x with t_fst = x1 } in
                        match op_cont1 with
                        | Some cont1 -> (* success in D1 *)
                            let addr = onode_fst2local x (i1, off)
                            and cont = onode_fst2local x cont1 in
                            (x, addr, Some cont)::acc_done, acc_todo
                        | None -> (* failure in D1 *)
                            match Dom_eqs.find_eq_a i1 x.t_eqs with
                            | Some i2 -> (* continue in D2 *)
                                acc_done, (x, Dic_snd, (i2, off), true)::acc_todo
                            | None -> (* KO in D1 *)
                                let addr = onode_fst2local x (i1, off) in
                                (x, addr, None)::acc_done, acc_todo
                      ) (acc_done, acc_todo) l1 in
              (* 3. reccursive call *)
              cell_read_aux (count - 1) acc_done acc_todo
          | (x, Dic_snd, (i2, off), b)::acc_todo ->
              (* 0. if countdown is over, stop the resolution *)
              if count = 0 then
                Log.fatal_exn "reached the maximal number of cell_read!";
              (* 1. call cell read in D2 *)
              let l2 = D2.cell_read false (i2, off) sz x.t_snd in
              (* 2. move successful reading in acc_done and
               *    unsuccessful to acc_todo in D2 *)
              let acc_done, acc_todo =
                match b, l2 with
                | true, [ x2, (i2, off), op_cont2 ] ->
                    (* reading was attempted in D1 and D2
                     * => put the result whatever it is in acc_done *)
                    let x = sve_fix { x with t_snd = x2 } in
                    let addr = onode_snd2local x (i2, off)
                    and op_cont = Option.map (onode_snd2local x) op_cont2 in
                    (x, addr, op_cont)::acc_done, acc_todo
                | _ ->
                    List.fold_left
                      (fun (acc_done, acc_todo) (x2, (i2, off), op_cont2) ->
                        let x = sve_fix { x with t_snd = x2 } in
                        match op_cont2 with
                        | Some cont2 -> (* success in D2 *)
                            let addr = onode_snd2local x (i2, off)
                            and cont = onode_snd2local x cont2 in
                            (x, addr, Some cont)::acc_done, acc_todo
                        | None -> (* failure in D2 *)
                            match Dom_eqs.find_eq_b i2 x.t_eqs with
                            | Some i1 -> (* continue in D1 *)
                                acc_done, (x, Dic_fst, (i1, off), true)::acc_todo
                            | None -> (* KO in D2 *)
                                let addr = onode_snd2local x (i2, off) in
                                (x, addr, None)::acc_done, acc_todo
                      ) (acc_done, acc_todo) l2 in
              (* 3. reccursive call *)
              cell_read_aux (count - 1) acc_done acc_todo in
      let acc_todo =
        match DIC.local2under x.t_dic i with
        | Dic_fst, i1 -> [ x, Dic_fst, (i1, off), false ]
        | Dic_snd, i2 -> [ x, Dic_snd, (i2, off), false ] in
      cell_read_aux Flags.max_cell_read [] acc_todo

    (* Resolve a cell *)
    let cell_resolve ((i, off): onode) (size: int) (x: t)
        : (t * onode * bool) list =
      (* function to translate resolution the sep level *)
      let cr_fst2local x (x1, (i1, off), b) =
        let x_post = sve_fix { x with t_fst = x1 } in
        let i = DIC.fst2local x_post.t_dic i1 in
        x_post, (i, off), b
      and cr_snd2local x (x2, (i2, off), b) =
        let x_post = sve_fix { x with t_snd = x2 } in
        let i = DIC.snd2local x_post.t_dic i2 in
        x_post, (i, off), b in
      let rec cell_resolve_aux
          (count: int)
          (acc_done: (t * onode * bool) list) (* already treated *)
          : (t
             * dic_side (* where resolution need to be done *)
             * onode    (* the address of the cell *)
             * bool     (* whether resolution has been attempted already *)
            ) list      (* acc todo *)
        -> (t * onode * bool) list = function
          | [] -> acc_done
          | (x, Dic_fst, (i1, off), b)::acc_todo ->
              (* 0. if countdown is over, stop the resolution *)
              if count = 0 then
                Log.fatal_exn "reached the maximal number of cell_resolve!";
              (* 1. call cell resolve in D1 *)
              let l1 = D1.cell_resolve (i1, off) size x.t_fst in
              (* 2. move successful resolution in acc_done and
               *    unsuccessful to acc_todo in D2 *)
              let acc_done, acc_todo =
                match b, l1 with
                | true, [ x1, addr1, is_res ] ->
                    (* resolution was attempted in D1 and D2
                     * => put the result whatever it is in acc_done *)
                    let res = cr_fst2local x (x1, addr1, is_res) in
                    res::acc_done, acc_todo
                | _ ->
                    List.fold_left
                      (fun (acc_done, acc_todo) (x1, addr1, is_res) ->
                        let x = sve_fix { x with t_fst = x1 } in
                        if is_res then (* successful in D1 *)
                          let i = DIC.fst2local x.t_dic (fst addr1) in
                          let addr = i, snd addr1 in
                          (x, addr, true)::acc_done, acc_todo
                        else (* try to continue resolution in D2 *)
                          match Dom_eqs.find_eq_a (fst addr1) x.t_eqs with
                          | Some i2 ->
                              let addr2 = i2, snd addr1 in
                              acc_done, (x, Dic_snd, addr2, true)::acc_todo
                          | None ->
                              let i = DIC.fst2local x.t_dic (fst addr1) in
                              let addr = i, snd addr1 in
                              (x, addr, false)::acc_done, acc_todo
                      ) (acc_done, acc_todo) l1 in
              (* 3. reccursive call *)
              cell_resolve_aux (count - 1) acc_done acc_todo
          | (x, Dic_snd, (i2, off), b)::acc_todo ->
              (* 0. if countdown is over, stop the resolution *)
              if count = 0 then
                Log.fatal_exn "reached the maximal number of cell_resolve!";
              (* 1. call cell resolve in D1 *)
              let l2 = D2.cell_resolve (i2, off) size x.t_snd in
              (* 2. move successful resolution in acc_done and
               *    unsuccessful to acc_todo in D2 *)
              let acc_done, acc_todo =
                match b, l2 with
                | true, [ x2, addr2, is_res ] ->
                    (* resolution was attempted in D1 and D2
                     * => put the result whatever it is in acc_done *)
                    let res = cr_snd2local x (x2, addr2, is_res) in
                    res::acc_done, acc_todo
                | _ ->
                    List.fold_left
                      (fun (acc_done, acc_todo) (x2, addr2, is_res) ->
                        let x = sve_fix { x with t_snd = x2 } in
                        if is_res then (* successful in D2 *)
                          let i = DIC.snd2local x.t_dic (fst addr2) in
                          let addr = i, snd addr2 in
                          (x, addr, true)::acc_done, acc_todo
                        else (* try to continue resolution in D2 *)
                          match Dom_eqs.find_eq_b (fst addr2) x.t_eqs with
                          | Some i1 ->
                              let addr1 = i1, snd addr2 in
                              acc_done, (x, Dic_fst, addr1, true)::acc_todo
                          | None ->
                              let i = DIC.snd2local x.t_dic (fst addr2) in
                              let addr = i, snd addr2 in
                              (x, addr, false)::acc_done, acc_todo
                      ) (acc_done, acc_todo) l2 in
              (* 3. reccursive call *)
              cell_resolve_aux (count - 1) acc_done acc_todo in
      let acc_todo =
        match DIC.local2under x.t_dic i with
        | Dic_fst, i1 -> [ x, Dic_fst, (i1, off), false ]
        | Dic_snd, i2 -> [ x, Dic_snd, (i2, off), false ] in
      cell_resolve_aux Flags.max_cell_resolve [] acc_todo

    (* Write *)
    let cell_write
        (nt: ntyp)
        ((idst, odst) as dst: onode)
        (sz: int) (ne: n_expr) (x: t): t =
      if !flag_debug_assign then
        Log.force
          "separating_cell_write:\n - dst: %s\n - expr: %s\n - x:\n%s"
          (Graph_utils.onode_2str dst)
          (Nd_utils.n_expr_2str ne)
          (t_2stri "\t" x);
      match DIC.local2under x.t_dic idst with
      | Dic_fst, idst1 -> (* cell is materialized in D1 *)
          let ne1 = n_expr_local2fst x ne in
          let dst1 = idst1, odst in
          if !flag_debug_assign then
            Log.force "separating_cell_write: assignment in D1";
          let x1 = D1.cell_write nt dst1 sz ne1 x.t_fst in
          let x = sve_fix { x with t_fst = x1 } in
          let x = match ne with
          | Ne_var i_ne ->
              (* refinement: some equality may be written in t_eqs *)
              let x = match D1.cell_read false dst1 sz x.t_fst with
              | [ x1, addr1, Some (icont1, ocont1) ] ->
                  assert( addr1 = dst1 );
                  if Offs.is_zero ocont1 then
                    match DIC.local2under x.t_dic i_ne with
                    | Dic_fst, i_ne1 ->
                        if !flag_debug_assign then
                          begin
                            Log.force
                              "separating_cell_write: assignment in eqs";
                            Log.force "\t%i (D1) == %i (D1)" icont1 i_ne1;
                          end;
                        let x = match Dom_eqs.find_eq_a i_ne1 x.t_eqs with
                        | Some i2 ->
                            { x with
                              t_eqs = Dom_eqs.write_eq icont1 i2 x.t_eqs }
                        | None -> x in x
                    | Dic_snd, i_ne2 ->
                        if !flag_debug_assign then
                          begin
                            Log.force
                              "separating_cell_write: assignment in eqs";
                            Log.force "\t%i (D1) == %i (D2)" icont1 i_ne2;
                          end;
                        { x with
                          t_eqs = Dom_eqs.write_eq icont1 i_ne2 x.t_eqs }
                  else (* can not write it in eqs *) x
              | _ ->
                  (* if read produce more than one abstract values, give up *)
                  x in x
          | _ -> x in x
      | Dic_snd, idst2 -> (* cell is materialized in D2 *)
          let ne2 = n_expr_local2snd x ne in
          let dst2 = idst2, odst in
          if !flag_debug_assign then
            Log.force "separating_cell_write: assignment in D2";
          let x2 = D2.cell_write nt dst2 sz ne2 x.t_snd in
          let x = sve_fix { x with t_snd = x2 } in
          let x = match ne with
          | Ne_var i_ne ->
              (* refinement: some equality may be written in t_eqs *)
              let x = match D2.cell_read false dst2 sz x.t_snd with
              | [ x2, addr2, Some (icont2, ocont2) ] ->
                  assert( addr2 = dst2 );
                  if Offs.is_zero ocont2 then
                    match DIC.local2under x.t_dic i_ne with
                    | Dic_fst, i_ne1 ->
                        if !flag_debug_assign then
                          begin
                            Log.force
                              "separating_cell_write: assignment in eqs";
                            Log.force "\t%i (D2) == %i (D1)" icont2 i_ne1
                          end;
                        { x with
                          t_eqs = Dom_eqs.write_eq i_ne1 icont2 x.t_eqs }
                    | Dic_snd, i_ne2 ->
                        if !flag_debug_assign then
                          begin
                            Log.force
                              "separating_cell_write: assignment in eqs";
                            Log.force "\t%i (D2) == %i (D2)" icont2 i_ne2;
                          end;
                        let x = match Dom_eqs.find_eq_b i_ne2 x.t_eqs with
                        | Some i1 ->
                            { x with
                              t_eqs = Dom_eqs.write_eq i1 icont2 x.t_eqs }
                        | None -> x in x
                  else (* can not write it in eqs *) x
              | _ ->
                  (* if read produce more than one abstract values, give up *)
                  x in x
          | _ -> x in x

    (** Transfer functions for the analysis *)

    (* Condition test *)
    let guard (nc: n_cons) (x: t): t =
      (* 1. do guard in eqs if applicable *)
      let eqs = match nc with
      | Nc_cons (Apron.Tcons1.EQ, Ne_var i, Ne_var j) ->
          begin
            match DIC.local2under x.t_dic i, DIC.local2under x.t_dic j with
            | (Dic_fst, i1), (Dic_snd, i2)
            | (Dic_snd, i2), (Dic_fst, i1) -> Dom_eqs.write_eq i1 i2 x.t_eqs
            | (Dic_fst, i1), (Dic_fst, j1) ->
                let eqs = match Dom_eqs.find_eq_a i1 x.t_eqs with
                | Some i2 -> Dom_eqs.write_eq j1 i2 x.t_eqs
                | None ->
                    let eqs = match Dom_eqs.find_eq_a j1 x.t_eqs with
                    | Some j2 -> Dom_eqs.write_eq i1 j2 x.t_eqs
                    |  _ -> x.t_eqs in eqs in eqs
            | (Dic_snd, i2), (Dic_snd, j2) ->
                let eqs = match Dom_eqs.find_eq_b i2 x.t_eqs with
                | Some i1 -> Dom_eqs.write_eq i1 j2 x.t_eqs
                | None ->
                    let eqs = match Dom_eqs.find_eq_b j2 x.t_eqs with
                    | Some j1 -> Dom_eqs.write_eq j1 i2 x.t_eqs
                    |  _ -> x.t_eqs in eqs in eqs
          end
      | _ -> x.t_eqs in
      (* 2. do guard in shape component *)
      let nc1 = n_cons_local2fst x nc
      and nc2 = n_cons_local2snd x nc in
      let x1 = if nc1 = Nc_rand then x.t_fst else D1.guard nc1 x.t_fst
      and x2 = if nc2 = Nc_rand then x.t_snd else D2.guard nc2 x.t_snd in
      (* 3. return abstract value *)
      sve_fix { x with
                t_fst = x1;
                t_snd = x2;
                t_eqs = eqs; }

    (* Checking that a constraint is satisfied; returns over-approx sat *)
    let sat (nc: n_cons) (x: t): bool =
      (* check on eqs component *)
      let sat_eq () =
        match nc with
        | Nc_cons(Apron.Tcons1.EQ, Ne_var i, Ne_var j) ->
            begin
              match DIC.local2under x.t_dic i, DIC.local2under x.t_dic j with
              | (Dic_fst, i1), (Dic_snd, i2)
              | (Dic_snd, i2), (Dic_fst, i1) -> Dom_eqs.are_eq i1 i2 x.t_eqs
              | _ -> false
            end
        | _ -> false in
      (* check on underlying shape component and then on eqs *)
      ( D1.sat (n_cons_local2fst x nc) x.t_fst ) ||
      ( D2.sat (n_cons_local2snd x nc) x.t_snd ) ||
      ( sat_eq () )


    (** Set domain *)
    let setv_add_fresh _ = Log.todo_exn "setv_add_fresh"
    let setv_delete _ = Log.todo_exn "setv_delete"
    let set_sat _ = Log.todo_exn "set_sat"


    (** Unfolding, assuming and checking inductive edges *)

    (* Unfold *)
    let ind_unfold (udir: unfold_dir) ((i, o): onode) (x: t): t list =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 ->
          let l1 = D1.ind_unfold udir (i1, o) x.t_fst in
          List.map (fun x1 -> sve_fix { x with t_fst = x1 }) l1
      | Dic_snd, i2 ->
          let l2 = D2.ind_unfold udir (i2, o) x.t_snd in
          List.map (fun x2 -> sve_fix { x with t_snd = x2 }) l2

    (* Assume construction *)
    (* Translate gen_ind_call *)
    let gen_ind_call_local2fst (x: t)
        (ic: onode gen_ind_call): onode gen_ind_call option =
      let f (i, o) =
        match sv_convert_local2fst x i with
        | Some i1 -> i1, o
        | None -> raise Stop in
      try Some (map_gen_ind_call f ic) with Stop -> None
    let gen_ind_call_local2snd (x: t)
        (ic: onode gen_ind_call): onode gen_ind_call option =
      let f (i, o) =
        match sv_convert_local2snd x i with
        | Some i2 -> i2, o
        | None -> raise Stop in
      try Some (map_gen_ind_call f ic) with Stop -> None


    let assume (op: meml_log_form) (x: t): t =
      match op with
      | SL_seg _ -> Log.todo_exn "assume Segment"
      | SL_array -> Log.fatal_exn "assume Array"
      | SL_set _ -> Log.todo_exn "assume Setprop"
      | SL_ind (ic, (i, off)) ->
        (* 1. decide which sub-domain *)
          match D1.inductive_is_allowed ic.ic_name,
            D2.inductive_is_allowed ic.ic_name with
          | true, _ -> (* D1 *)
              let x, i1 =
                match DIC.local2under x.t_dic i with
                | Dic_fst, i1 -> x, i1
                | Dic_snd, i2 -> sv_convert_snd2fst x i2 in
              let x =
                match gen_ind_call_local2fst x ic with
                | Some ic1 ->
                    let r =
                      D1.assume (SL_ind (ic1, (i1, off))) x.t_fst in
                    { x with t_fst = r }
                | None     -> Log.todo_exn "ind_assume (1)" in
              x
          | false, true -> (* D2 *)
              let x, i2 =
                match DIC.local2under x.t_dic i with
                | Dic_snd, i2 -> x, i2
                | Dic_fst, i1 -> sv_convert_fst2snd x i1 in
              let x =
                match gen_ind_call_local2snd x ic with
                | Some ic2 ->
                    let r =
                      D2.assume (SL_ind (ic2, (i2, off))) x.t_snd in
                    { x with t_snd = r }
                | None     -> Log.todo_exn "ind_assume (2)" in
              x
          | _ -> Log.fatal_exn "can not assume the ind"

    let check (op: meml_log_form) (x: t): bool =
      Log.todo_exn "seg_check"

    (* Check construction, that an inductive be there *)
    let ind_check
        (ic: onode gen_ind_call)
        ((i, off): onode) (x: t): bool =
      let do_ic1 i1 =
        D1.inductive_is_allowed ic.ic_name
          &&
        begin
          match gen_ind_call_local2fst x ic with
          | Some ic1 -> D1.check (SL_ind (ic1, (i1, off))) x.t_fst
          | None     -> false
        end
      and do_ic2 i2 =
        D2.inductive_is_allowed ic.ic_name
          &&
        begin
          match gen_ind_call_local2snd x ic with
          | Some ic2 -> D2.check (SL_ind (ic2, (i2, off))) x.t_snd
          | None     -> false
        end in
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 ->
          do_ic1 i1
        ||
          begin
            match Dom_eqs.find_eq_a i1 x.t_eqs with
            | Some i2 -> do_ic2 i2
            | _ -> false
          end
        ||
          begin
            Offs.is_zero off
              &&
            begin
              let ind = Ind_utils.ind_find ic.ic_name in
              let nc = Nc_cons (Apron.Tcons1.EQ, Ne_var i, Ne_csti 0) in
              ind.i_mt_rule && sat nc x
            end
          end
      | Dic_snd, i2 ->
          do_ic2 i2
        ||
          begin
            match Dom_eqs.find_eq_b i2 x.t_eqs with
            | Some i1 -> do_ic1 i1
            | _ -> false
          end
        ||
          begin
            Offs.is_zero off
              &&
            begin
              let ind = Ind_utils.ind_find ic.ic_name in
              let nc = Nc_cons (Apron.Tcons1.EQ, Ne_var i, Ne_csti 0) in
              ind.i_mt_rule && sat nc x
            end
          end

    (* Temporaries specific for array *)
    let array_check (x: t): bool =
      Log.fatal_exn "array check in dom_mem_low_sep"
  end: DOM_MEM_LOW)


(** The separating product functor instanciated with the chosen DIC module *)
module Dom_sep = Dom_sep_dic( Dic_hash )
(*module Dom_sep = Dom_sep_dic( Dic_map )*)
