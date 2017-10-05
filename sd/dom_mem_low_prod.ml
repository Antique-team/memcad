(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_mem_low_prod.ml
 **       Basis for a product of shape abstraction
 ** Xavier Rival, Antoine Toubhans, 2011/04/04 *)
open Data_structures
open Flags
open Lib

open Ast_sig
open Dom_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig
open Svenv_sig

open Ast_utils
open Dom_utils

open Dom_dictionary

module Log =
  Logger.Make(struct let section = "dm_lprod" and level = Log_level.DEBUG end)

(** The product domain *)
module Dom_prod_dic =
  functor (DIC: DIC) ->
    functor (D1: DOM_MEM_LOW) ->
      functor (D2: DOM_MEM_LOW) ->
  (struct
    (** Module name *)
    let module_name = Printf.sprintf "(%s X %s)" D1.module_name D2.module_name
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s -> %s\n%s -> %s\n%s%s%s"
        module_name DIC.module_name
        module_name D1.module_name
        module_name D2.module_name
        (DIC.config_2str ())
        (D1.config_2str ())
        (D2.config_2str ())

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
    let init_inductives _ _: _ =
      Log.fatal_exn "init_inductives should not be called"
    let inductive_is_allowed (s: string): bool =
      D1.inductive_is_allowed s || D2.inductive_is_allowed s

    (** Fixing sets of keys *)
    let sve_sync_bot_up (x: t): t * svenv_mod =
      { x with t_envmod = svenv_empty }, x.t_envmod
    let sanity_sv (_: IntSet.t) (x: t): bool =
      Log.todo "sanity_sv: unimp";
      true

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
      let str_name = Printf.sprintf "%sCARTESIAN PRODUCT %s\n" ind module_name
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
      if flag_sanity_pshape then
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

    (* convert onode from D1 (resp. D2) to onode in (D1 X D2) *)
    let onode_fst2local (x: t) ((i1, off): onode): onode =
      DIC.fst2local x.t_dic i1, off
    let onode_snd2local (x: t) ((i2, off): onode): onode =
      DIC.snd2local x.t_dic i2, off

    (* convert from (D1 X D2) to D1 and D2 *)
    let sv_local2under (x: t) (i: int): int option * int option =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 -> Some i1, Dom_eqs.find_eq_a i1 x.t_eqs
      | Dic_snd, i2 -> Dom_eqs.find_eq_b i2 x.t_eqs, Some i2

    (* convert a sv in (D1 X D2) to a expression in D1 (resp. D2) *)
    let sv_local2n_expr_fst (x: t) (i: int): n_expr =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 -> Ne_var i1
      | Dic_snd, i2 ->
          match Dom_eqs.find_eq_b i2 x.t_eqs with
          | Some i1 -> Ne_var i1
          | None -> (* check wether it is null *)
              if D2.sat (Nc_cons (Apron.Tcons1.EQ, Ne_var i2, Ne_csti 0))
                  x.t_snd then
                Ne_csti 0
              else Ne_rand
    let sv_local2n_expr_snd (x: t) (i: int): n_expr =
      match DIC.local2under x.t_dic i with
      | Dic_snd, i2 -> Ne_var i2
      | Dic_fst, i1 ->
          match Dom_eqs.find_eq_a i1 x.t_eqs with
          | Some i2 -> Ne_var i2
          | None ->
              if D1.sat (Nc_cons (Apron.Tcons1.EQ, Ne_var i1, Ne_csti 0))
                  x.t_fst then
                Ne_csti 0
              else Ne_rand

    (* convert numerical expression from (D1 X D2) to D1 (resp. D2) *)
    let n_expr_local2fst (x: t) (ne: n_expr): n_expr =
      let f i =
        match sv_local2n_expr_fst x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_expr_subst f ne with Stop -> Ne_rand
    let n_expr_local2snd (x: t) (ne: n_expr): n_expr =
      let f i =
        match sv_local2n_expr_snd x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_expr_subst f ne with Stop -> Ne_rand

    (* convert numerical condition from (D1 X D2) to D1 (resp. D2) *)
    let n_cons_local2fst (x: t) (nc: n_cons): n_cons =
      let f i =
        match sv_local2n_expr_fst x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_cons_subst f nc with Stop -> Nc_rand
    let n_cons_local2snd (x: t) (nc: n_cons): n_cons =
      let f i =
        match sv_local2n_expr_snd x i with
        | Ne_rand -> raise Stop
        | x -> x in
      try Nd_utils.n_cons_subst f nc with Stop -> Nc_rand


    (** Management of cells and values *)
    (* Will that symb. var. creation be allowed by the domain? *)
    let sv_is_allowed ?(attr: node_attribute = Attr_none) (nt: ntyp)
        (na: nalloc) (x: t): bool =
      D1.sv_is_allowed ~attr nt na x.t_fst &&
      D2.sv_is_allowed ~attr nt na x.t_snd
    (* Add a node, with a newly generated id *)
    let sv_add_fresh ?(attr: node_attribute = Attr_none) ?(root: bool = false)
        (nt: ntyp) (na: nalloc) (x: t): int * t =
      (* 1. create sv in both underlying shape components *)
      let i1, x1 = D1.sv_add_fresh ~attr:attr ~root:root nt na x.t_fst
      and i2, x2 = D2.sv_add_fresh ~attr:attr ~root:root nt na x.t_snd in
      (* 2. fix sve *)
      let x = sve_fix { x with
                        t_fst = x1;
                        t_snd = x2 } in
      (* 3. add i1==i2 in EQS component *)
      let x = { x with t_eqs = Dom_eqs.write_eq i1 i2 x.t_eqs } in
      (* 4. returns local version of i1 (sound, it could be i2) *)
      DIC.fst2local x.t_dic i1, x

    (* Recover information about a symbolic variable *)
    let sv_get_info (i: int) (x: t): nalloc option * ntyp option =
      match DIC.local2under x.t_dic i with
      | Dic_fst, i1 -> D1.sv_get_info i1 x.t_fst
      | Dic_snd, i2 -> D2.sv_get_info i2 x.t_snd

    (* Garbage collection *)
    let gc (roots: int uni_table) (x: t): t =
      (* 0. compute roots for underlying shape components *)
      let roots1, roots2 =
        Aa_sets.fold
          (fun i (roots1, roots2) ->
            let op_i1, op_i2 = sv_local2under x i in
            let roots1 =
              match op_i1 with
              | Some i1 -> Aa_sets.add i1 roots1
              | None    -> roots1
            and roots2 =
              match op_i2 with
              | Some i2 -> Aa_sets.add i2 roots2
              | None    -> roots2 in
            roots1, roots2
          ) roots (Aa_sets.empty, Aa_sets.empty) in
      (* 1. perform gcs on shape component *)
      let x1 = D1.gc roots1 x.t_fst
      and x2 = D2.gc roots2 x.t_snd in
      (* 2. fix SV env *)
      sve_fix { x with
                t_fst = x1;
                t_snd = x2 }

    (** Comparison and Join operators *)

    (* Tools, translators from local to underlying shape components *)

    let opt_hint_us_local2under (x: t): int hint_us option
      -> int hint_us option * int hint_us option = function
        | None -> None, None
        | Some hu ->
            let l1, l2 =
              Aa_sets.fold
                (fun i (l1, l2) ->
                  let op_i1, op_i2 = sv_local2under x i in
                  let l1 =
                    match op_i1 with
                    | Some i1 -> Aa_sets.add i1 l1
                    | None -> l1
                  and l2 =
                    match op_i2 with
                    | Some i2 -> Aa_sets.add i2 l2
                    | None -> l2 in
                  l1, l2
                ) hu.hus_live (Aa_sets.empty, Aa_sets.empty) in
            Some { hus_live = l1 }, Some { hus_live = l2 }
    let opt_hint_bs_local2under (xl: t) (xr: t): int hint_bs option ->
      int hint_bs option * int hint_bs option = function
        | None -> None, None
        | Some hb ->
            let t1, t2 =
              Aa_maps.fold
                (fun ir il (t1, t2) ->
                  let op_ir1, op_ir2 = sv_local2under xr ir
                  and op_il1, op_il2 = sv_local2under xl il in
                  let t1 =
                    match op_ir1, op_il1 with
                    | Some ir1, Some il1 -> Aa_maps.add ir1 il1 t1
                    | _ -> t1
                  and t2 =
                    match op_ir2, op_il2 with
                    | Some ir2, Some il2 -> Aa_maps.add ir2 il2 t2
                    | _ -> t2 in
                  t1, t2
                ) hb.hbs_live (Aa_maps.empty, Aa_maps.empty) in
            Some { hbs_live = t1 }, Some { hbs_live = t2 }
    let bin_table_local2under (xl: t) (xr: t)
        (roots: int bin_table): int bin_table * int bin_table =
      Aa_maps.fold
        (fun ir il (r1, r2) ->
          let op_il1, op_il2 = sv_local2under xl il
          and op_ir1, op_ir2 = sv_local2under xr ir in
          let r1 =
            match op_il1, op_ir1 with
            | Some il1, Some ir1 -> Aa_maps.add ir1 il1 r1
            | _ -> r1
          and r2 =
            match op_il2, op_ir2 with
            | Some il2, Some ir2 -> Aa_maps.add ir2 il2 r2
            | _ -> r2 in
          r1, r2
        ) roots (Aa_maps.empty , Aa_maps.empty)
    let tri_table_local2under (xl: t) (xr: t)
        (roots: int tri_table): int tri_table * int tri_table =
      Aa_sets.fold
        (fun (il, ir, io) (r1, r2) ->
          let op_il1, op_il2 = sv_local2under xl il
          and op_ir1, op_ir2 = sv_local2under xr ir in
          let r1 =
            match op_il1, op_ir1 with
            | Some il1, Some ir1 -> Aa_sets.add (il1, ir1, il1) r1
            | _ -> r1
          and r2 =
            match op_il2, op_ir2 with
            | Some il2, Some ir2 -> Aa_sets.add (il2, ir2, il2) r2
            | _ -> r2 in
          r1, r2
        ) roots (Aa_sets.empty, Aa_sets.empty)
    (* Compose svenv_upd *)
    let svenv_upd_under2local
        (dic_l: DIC.t) (dic_r: DIC.t)
        (svu1: svenv_upd) (svu2: svenv_upd): svenv_upd =
      let sv_upd_map f = function
        | Svu_mod (i, s) ->
            let sf = IntSet.fold (fun i -> IntSet.add (f i)) s IntSet.empty in
            Svu_mod (f i, sf)
        | Svu_rem -> Svu_rem in
      fun il ->
        match DIC.local2under dic_l il with
        | Dic_fst, il1 -> sv_upd_map (DIC.fst2local dic_r) (svu1 il1)
        | Dic_snd, il2 -> sv_upd_map (DIC.snd2local dic_r) (svu2 il2)
    (* lift up equalities *)
    let eqs_lift
        (cond: int -> int -> bool) (* filter, used to compute intersection *)
        (e_under: (int, int) Dom_eqs.t) (* equalities to be lifted up *)
        (svu1: svenv_upd) (svu2: svenv_upd): (int, int) Dom_eqs.t =
      let f svu u i =
        match svu i, u with
        | u0, Svu_rem
        | Svu_rem, u0 -> u0
        | Svu_mod (jj, ss), Svu_mod (j ,s) ->
            Svu_mod (j, IntSet.add jj (IntSet.union s ss)) in
      Dom_eqs.fold
        (fun lst1 lst2 e ->
          let u1 = List.fold_left (f svu1) Svu_rem lst1
          and u2 = List.fold_left (f svu2) Svu_rem lst2 in
          match u1, u2 with
          | Svu_rem, _ | _, Svu_rem -> e
          | Svu_mod (i1, s1), Svu_mod (i2, s2) ->
              let wr12 i1 i2 e =
                if cond i1 i2 then Dom_eqs.write_eq i1 i2 e else e in
              let wr21 i2 i1 = wr12 i1 i2 in
              let e = wr12 i1 i2 e in
              let e = IntSet.fold (wr12 i1) s2 e in
              IntSet.fold (wr21 i2) s1 e
        ) e_under Dom_eqs.empty

    (* Checks if the left argument is included in the right one *)
    let is_le
        (roots: int bin_table) (setroots: int bin_table)
        (xl: t) (xr: t): svenv_upd option =
      (* 0. split the roots *)
      let roots1, roots2 = bin_table_local2under xl xr roots in
      match D1.is_le roots1 setroots xl.t_fst xr.t_fst with
      | None -> None
      | Some svu1 ->
          match D2.is_le roots2 setroots xl.t_snd xr.t_snd with
          | None -> None
          | Some svu2 ->
              (* check equalities inclusion *)
              let e_l2r = eqs_lift (fun _ _ -> true) xl.t_eqs svu1 svu2 in
              let b =
                try
                  Dom_eqs.iter
                    (fun l1 l2 ->
                      List.iter
                        (fun i1 ->
                          List.iter
                            (fun i2 ->
                              if not (Dom_eqs.are_eq i1 i2 e_l2r) then
                                raise Stop
                            ) l2
                        ) l1
                    ) xr.t_eqs;
                  true
                with Stop -> false in
              if b then Some (svenv_upd_under2local xl.t_dic xr.t_dic svu1 svu2)
              else None

    (* encode graph *)
    let encode (disj: int) (n: namer) (x: t) =
      Log.todo_exn "encode"

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
      (* 0. split roots and hints *)
      let hbo1, hbo2 = opt_hint_bs_local2under xl xr hbo in
      let roots1, roots2 = tri_table_local2under xl xr roots in
      (* 1. compute joins on underlying shape components *)
      let x1o, svu1l, svu1r =
        D1.join jk hbo1 None roots1 setroots (xl.t_fst, jl) (xr.t_fst, jr)
      and x2o, svu2l, svu2r =
        D2.join jk hbo2 None roots2 setroots (xl.t_snd, jl) (xr.t_snd, jr) in
      (* 2. compute the join of equalities *)
      let eqs_from_l = eqs_lift (fun _ _ -> true) xl.t_eqs svu1l svu2l in
      let cond i1 i2 = Dom_eqs.are_eq i1 i2 eqs_from_l in
      let eqs = eqs_lift cond xr.t_eqs svu1r svu2r in
      (* 3. compute the new dictionary *)
      let dic =
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
      let x = { t_dic = dic;
                t_fst = x1o;
                t_snd = x2o;
                t_eqs = eqs;
                t_envmod = svenv_empty } in
      let svul = svenv_upd_under2local xl.t_dic x.t_dic svu1l svu2l
      and svur = svenv_upd_under2local xr.t_dic x.t_dic svu1r svu2r in
      x, svul, svur

    (* Directed weakening; over-approximates only the right element *)
    let directed_weakening
        (hbo: int hint_bs option)
        (roots: int tri_table) (setroots: int tri_table)
        (xl: t) (xr: t): t * svenv_upd =
      Log.todo_exn "directed_weakening"

    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    let local_abstract (ohus: int hint_us option) (x: t): t =
      (* temporary assertions, to be removed *)
      assert (svenv_is_empty x.t_envmod);
      let ohus1, ohus2 = opt_hint_us_local2under x ohus in
      sve_fix { x with
                t_fst = D1.local_abstract ohus1 x.t_fst;
                t_snd = D2.local_abstract ohus2 x.t_snd }

    (** Cell operations *)

    (* Addition of a cell *)
    let cell_create ?(attr:node_attribute = Attr_none)
        ((i, off): onode) (sz: Offs.size) (nt: ntyp) (x: t): t =
      match sv_local2under x i with
      | Some i1, Some i2 ->
          sve_fix { x with
                    t_fst = D1.cell_create (i1, off) sz nt x.t_fst;
                    t_snd = D2.cell_create (i2, off) sz nt x.t_snd }
      | _ ->
          Log.fatal_exn
            "cell_create: SV can not be found in both shape components"

    (* Remove a cell *)
    let cell_delete ?(free: bool = true) ?(root:bool = false)
        (i: int) (x: t): t =
      match sv_local2under x i with
      | Some i1, Some i2 ->
          sve_fix { x with
                    t_fst = D1.cell_delete ~free:free ~root:root i1 x.t_fst;
                    t_snd = D2.cell_delete ~free:free ~root:root i2 x.t_snd }
      | _ ->
          Log.fatal_exn
            "cell_delete: SV can not be found in both shape components"

    (* Read *)
    let cell_read (is_resolve: bool) ((i, off): onode) (sz: int) (x: t)
        : (t * onode * onode option) list =
      match sv_local2under x i with
      | Some i1, Some i2 ->
          let res1 = D1.cell_read false (i1, off) sz x.t_fst
          and res2 = D2.cell_read false (i2, off) sz x.t_snd in
          (* Combine results *)
          List.fold_left
            (fun res (x1, src1, op_dst1) ->
              List.fold_left
                (fun res (x2, src2, op_dst2) ->
                  (* 1. make the new abstract value *)
                  let x = sve_fix { x with
                                    t_fst = x1;
                                    t_snd = x2 } in
                  (* 2. make src *)
                  assert(Offs.eq (snd src1) (snd src2));
                  let x =
                    let eqs = Dom_eqs.write_eq (fst src1) (fst src2) x.t_eqs in
                    { x with t_eqs = eqs } in
                  let src = onode_fst2local x src1 in
                  (* 3. make the returned dst *)
                  let x, op_dst =
                    match op_dst1, op_dst2 with
                    | Some (j1, off1), Some (j2, off2) ->
                        assert(Offs.eq off1 off2);
                        let x = { x with
                                  t_eqs = Dom_eqs.write_eq j1 j2 x.t_eqs } in
                        let op_dst = Some (DIC.fst2local x.t_dic j1, off1) in
                        x, op_dst
                    | Some dst1, None -> x, Some (onode_fst2local x dst1)
                    | None, Some dst2 -> x, Some (onode_snd2local x dst2)
                    | _ -> x, None in
                  (x, src, op_dst)::res
                ) res res2
            ) [] res1
      | Some i1, None ->
          let res1 = D1.cell_read false (i1, off) sz x.t_fst in
          List.map
            (fun (x1, src1, op_dst1) ->
              let x = sve_fix { x with t_fst = x1 } in
              let src = onode_fst2local x src1
              and op_dst = Option.map (onode_fst2local x) op_dst1 in
              x, src, op_dst
            ) res1
      | None, Some i2 ->
          let res2 = D2.cell_read false (i2, off) sz x.t_snd in
          List.map
            (fun (x2, src2, op_dst2) ->
              let x = sve_fix { x with t_snd = x2 } in
              let src = onode_snd2local x src2
              and op_dst = Option.map (onode_snd2local x) op_dst2 in
              x, src, op_dst
            ) res2
      | _ ->
          Log.fatal_exn "cell_read: SV can not be found in any shape component"

    (* Resolving a cell, i.e., preparing it for a read or write *)
    let cell_resolve ((i, off): onode) (sz: int) (x: t)
        : (t * onode * bool) list =
      match sv_local2under x i with
      | Some i1, Some i2 ->
          let res1 = D1.cell_resolve (i1, off) sz x.t_fst
          and res2 = D2.cell_resolve (i2, off) sz x.t_snd in
          (* Combine results *)
          List.fold_left
            (fun res (x1, (i1, off1), b1) ->
              List.fold_left
                (fun res (x2, (i2, off2), b2) ->
                  assert( Offs.eq off1 off2 );
                  let x = sve_fix { x with
                                    t_fst    = x1;
                                    t_snd    = x2 } in
                  let x = { x with t_eqs = Dom_eqs.write_eq i1 i2 x.t_eqs } in
                  let i = DIC.fst2local x.t_dic i1 in
                  (x, (i, off1), (b1 && b2))::res
                ) res res2
            ) [] res1
      | _ ->
          Log.fatal_exn
            "cell_resolve: SV can not be found in both shape components"

    (* Write *)
    let cell_write (nt: ntyp)
        ((i, off): onode) (sz: int) (ne: n_expr) (x: t): t =
      match sv_local2under x i with
      | Some i1, Some i2 ->
          let ne1 = n_expr_local2fst x ne
          and ne2 = n_expr_local2snd x ne in
          sve_fix { x with
                    t_fst = D1.cell_write nt (i1, off) sz ne1 x.t_fst;
                    t_snd = D2.cell_write nt (i2, off) sz ne2 x.t_snd }
      | _ ->
          Log.fatal_exn
            "cell_write: SV can not be found in both shape components"


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

    (** Unfolding, assuming and checking inductive edges *)
    (* Translate gen_ind_call from (D1 X D2) to D1 (resp. D2) *)
    let gen_ind_call_local2fst (x: t)
        (ic: onode gen_ind_call): onode gen_ind_call option =
      let f (i, off) =
        match sv_local2under x i with
        | Some i1, _ -> i1, off
        | _ -> raise Stop in
      try Some (map_gen_ind_call f ic) with Stop -> None
    let gen_ind_call_local2snd (x: t)
        (ic: onode gen_ind_call): onode gen_ind_call option =
      let f (i, off) =
        match sv_local2under x i with
        | _, Some i2 -> i2, off
        | _ -> raise Stop in
      try Some (map_gen_ind_call f ic) with Stop -> None

    let assume (op: meml_log_form) (x: t) =
      match op with
      | SL_set _ -> Log.todo_exn "assume Setprop"
      | SL_array -> Log.todo_exn "assume Array"
      | SL_seg (ic, lv, ic_e, lv_e) -> Log.todo_exn "assume Segment"
      | SL_ind (ic, (i, off)) ->
          begin
            let do1 i1 =
              if D1.inductive_is_allowed ic.ic_name then
                match gen_ind_call_local2fst x ic with
                | Some ic1 ->
                    Log.info "ind_assume in D1";
                    D1.assume (SL_ind (ic1, (i1, off))) x.t_fst
                | None     -> x.t_fst
              else x.t_fst
            and do2 i2 =
              if D2.inductive_is_allowed ic.ic_name then
                match gen_ind_call_local2snd x ic with
                | Some ic2 ->
                    Log.info "ind_assume in D2";
                    D2.assume (SL_ind (ic2, (i2, off))) x.t_snd
                | None     -> x.t_snd
              else x.t_snd in
            match sv_local2under x i with
            | Some i1, Some i2 -> { x with t_fst = do1 i1; t_snd = do2 i2 }
            | Some i1, None    -> { x with t_fst = do1 i1 }
            | None, Some i2    -> { x with t_snd = do2 i2 }
            | None, None       -> x
          end

    (* Unfold *)
    let ind_unfold
        (udir: unfold_dir)
        ((i, off): onode) (x: t): t list =
      let op_i1, op_i2 = sv_local2under x i in
      let res1 =
        match op_i1 with
        | Some i1 -> D1.ind_unfold udir (i1, off) x.t_fst
        | None    -> [ x.t_fst ]
      and res2 =
        match op_i2 with
        | Some i2 -> D2.ind_unfold udir (i2, off) x.t_snd
        | None    -> [ x.t_snd ] in
      List.fold_left
        (fun res x1 ->
          List.fold_left
            (fun res x2 ->
              let x = sve_fix { x with
                                t_fst = x1;
                                t_snd = x2 } in
              x::res
            ) res res2
        ) [] res1

    let check (op: meml_log_form) (x: t): bool =
      match op with
      | SL_set _ -> Log.todo_exn "check Setprop"
      | SL_array -> Log.todo_exn "check Array"
      | SL_seg _ -> Log.todo_exn "check Segment"
      | SL_ind (ic, (i, off)) ->
          begin
            (* Check construction, that an inductive be there *)
            let do1 i1 =
              D1.inductive_is_allowed ic.ic_name
                &&
              begin
                match gen_ind_call_local2fst x ic with
                | Some ic1 ->
                    Log.info "ind_check in D1";
                    D1.check (SL_ind (ic1, (i1, off))) x.t_fst
                | None     -> false
              end
            and do2 i2 =
              D2.inductive_is_allowed ic.ic_name
                &&
              begin
                match gen_ind_call_local2snd x ic with
                | Some ic2 ->
                    Log.info "ind_check in D2";
                    D2.check (SL_ind (ic2, (i2, off))) x.t_snd
                | None     -> false
              end
            and do_eq () =
              Log.info "ind_check in EQS";
              Offs.is_zero off &&
              let ind = Ind_utils.ind_find ic.ic_name in
              let nc = Nc_cons (Apron.Tcons1.EQ, Ne_var i, Ne_csti 0) in
              ind.i_mt_rule && sat nc x in
            match sv_local2under x i with
            | Some i1, Some i2 -> do1 i1 || do2 i2 || do_eq ()
            | Some i1, None    -> do1 i1 || do_eq ()
            | None, Some i2    -> do2 i2 || do_eq ()
            | _                -> do_eq ()
        end

  end: DOM_MEM_LOW)

(** The product functor instanciated with the chosen DIC module *)
module Dom_prod = Dom_prod_dic( Dic_hash )
(*module Dom_prod = Dom_prod_dic( Dic_map )*)
