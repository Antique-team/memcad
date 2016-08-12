(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_mem_exprs.ml
 **       Memory abstract domain; expressions evaluation layer
 ** Xavier Rival, 2013/08/14 *)
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
open Graph_utils
open Nd_utils

open Apron

(** This module factors some code out of the rest of the shape domain;
 ** it is effectively shared across all dom_mem_low implementations:
 **  - translation of expressions from "int expr" to "n_expr", lvalues,
 **    and conditions
 **  - reading of lvalues
 **  - higher level treatment of assign, guard, sat, alloc *)

(** Error report *)
module Log =
  Logger.Make(struct let section = "dm_xpr__" and level = Log_level.DEBUG end)

let debug_mod = false

(** The build functor *)
module DBuild = functor (D: DOM_MEM_LOW) ->
  (struct
    (** Type of abstract values *)
    type t = D.t (* same as layer below; this layer aims at factoring code *)

    (** Domain initialization to a set of inductive definitions *)
    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (g: Keygen.t) (s: StringSet.t): Keygen.t =
      D.init_inductives g s (* this domain generates no keys *)
    let inductive_is_allowed: string -> bool = D.inductive_is_allowed

    (** Fixing sets of keys *)
    let sve_sync_bot_up: t -> t * svenv_mod = D.sve_sync_bot_up

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t = D.bot
    let is_bot: t -> bool = D.is_bot
    (* Top element, with empty set of roots *)
    let top: unit -> t = D.top
    (* Pretty-printing *)
    let t_2stri: string -> t -> string = D.t_2stri
    let t_2str: t -> string = D.t_2str
    (* External output *)
    let ext_output: output_format -> string -> namer -> t -> unit =
      D.ext_output

    (* Garbage collection *)
    let gc: int uni_table -> t -> t = D.gc

    (* Function handling outputs of cell_read/cell_resolve *)
    let cell_read src sz x =
      let f = function
        | x, _, Some cont -> x, cont
        | x, _, None      -> Log.fatal_exn "cell_read fails" in
      List.map f (D.cell_read false src sz x)
    let cell_resolve src sz x =
      let f (x, src, b) =
        if b then x, src else Log.fatal_exn "cell_resolve fails" in
      List.map f (D.cell_resolve src sz x)


    (** Evaluation of l-values and expressions (with possible unfolding) *)

    (* Translation of an expression *)
    let rec tr_expr (ind: string) (x: t) (e: int expr): (t * n_expr) list =
      let nind = "  "^ind in
      (* value of the variable, augmented of the offset, if any *)
      let onode_2var (n, o): n_expr =
        if Offs.is_zero o then Ne_var n
        else Ne_bin (Texpr1.Add, Ne_var n, Offs.to_n_expr o) in
      match e with
      | Erand ->
          [ x, Ne_rand ]
      | Ecst (Cint i) ->
          [ x, Ne_csti i ]
      | Ecst (Cint64 i) ->
          let ci = Int64.to_int i in let cci = Int64.of_int ci in
          if i != cci then Log.warn "imprecise conversion int64 => int32";
          [ x, Ne_csti ci ]
      | Ecst (Cchar c) ->
          [ x, Ne_cstc c ]
      | Elval tl ->
          List.map (fun (x, v) -> x, onode_2var v) (rd_tlval nind x tl)
      | EAddrOf lv ->
          List.map (fun (x, iv) -> x, onode_2var iv) (tr_tlval nind x lv)
      | Ebin ((Badd | Bsub | Bmul | Bdiv | Bmod) as op, e0, e1) ->
          let t_op = tr_bin_op op in
          List.fold_left
            (fun acc (x, ne0) ->
              List.fold_left
                (fun acc (x, ne1) ->
                  (x, Ne_bin (t_op, ne0, ne1)) :: acc
                ) acc (tr_texpr nind x e1)
            ) [] (tr_texpr nind x e0)
      | Euni (Uneg, e0) ->
          List.map
            (fun (x, ne0) ->
              x, Ne_bin (Texpr1.Sub, Ne_csti 0, ne0))
            (tr_texpr nind x e0)
      | _ ->
          Log.todo_exn "tr_expr: %s" (iexpr_2str e)
    and tr_texpr (ind: string) (x: t) (te: int texpr): (t * n_expr) list =
      if !flag_debug_dommem_eval then
        Log.force "%s=> tr_texpr<%s>" ind (itexpr_2str te);
      let r = tr_expr ind x (fst te) in
      if !flag_debug_dommem_eval then
        Log.force "%s<= tr_texpr<%s> =>    %s" ind
          (itexpr_2str te)
          (gen_list_2str "_|_" (fun (_, io) -> n_expr_2str io) ", " r);
      r

    (* Translation of an lvalue *)
    and tr_lval (ind: string) (x: t) (lv: int lval): (t * onode) list =
      let nind = "  "^ind in
      match lv with
      | Lvar i -> [ x, (i, Offs.zero) ]
      | Lfield (tl0, fld) ->
          let ofld = field_2off fld in
          List.map (fun (x, (i, o)) -> x, (i, Offs.add o ofld))
            (tr_tlval nind x tl0)
      | Lderef e0 ->
          List.map
            (fun (x, ne0) ->
              let v, ee = Nd_utils.decomp_lin ne0 in
              x, (v, Offs.of_n_expr ee)
            ) (tr_texpr nind x e0)
      | Lindex (lv0, e1) ->
          let align =
            match snd lv0 with
            | Tarray (t0,_) -> sizeof_typ t0
            | _ -> Log.fatal_exn "Lindex applied to non array type" in
          if !flag_debug_array_blocks then
            Log.force "%s   align is %d" ind align;
          let l0 = tr_tlval nind x lv0 in
          List.fold_left
            (fun acc (x, (ibase, obase)) ->
              let l1 = tr_texpr nind x e1 in
              List.fold_left
                (fun acc (x, ne1) ->
                  let otot =
                    Offs.add obase (Offs.mul_int (Offs.of_n_expr ne1) align) in
                  (x, (ibase, otot)) :: acc
                ) acc l1
            ) [] l0
    and tr_tlval (ind: string) (x: t) (tl: int tlval): (t * onode) list =
      if !flag_debug_dommem_eval then
        Log.force "%s=> tr_tlval<%s;%s>" ind
          (if !flag_debug_dommem_evalx then typ_2str (snd tl) else "")
          (itlval_2str tl);
      let r = tr_lval ind x (fst tl) in
      if !flag_debug_dommem_eval then
        Log.force "%s<= tr_tlval<%s;%s>:  %s" ind
          (if !flag_debug_dommem_evalx then typ_2str (snd tl) else "")
          (itlval_2str tl)
          (gen_list_2str "_|_" (fun (_, io) -> onode_2str io) ", " r);
      r

    (* Reading of an lvalue (computation of *lv) *)
    and rd_lval (ind: string) (x: t) (sz: int) (lv: int lval)
        : (t * onode) list =
      let res = tr_lval ind x lv in
      List.fold_left
        (fun acc (x, src) -> (cell_read src sz x) @ acc) [ ] res
    and rd_tlval (ind: string) (x: t) (tl: int tlval)
        : (t * onode) list =
      if !flag_debug_dommem_eval then
        Log.force "%s=> rd_tlval<%s><%s>" ind
          (if !flag_debug_dommem_evalx then typ_2str (snd tl) else "")
          (itlval_2str tl);
      let r = rd_lval ind x (sizeof_typ (snd tl)) (fst tl) in
      if !flag_debug_dommem_eval then
        Log.force "%s<= rd_tlval<%s><%s>:  %s" ind
          (if !flag_debug_dommem_evalx then typ_2str (snd tl) else "")
          (itlval_2str tl)
          (gen_list_2str "_|_" (fun (_, io) -> onode_2str io) ", " r);
      r

    (* Translation of conditions *)
    let tr_tcond (ind: string) (x: t) (tc: int texpr): (t * n_cons) list =
      let rec aux (x: t) (tc: int texpr) =
        let te_zero = Ne_csti 0 in
        match fst tc with
        | Ecst (Cint i) -> [ x, Nc_bool (i != 0) ]
        | Euni (Unot, e0) -> (* negation of e0 *)
            begin
              match fst e0 with
              | Elval _ -> (* amounts to e0 == 0 *)
                  let l = tr_texpr ind x e0 in
                  List.map
                    (fun (x, te) -> (x, Nc_cons (Tcons1.EQ, te, te_zero))) l
              | Ecst (Cint i) -> [ x, Nc_bool (i == 0) ]
              | Erand -> Log.todo_exn "tr_tcond: Unot on Erand"
              | Ecst _ -> Log.todo_exn "tr_tcond: Unot on Ecst"
              | Euni (_, _) -> Log.todo_exn "tr_tcond: Unot on Euni"
              | Ebin (op, lhs, rhs) ->
                  begin
                    match op with
                    | Beq -> aux x (Ebin (Bne, lhs, rhs), snd tc)
                    | Bne -> aux x (Ebin (Beq, lhs, rhs), snd tc)
                    | _ -> Log.todo_exn "tr_tcond: Unot on Ebin: %s"
                             (bin_op_2str op)
                  end
              | EAddrOf _ -> Log.todo_exn "tr_tcond: Unot on EAddrOf"
            end
        | Ebin ((Bgt | Bge | Beq | Bne) as op, e0, e1) ->
            if (texpr_is_rand_cell e0 && texpr_is_const e1
              || texpr_is_const e0 && texpr_is_rand_cell e1) then
              [ x, Nc_rand ]
            else
              let aop = make_apron_op op in
              let l_left = tr_texpr ind x e0 in
              List.fold_left
                (fun acc (xleft, ne0) ->
                  let l_right = tr_texpr ind xleft e1 in
                  List.fold_left
                    (fun acc (xright, ne1) ->
                      let bchr = xright == xleft in
                      let ne0 =
                        if not bchr then
                          match tr_texpr ind xright e0 with
                          | [ _, ne0 ] -> ne0
                          | _ ->
                              (* this case would mean we need to recompute
                               * the left expression again as the graph changed
                               * due to additional unfolding
                               * (this has not happened yet) *)
                              Log.todo_exn
                                "tr_cond: would need to recompute left side"
                        else ne0 in
                      (xright, Nc_cons (aop, ne0, ne1)) :: acc
                    ) acc l_right
                ) [ ] l_left
        | Elval _ -> (* amounts to e != 0 *)
            let l = tr_texpr ind x tc in
            List.map (fun (x, te) -> x, Nc_cons (Tcons1.DISEQ, te, te_zero)) l
        | Ebin (Band, e0, e1) -> Log.todo_exn "tr_tcond &&"
        | Ebin (Bor, e0, e1) -> Log.todo_exn "tr_tcond ||"
        | _ -> Log.todo_exn "tr_tcond: %s" (itexpr_2str tc) in
      aux x tc (* we may remove the aux function *)

    (* encode of graph *)
    let encode (disj: int) (l: namer) (x: t) =
      D.encode disj l x

    (** Operations on hints *)
    (* Pretty-printing *)
    let lint_bs_2str (l: ('a lint_bs) option) (f: 'a -> string): string =
      match l with
      | None -> ""
      | Some l ->
          Printf.sprintf "dead: %s"
            (Aa_maps.t_2str "" "\n"
               (fun i j -> Printf.sprintf "%s => %s" (f i)  (f j)) l.lbs_dead)
    (* Lint translation *)
    let compute_lint_bin (x0: t) (x1: t) (le: ((int tlval) lint_bs) option)
        : (onode lint_bs option) * t * t =
      if debug_mod then Log.info "compute_lint_bin";
      match le with
      | None -> None, x0, x1
      | Some le ->
          let s, x0, x1  =
            Aa_maps.fold
              (fun lv0 lv1 (acc, x0, x1) ->
                try
                  let lv0_u = tr_tlval "" x0 lv0 in
                  let lv1_u = tr_tlval "" x1 lv1 in
                  assert (List.length lv0_u = 1);
                  assert (List.length lv1_u = 1);
                  let x0, on0 = List.hd lv0_u in
                  let x1, on1 = List.hd lv1_u in
                  (Aa_maps.add on0 on1 acc), x0, x1
                with
                | Failure _ -> acc, x0, x1
              ) le.lbs_dead  (Aa_maps.empty, x0, x1) in
          Some { lbs_dead = s }, x0, x1

    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    let is_le (roots: int bin_table) (setroots: int bin_table)
        (xl: t) (xr: t): bool =
      match D.is_le roots setroots xl xr with Some _ -> true | None -> false
    (* Generic comparison (does both join and widening) *)
    let join
        (jk: join_kind) (h: int hint_bs option)
        (l: ((int tlval) lint_bs) option)
        (roots: int tri_table) (setroots: int tri_table)
        ((xl, jl): t * join_ele) ((xr, jr): t * join_ele): t =
      let l, xl, xr = compute_lint_bin xl xr l in
      if debug_mod then
        Log.info "lint_bin: %s"  (lint_bs_2str l onode_2str);
      let xo, _, _ = D.join jk h l roots setroots (xl, jl) (xr, jr) in
      xo
    (* Directed weakening; over-approximates only the right element *)
    let directed_weakening
        (h: int hint_bs option)
        (roots: int tri_table) (setroots: int tri_table)
        (xl: t) (xr: t): t =
      let xo, _ = D.directed_weakening h roots setroots xl xr in xo
    (* Unary abstraction, a kind of weaker canonicalization operator *)
    let local_abstract: int hint_us option -> t -> t =
      D.local_abstract

    (** Transfer functions for the analysis *)
    (* Assignment *)
    let assign (lv: int tlval) (ex: int texpr) (x: t): t list =
      (* 1. get ntyp and size from typ *)
      let typ, size =
        match snd ex with
        | Tint (sz, _) -> Ntint, sz
        | Tptr _       -> Ntaddr, abi_ptr_size (* means pointer assignment *)
        | t -> Log.todo_exn "assign: type-to-kind: %s" (typ_2str t) in
      (* 2. evaluate l-value *)
      let l = tr_tlval "" x lv in
      (* 3. resolve cells to write on (prepare them for materialization) *)
      let l =
        let f (x, wr_on) = cell_resolve wr_on size x in
        List.map_flatten f l in
      (* 4. write cells *)
      let f ((x, wr_on): t * onode): t list =
        (* evaluate r-value *)
        let l_ex = tr_texpr "" x ex in
        let f ((x, val_en): t * n_expr): t =
          D.cell_write typ wr_on size val_en x in
        List.map f l_ex in
      List.map_flatten f l

    (* Condition test *)
    let guard (b: bool) (cond: int texpr) (x: t): t list =
      let rec guard_aux (b: bool) (ct: int condtree) (x: t): t list =
        match ct, b with
        | Ctrand, _ ->
            [ x ]
        | Ctleaf cnd, _ ->
            let l_cnd = tr_tcond "" x cnd in
            List.map
              (fun (x, conv) ->
                let tcnd = if b then conv else Nd_utils.neg_n_cons conv in
                D.guard tcnd x
              ) l_cnd
        | Ctland (c0, c1), true | Ctlor (c0, c1), false ->
            List.map_flatten (guard_aux b c1) (guard_aux b c0 x)
        | Ctland (c0, c1), false | Ctlor (c0, c1), true ->
            (guard_aux b c0 x) @ (guard_aux b c1 x) in
      let ct = extract_tree cond in
      let res = guard_aux b ct x in
      res

    (* Checking that a constraint is satisfied *)
    let sat (cond: int texpr) (x: t): bool =
      let rec sat_aux (c: int condtree): bool =
        match c with
        | Ctrand ->
            false
        | Ctleaf cnd ->
            List.for_all
              (fun (x, conv) -> D.sat conv x)
              (tr_tcond "" x cnd)
        | Ctland (c0, c1) ->
            sat_aux c0 && sat_aux c1
        | Ctlor (c0, c1) ->
            sat_aux c0 || sat_aux c1 in
      let ct = extract_tree cond in
      sat_aux ct

    (* Checking that several constraints are satisfied *)
    let sat_many (conds: int texpr list) (x: t): bool =
      List.for_all (fun c -> sat c x) conds

    (* Creation of the memory for a variable *)
    let create_mem_var (typ: typ) (x: t): int * t =
      (* conversion of types *)
      let fldof_strt (t: typ): int list =
        match t with
        | Tstruct s ->
            List.map (fun ele ->  ele.tsf_size) s.ts_fields
        | _ -> [ sizeof_typ t ] in
      let rec conv_typ (t: typ)
          : (node_attribute * ntyp * int * Offs.t) list =
        match t with
        | Tint (s, _) -> [ Attr_none, Ntint, s, Offs.zero ]
        | Tptr _ -> [ Attr_none, Ntaddr, Flags.abi_ptr_size, Offs.zero ]
        | Tstruct s ->
            List.map
              (fun p ->
                match conv_typ p.tsf_typ with
                | [ a, t, s, o ] ->
                    assert (s = p.tsf_size);
                    a, t, s, Offs.add_int o p.tsf_off
                | _ -> Log.fatal_exn "conv_typ: unsupported nested aggregates"
              ) s.ts_fields
        | Tarray (sub, s) ->
            [ Attr_array (s, Some (fldof_strt sub)),
              Ntraw, sizeof_typ t, Offs.zero ]
        | _ -> Log.fatal_exn "conv_typ: unsupported type: %s" (typ_2str t) in
      let lfields = conv_typ typ in
      (* compute node attribute, for sub-mem detection *)
      let nattr =
        match typ with
        | Tarray (sub,_) -> Attr_array (sizeof_typ sub, None)
        | _ -> Attr_none in
      (* add a node for the address and another for the content *)
      let n_address, m0 =
        D.sv_add_fresh ~attr:nattr ~root:true Ntaddr Nstack x in
      let r =
        List.fold_left
          (fun acc (at, gk, size, off) ->
            D.cell_create
              ~attr:at (n_address, off) (Offs.size_of_int size) gk acc
          ) m0 lfields in
      n_address, r

    (** Management of the memory: add/destroy cells *)
    let delete_mem_var: int -> t -> t = D.cell_delete ~free:false ~root:true

    (* Allocation *)
    let memory (op: int_mem_operand) (x: t): t list =
      match op with
      | Allocate (lv, ex) ->
          let lv_sz = sizeof_typ (snd lv) in
          assert (lv_sz = abi_ptr_size);
          (* 1. evaluate left value *)
          let l_lv = tr_tlval "" x lv in
          let f ((x, on_addr): t * onode): t list =
            (* 2. evaluate sizes *)
            let l_sz = tr_texpr "" x ex in
            List.map
              (fun (x, sz) ->
                 (* 3. perform the allocation *)
                 let attr =
                   match sz with
                   | Ne_csti cst -> Nheap (Some cst)
                   | _           -> Nheap None in
                 (* create the node representing the contents *)
                 let nc, x = D.sv_add_fresh Ntaddr attr x in
                 (* write the cell, corresponding to the allocated zone *)
                 let x =
                   D.cell_create (nc, Offs.zero) (Offs.to_size (Offs.of_n_expr sz))
                     Ntraw x in
                 D.cell_write Ntaddr on_addr lv_sz (Ne_var nc) x
              ) l_sz in
          List.map_flatten f l_lv
      | Deallocate lv ->
          (* 1. read l-value *)
          let l_lv = rd_tlval "" x lv in
          (* 2. materialize the deallocated cells *)
          let l_lv =
            let size = sizeof_typ (snd lv) in
            let f (x, wr_on) = cell_resolve wr_on size x in
            List.map_flatten f l_lv in
          (* 3. deallocate *)
          List.map
            (fun (x, (i, off)) ->
               if not (Offs.is_zero off) then
                 Log.fatal_exn
                   "deallocate applied to an offset not verified be null";
               D.cell_delete ~free:true i x
            ) l_lv

    (** Set domain *)

    (* Adding / removing set variables *)
    let gen_setvar (s: string) (x: t): int * t =
      D.setv_add_fresh true s x
    let del_setvar: int -> t -> t =
      D.setv_delete

    (* utility function *)
    let get_one (l: 'a list) (err_msg: string): 'a = match l with
      | [ u ] -> u
      | _ -> Log.fatal_exn "%s" err_msg

    (* Guard and sat functions for set properties *)
    (* set_prepare is common to both set_assume and set_sat *)
    let set_prepare (x: int tlval setprop) (t: t) (err_msg: string)
      : onode setprop * t =
      match x with
      | Sp_sub (l, r) -> Sp_sub (l, r), t
      | Sp_mem (e, r) ->
          let t, e = get_one (rd_tlval "" t e) err_msg in
          Sp_mem (e, r), t
      | Sp_emp l -> Sp_emp l, t
      | Sp_euplus (l, e, r) ->
          let t, e = get_one (rd_tlval "" t e) err_msg in
          Sp_euplus (l, e, r), t

    (** Unfolding, assuming and checking inductive edges *)

    (* Unfold *)
    let ind_unfold (ud: unfold_dir) (lv: int tlval) (x: t): t list =
      let l_lv = rd_tlval "" x lv in
      List.map_flatten (fun (x, on) -> D.ind_unfold ud on x) l_lv

    (* Utility function for ind_assume and ind_check
     *  translation of ind_call, assuming no cell need unfolding to be
     *  materialized (this is reasonable, as ind_assume, ind_check should
     *  apply to basic variables / access paths) *)
    let tr_ind_call (x: t) (ic: int tlval gen_ind_call)
        : t * onode gen_ind_call =
      let tr_list f l x =
        List.fold_left
          (fun (x, accl) a ->
            let x, b = f a x in x, b :: accl
          ) (x, [ ]) (List.rev l) in
      let f_int_tlval (lv: int tlval) (x: t): t * onode =
        match rd_tlval "" x lv with
        | [ y, on ] -> y, on
        | _ -> Log.fatal_exn "tr_ind_call: should not have to unfold" in
      let f_gen_ind_intp (ii: int tlval gen_ind_intp) (x: t)
          : t * onode gen_ind_intp =
        match ii with
        | Ii_const n -> x, Ii_const n
        | Ii_lval lv -> let y, on = f_int_tlval lv x in y, Ii_lval on in
      let f_gen_ind_pars (p: int tlval gen_ind_pars) (x: t)
          : t * onode gen_ind_pars =
        let x, n_ic_ptr = tr_list f_int_tlval p.ic_ptr x in
        let x, n_ic_int = tr_list f_gen_ind_intp p.ic_int x in
        x, { ic_ptr = n_ic_ptr ;
             ic_int = n_ic_int ;
             ic_set = p.ic_set } in
      let x, ind_pars =
        match ic.ic_pars with
        | Some p -> let x, p = f_gen_ind_pars p x in x, Some p
        | None   -> x, None in
      x, { ic_name = ic.ic_name;
           ic_pars = ind_pars }

    (** Check and assume constructions *)
    let prep_log_form (s: string) (x: t) (op: memh_log_form): meml_log_form * t =
      match op with
      | SL_set sp ->
          let err_msg = "set_"^s^": requires further unfolding" in
          let sp, x = set_prepare sp x err_msg in
          SL_set sp, x
      | SL_ind (ic, lv) ->
          (* For the sake of simplicity, we assume that no further unfolding
           * is needed in order to materialize cells from which the edge
           * should be added, and for the parameters *)
          let err_msg = "ind_"^s^": requires further unfolding" in
          let x, lv = get_one (rd_tlval "" x lv) err_msg in
          let x, ic = tr_ind_call x ic in
          SL_ind (ic, lv), x
      | SL_seg (ic, lv, ic_e, lv_e) ->
          let err_msg = "seg_"^s^": requires further unfolding" in
          let x, lv = get_one (rd_tlval "" x lv) err_msg in
          let x, ic = tr_ind_call x ic in
          let x, lv_e = get_one (rd_tlval "" x lv_e) err_msg in
          let x, ic_e = tr_ind_call x ic_e in
          SL_seg (ic, lv, ic_e, lv_e), x
      | SL_array -> SL_array, x
    let assume (op: memh_log_form) (x: t): t =
      let op, x = prep_log_form "assume" x op in D.assume op x
    let check (op: memh_log_form) (x: t): bool =
      let op, x = prep_log_form "check" x op in D.check op x
  end: DOM_MEM_EXPRS)


(** Timer instance of the dom_mem_exprs domain (act as a functor on top
 ** of the domain itself) *)
module Dom_mem_exprs_timing = functor (D: DOM_MEM_EXPRS) ->
  (struct
    module T = Timer.Timer_Mod( struct let name = "Mem_exprs" end )
    type t = D.t
    let init_inductives = T.app2 "init_inductives" D.init_inductives
    let inductive_is_allowed = T.app1 "ind_is_allowed"D.inductive_is_allowed
    let sve_sync_bot_up = T.app1 "sve_sync_bot_up" D.sve_sync_bot_up
    let bot = D.bot
    let is_bot = T.app1 "is_bot" D.is_bot
    let top = T.app1 "top" D.top
    let t_2stri = T.app2 "t_2stri" D.t_2stri
    let t_2str = T.app1 "t_2str" D.t_2str
    let ext_output = T.app4 "ext_output" D.ext_output
    let gc = T.app2 "gc" D.gc
    let is_le = T.app4 "is_le" D.is_le
    let join = T.app7 "join" D.join
    let directed_weakening = T.app5 "weaken" D.directed_weakening
    let local_abstract = T.app2 "local_abstract" D.local_abstract
    let assign = T.app3 "assign" D.assign
    let guard = T.app3 "guard" D.guard
    let encode = T.app3 "encode" D.encode
    let sat = T.app2 "sat" D.sat
    let create_mem_var = T.app2 "create_mem_var" D.create_mem_var
    let delete_mem_var = T.app2 "delete_mem_var" D.delete_mem_var
    let memory = T.app2 "memory" D.memory
    let gen_setvar = T.app2 "gen_setvar" D.gen_setvar
    let del_setvar = T.app2 "del_setvar" D.del_setvar
    let assume = T.app2 "assume" D.assume
    let check = T.app2 "check" D.check
    let ind_unfold = T.app3 "ind_unfold" D.ind_unfold
  end: DOM_MEM_EXPRS)
