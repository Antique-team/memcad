(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_node.ml
 **       lifting of a numerical domain into an array abstraction
 ** Jiangchao Liu 2014/09/23 *)
open Data_structures
open Flags
open Lib
open Offs

open Dom_sig
open C_sig
open Ast_sig
open Nd_sig
open Svenv_sig
open Sv_sig
open List_sig
open Array_ppred_sig
open Array_ind_sig

open List_utils
open Dom_utils
open Nd_utils
open Dom_val_maya

open List_utils
open Array_ppred_utils
open Array_ind_utils

(* Apron library needed here *)
open Apron

(* Materialization environment *)
let mat_left: bool ref = ref false
let mat_guard: bool ref = ref true
let mater_id: (IntSet.t * IntSet.t) ref =  ref (IntSet.empty, IntSet.empty)
let mat_var:  ((VarSet.t * VarSet.t) IntMap.t) ref = ref (IntMap.empty)
let varm: (int * typ) VarMap.t ref = ref VarMap.empty

(** Error report *)
module Log =
  Logger.Make(struct let section = "a_node___" and level = Log_level.DEBUG end)

(** Size and index dimensions  *)
let g_index = -2
let g_size = -1

(** Fresh names for groups *)
let group_counter: int ref = ref (-1)
let get_new_group () =
  group_counter := !group_counter + 1;
  !group_counter


(** Fresh names of dimensions associated with array cells,todo:
 ** a better nameing scheme  *)
let dimension_counter: int ref = ref 10000000
let get_new_dim () =
  if !dimension_counter = 100000000 then
    Log.fatal_exn "dimension_counter limit reached"
  else
    dimension_counter := !dimension_counter + 1;
  !dimension_counter

(** Temp names for dimensions on array cells,
 ** used in transfer functions on summarizing dimensions  *)
let tmp_dimension_counter: int ref = ref 100000000
let get_tmp_dim () =
  tmp_dimension_counter := !tmp_dimension_counter + 1;
  !tmp_dimension_counter
let tmp_dim_reset  () =
  tmp_dimension_counter := 100000000



module T = Timer.Timer_Mod( struct let name = "Array" end)

(** A functor that describes the properties of an array **)
module Array_Node (Op: DOM_MAYA) =
  struct
    (** This module is about the information and operation on array node.
     ** For now, we just support varRe and indexRe predicates happen
     ** within an array.   *)
    type local_env = (int, int) Bi_fun.t (*From local to symbolic dimension*)

    (* Structural predicates *)
    type array_pred =
      | Pred_list of (int * lmem * local_env)
      | Pred_pure of (pmem * local_env)

    type t =
        { t_id: int;
          (* Offset of each field, starting with 1 besides g_index and g_size *)
          t_fields: int IntMap.t;
          (* Size of each cell in bytes*) (* XR: in bytes ? *)
          t_align: int;
          (* Size of this array node: number of cells *)
          t_size: int;
          (* Group names that this array in partitioned into *)
          t_groups: IntSet.t;
          (* Dimensions of each field of each group
           * starts with 2, 1 is specially used for "size", 0 for index *)
          t_dimensions: (int * int, int) Bi_fun.t;
          (* varRes: Predicating a variable may be an index of a group *)
          t_varRes: IntSet.t IntMap.t;
          (* indexRes: Predicating the value of one field in cells of a group
           * may be an index of a group *) (* XR: what is it ? *)
          t_indexRes: IntSet.t IntMap.t;
          (*Whether a group satisfies a predicate, if is does, it records the
            parameters of this predicate*)
          t_pred: array_pred IntMap.t;
          t_ref_count: int IntMap.t; }

    (** Pretty print  *)
    let t_2stri (ind: string) (x: t): string =
      let strVarRe =
        IntMap.fold
          (fun var set acc ->
            let oline =
              Printf.sprintf
                "\n |%d| <- %s \n" var (intset_2str set ) in
            acc ^ oline
          ) x.t_varRes "Variable Relations:\n" in
      let strIndexRe =
        IntMap.fold
          (fun di set acc ->
            let g, f = Bi_fun.inverse_inj di x.t_dimensions in
            let oline =
              Printf.sprintf "\n (%d, %d) <- %s \n" g f (intset_2str set) in
            acc ^ oline
          ) x.t_indexRes "Index Relations:\n" in
      let str_ref_count =
        IntMap.fold
          (fun key cou acc ->
            let astr = Printf.sprintf "%d -> %d \n" key cou in
            acc^astr
          ) x.t_ref_count "\n ref_count is\n" in
      let bi_fun_int_print =
        Bi_fun.t_2str "" (Printf.sprintf "%d") (Printf.sprintf "%d") in
      let strPred =
        IntMap.fold
          (fun key ap acc ->
            match ap with
            | Pred_list (ai, al, ae) ->
                (Printf.sprintf "In group %d \n" key)
                ^(Printf.sprintf "head is%d " ai)
                ^(lmem_2stri "" al)^"Env is:\n"
                ^(bi_fun_int_print ae)^acc
            | Pred_pure (ap, ae) ->
                (Printf.sprintf "In group %d \n" key)
                ^(pmem_2stri "" ap)^"Env is:\n"
                ^(bi_fun_int_print ae)^acc
          ) x.t_pred "" in
      Printf.sprintf "%s ---------In Array Node: |%d|--------------
        \n %d Groups: %s\n\n\n %s \n\n %s \n %s \n\n %s \n"
        ind  x.t_id (IntSet.cardinal x.t_groups) (intset_2str x.t_groups)
        strVarRe strIndexRe str_ref_count strPred


    (** Utilities *)
    let get_namer (key: int) (x: t) (base: sv_namer): sv_namer =
      let fg (g, f) =
        let strGroup = Printf.sprintf "G(%d)" g in
        let strField =
          if f = g_index then  "@index"
          else if f = g_size then "@size"
          else Printf.sprintf "@Field@%d" f in
        Printf.sprintf "%s%s" strGroup strField in
      Bi_fun.fold_dom
        (fun key dim acc -> IntMap.add dim (fg key) acc) x.t_dimensions base


    (* XR: I do not understand this comment! *)
    (* Compute the similarity of the values stored in two variables *)
    let var_compare (lv: int) (lm: Op.t) (rv: int) (rm:Op.t): int =
      let intevL = Op.bound_variable lv lm in
      let intevR = Op.bound_variable rv rm in
      let score (a: int option) b =
        match a, b with
        | None, None -> 1
        | None, Some i -> 0
        | Some i, None -> 0
        | Some i, Some j -> if i = j then 1 else 0 in
      (score intevL.intv_inf intevR.intv_inf)
        + (score intevL.intv_sup intevR.intv_sup)

    (* Apply the constraints on a variable to another varible.
     * which could be in different numeric states. *)
    let cons_copy (lv: int) (lm: Op.t) (rv: int) (rm: Op.t): Op.t =
      let intev = Op.bound_variable lv lm in
      let bound_guard bound isinf x =
        match bound with
        | None -> x
        | Some bd ->
            let cons =
              if isinf then Nc_cons (Tcons1.SUPEQ, (Ne_var rv), (Ne_csti bd))
              else Nc_cons (Tcons1.SUPEQ, (Ne_csti bd), (Ne_var rv)) in
            Op.guard_s true cons x in
      bound_guard intev.intv_inf true (bound_guard intev.intv_sup false rm)

    (* Inclusion check on two states with the same parition *)
    let flat_is_le (lx: t) (rx: t): bool =
      let compareRes lres rres =
        IntMap.fold
          (fun var set acc ->
            acc && ( not (IntMap.mem var lres)
                   || IntSet.subset (IntMap.find var lres) set)
          ) rres true in
      let varc = compareRes lx.t_varRes rx.t_varRes in
      let indc = compareRes lx.t_indexRes rx.t_indexRes in
      varc && indc

    (* Join function for two states with the same partition *)
    let flat_join (lx: t) (rx: t): t =
      let set_join key ls rs =
        match ls, rs with
        | None, _ -> None
        | _, None -> None
        | Some l, Some r -> Some (IntSet.union l r) in
      let nvarRes = IntMap.merge set_join lx.t_varRes rx.t_varRes in
      let nindexres = IntMap.merge set_join lx.t_indexRes rx.t_indexRes in
      { lx with
        t_varRes   = nvarRes;
        t_indexRes = nindexres }

    (* Constrain numeric elements in each group on the size of each group  *)
    let nc_size (array: t) (main: Op.t): Op.t=
      let expr =
        IntSet.fold
          (fun elt expr ->
            let dim = Bi_fun.image (elt, g_size) array.t_dimensions in
            Ne_bin (Texpr1.Add, expr, Ne_var dim)
          ) array.t_groups (Ne_csti 0) in
      let idx_size_expr =
        IntSet.fold
          (fun elt expr ->
            let dim = Bi_fun.image (elt, g_index) array.t_dimensions in
            Ne_bin (Texpr1.Add, expr, Ne_var dim)
          ) array.t_groups (Ne_csti 0) in
      let idx_cons =
        Nc_cons (Tcons1.SUPEQ, Ne_csti array.t_size, idx_size_expr) in
      let cons = Nc_cons (Tcons1.SUPEQ, Ne_csti array.t_size, expr) in
      let main = (Op.guard_s true cons main) in
      Op.size_guard idx_cons  main

    (* Calculate the similariy of two groups within one state,
     * this function is used to help calculate whether to do "merge" *)
    let self_rankscore (x: t) (main: Op.t) (l_id: int) (r_id: int) : int =
      let idx_weight = 1 in
      let sz_weight = 1 in
      let fld_weight = 1 in
      let relation_weight = 3 in
      let result =
        IntMap.fold
          (fun key off wacc->
            let l_dim = Bi_fun.image (l_id, key) x.t_dimensions in
            let r_dim = Bi_fun.image (r_id, key) x.t_dimensions in
            let fld_score =
              fld_weight * (var_compare l_dim main r_dim main) in
            (* new code *)
            let l_set =
              try IntMap.find l_dim x.t_indexRes
              with Not_found -> IntSet.empty in
            let r_set =
              try IntMap.find r_dim x.t_indexRes
              with Not_found -> IntSet.empty in
            let relation_score = if IntSet.equal l_set r_set then 1 else 0 in
            wacc + fld_score + relation_score * relation_weight
          ) x.t_fields 0 in
      let lsz_dim = Bi_fun.image (l_id, g_size) x.t_dimensions in
      let lidx_dim = Bi_fun.image (l_id, g_index) x.t_dimensions in
      let rsz_dim = Bi_fun.image (r_id, g_size) x.t_dimensions in
      let ridx_dim = Bi_fun.image (r_id, g_index) x.t_dimensions in
      let sz_score = sz_weight * (var_compare lsz_dim main rsz_dim main) in
      let idx_score =
        idx_weight * (var_compare lidx_dim main ridx_dim main) in
      let cons = Nc_cons (Tcons1.EQ, Ne_var lidx_dim, Ne_var ridx_dim) in
      let idx_score =
        if Op.is_bot (Op.guard_s true cons main) then 0
        else idx_score in
      result + sz_score + idx_score

    (** Management of symbolic variables *)
    let sve_add (l_var: int) (nt: ntyp)
        (sve_env: local_env * (int IntMap.t) * t * Op.t) =
      let lenv, refc, x, main = sve_env in
      try
        let g_var = Bi_fun.image l_var lenv in
        if IntMap.mem g_var refc then
          lenv, IntMap.add g_var ((IntMap.find g_var refc) + 1) refc, x, main
        else
          lenv, IntMap.add g_var 1 refc, x,
          Op.add_node g_var false 1 (Some 1) main
      with
        Not_found ->
          let g_var = get_new_dim () in
          (Bi_fun.add l_var g_var lenv),
          (IntMap.add g_var 1 refc), x,
          (Op.add_node g_var false 1 (Some 1) main)

    let sve_rem (l_var: int) (sve_env: local_env * (int IntMap.t) * t * Op.t) =
      let lenv, refc, x, main = sve_env in
      assert (Bi_fun.mem_dir l_var lenv);
      let g_var = Bi_fun.image l_var lenv in
      let lenv = Bi_fun.rem_dir l_var lenv in
      let cou =
        try IntMap.find g_var refc
        with | Not_found -> Log.fatal_exn "predicate enviroment inconsitent" in
      if cou <= 1 then
        lenv,
        IntMap.remove g_var refc,
        { x with t_varRes = IntMap.remove g_var x.t_varRes },
        Op.rem_node g_var main
      else
        lenv, IntMap.add g_var (cou - 1) refc, x, main

    let sve_mod (l_var: int) (acc: 'a) = acc

    let sve_fix (msg: string) (main: Op.t) (x: t): Op.t * t =
      let tpreds, grefc, x, main =
        IntMap.fold
          (fun key apred (itpreds, irefc, ix, im) ->
            match apred with
            | Pred_list (ai, alm, alenv) ->
                let lm, svm = List_utils.sve_sync_bot_up alm in
                let alenv, irefc, ix, im =
                  svenv_mod_doit sve_add sve_rem sve_mod svm
                    (alenv, irefc, ix, im) in
                IntMap.add key (Pred_list (ai, lm, alenv)) itpreds,
                irefc, ix, im
            | Pred_pure (apm, alenv) ->
                let alenv, irefc, ix, im =
                  svenv_mod_doit sve_add sve_rem sve_mod apm.pm_svemod
                    (alenv, irefc, ix, im) in
                let apm = { apm with pm_svemod = Dom_utils.svenv_empty } in
                (IntMap.add key (Pred_pure (apm, alenv)) itpreds), irefc, ix, im
          ) x.t_pred (x.t_pred, x.t_ref_count, x, main) in
      main, { x with t_pred = tpreds; t_ref_count = grefc }

    (** Program variables used as symbolic variables in inductive instances *)
    let preprocess_pro_var (var: int) (refc: int IntMap.t) =
      if IntMap.mem var refc then refc
      else IntMap.add var 1 refc

    (* Calculate the similarity of each group from two states *)
    let rankscore (is_var: int -> bool) (lx: t) (lm: Op.t) (rx: t) (rm: Op.t)
        (lmap: int IntMap.t) (rmap: int IntMap.t) : (int * int * int) list =
      let idx_weight = 1 in
      let sz_weight = 1 in
      let fld_weight = 1 in
      let name_weight = (IntMap.cardinal lx.t_fields) * 10 in
      let fresh_name_weight = 3 in
      let pred_match = 100 in
      let pred_unmatch = 0 in
      let var_weight = 1 in
      (* The number of variables that store indexes from both groups *)
      let varRank (lx: t) (rx: t) (l_id: int) (r_id: int): int =
        IntMap.fold
          (fun key lset acc ->
            if IntMap.mem key rx.t_varRes then
              let rset = IntMap.find key rx.t_varRes in
              if IntSet.mem l_id lset && IntSet.mem r_id rset then acc + 1
              else acc
            else acc
          ) lx.t_varRes 0 in
      IntSet.fold
        (fun lg_id lacc ->
          let lsz_dim = Bi_fun.image (lg_id, g_size) lx.t_dimensions in
          let lidx_dim = Bi_fun.image (lg_id, g_index) lx.t_dimensions in
          IntSet.fold
            (fun rg_id racc ->
              match IntMap.mem lg_id lmap, IntMap.mem rg_id rmap with
              | true, true ->
                  if rg_id = IntMap.find lg_id lmap then
                    (lg_id, rg_id, pred_match) :: racc
                  else
                    (lg_id, rg_id, pred_unmatch) :: racc
              | true, false
              | false, true ->
                  (lg_id, rg_id, pred_unmatch) :: racc
              | false, false ->
                  let total =
                    match IntSet.mem lg_id rx.t_groups,
                      IntSet.mem rg_id lx.t_groups with
                    | true, false ->
                        (self_rankscore rx rm lg_id rg_id)
                          + (varRank lx rx lg_id rg_id)
                    | false, true ->
                        (self_rankscore lx lm rg_id lg_id)
                          + (varRank lx rx lg_id rg_id)
                    | _ ->
                        let result =
                          IntMap.fold
                            (fun key off wacc->
                              let lg_dim =
                                Bi_fun.image (lg_id, key) lx.t_dimensions in
                              let rg_dim =
                                Bi_fun.image (rg_id, key) rx.t_dimensions in
                              let fld_score =
                                fld_weight
                                  * (var_compare lg_dim lm rg_dim rm) in
                              wacc + fld_score
                            ) lx.t_fields 0 in
                        let rsz_dim =
                          Bi_fun.image (rg_id, g_size) rx.t_dimensions in
                        let ridx_dim =
                          Bi_fun.image (rg_id, g_index) rx.t_dimensions in
                        let sz_score =
                          sz_weight * var_compare lsz_dim lm rsz_dim rm in
                        let idx_score =
                          idx_weight * var_compare lidx_dim lm ridx_dim rm in
                        let result = result + sz_score + idx_score in
                        let result =
                          if lg_id = rg_id then result + name_weight
                          else result in
                        let var_score =
                          IntMap.fold
                            (fun v lgs vacc ->
                              if is_var v && var_compare v lm v rm = 2
                                  && (IntMap.mem v rx.t_varRes)
                                  && (IntSet.mem lg_id lgs) then
                                let rgs = IntMap.find v rx.t_varRes in
                                if (IntSet.mem rg_id rgs) then
                                  vacc + var_weight
                                else vacc
                              else vacc
                            ) lx.t_varRes 0 in
                        let freshl = not (IntSet.mem lg_id rx.t_groups) in
                        let freshr = not (IntSet.mem rg_id lx.t_groups) in
                        let result =
                          if freshl && freshr then
                            result + fresh_name_weight
                          else
                            result in
                        let result = result + var_score in
                        result in
                  (lg_id, rg_id, total) :: racc
            ) rx.t_groups lacc
        ) lx.t_groups []

    (* Split:
     * Split several elements from one group to form a new group,
     * the properties of the new group inherit the splitted group. *)
    let split (get_dim: unit -> int ) (g_id: int) (ng_id: int)
        (var: int option) (num: int option) (main: Op.t) (x: t): Op.t * t =
      let index_dim = get_dim () in
      let size_dim = get_dim () in
      let dimensions = Bi_fun.add (ng_id, g_index) index_dim x.t_dimensions in
      let dimensions = Bi_fun.add (ng_id, g_size) size_dim dimensions in
      let dimensions =
        IntMap.fold
          (fun key _ acc ->
            Bi_fun.add (ng_id, key) (get_dim ()) acc
          ) x.t_fields dimensions in
      let ngroups = IntSet.add ng_id x.t_groups in
      let ori_index_dim = Bi_fun.image (g_id, g_index) x.t_dimensions in
      let ori_size_dim = Bi_fun.image (g_id, g_size) x.t_dimensions in
      let main = Op.add_node index_dim true 1 (Some 1) main in
      let main = Op.add_node size_dim false 1 (Some 1) main in
      (*These code has been changed, check here if bug happens  *)
      let tmp_var = get_dim () in
      let main = Op.add_node tmp_var false 1 (Some 1) main in
      let main =
        match num with
        | None ->
            let tm =
              Op.guard_s true
                (Nc_cons (Tcons1.SUPEQ, Ne_var tmp_var, Ne_csti 0))
                main in
            Op.guard_s true
              (Nc_cons (Tcons1.SUP, Ne_csti x.t_size, Ne_var tmp_var)) tm
        | Some rm -> Op.update_subs_elt tmp_var (Ne_csti rm) main in
      let frsh_agn_expr = Ne_var tmp_var in
      let main = Op.update_subs_elt size_dim frsh_agn_expr main in
      let main = Op.size_assign index_dim frsh_agn_expr main in
      let old_agn_expr =
        Ne_bin (Texpr1.Sub, Ne_var ori_size_dim, Ne_var tmp_var) in
      let main = Op.update_subs_elt ori_size_dim old_agn_expr main in
      let old_size_cons =
        Nc_cons (Tcons1.SUPEQ, Ne_var ori_size_dim, Ne_csti 0) in
      let main = Op.guard_s true old_size_cons main in
      let main =
        match var with
        | None ->
            let old_inx_expr =
              Ne_bin (Texpr1.Sub, Ne_var ori_index_dim, Ne_var tmp_var) in
            Op.size_assign ori_index_dim old_inx_expr main
        | Some v ->
            let tmain = Op.update_rem ori_index_dim (Ne_var v) main in
            if num = Some 1 then
              let idxequal = Nc_cons (Tcons1.EQ, Ne_var index_dim, Ne_var v) in
              Op.guard_s true idxequal tmain
            else tmain in
      let main = Op.rem_node tmp_var main in
      let main =
        IntMap.fold
          (fun key _ acc ->
            let ori_fld_dim = Bi_fun.image (g_id, key) dimensions in
            let frsh_fld_dim = Bi_fun.image (ng_id, key) dimensions in
            let acc = Op.expand ori_fld_dim frsh_fld_dim acc in
            if num = Some 1 then
              Op.scalar_to_single frsh_fld_dim  acc
            else
              acc
          ) x.t_fields main in
      (* can be more precise by comparing the index of new group and each var *)
      let refreshS elt =
        if IntSet.mem g_id elt then IntSet.add ng_id elt
        else elt in
      (* let nvarRes = IntMap.map refreshS x.t_varRes in *)
      let nvarRes =
        IntMap.fold
          (fun iv is acc ->
            if IntSet.mem g_id is then
              match var with
              | Some v ->
                  if Op.sat_s main
                      (Nc_cons (Tcons1.EQ, (Ne_var iv), (Ne_var v))) then
                    IntMap.add iv (IntSet.singleton ng_id) acc
                  else
                    IntMap.add iv (IntSet.add ng_id is) acc
              | None -> IntMap.add iv (IntSet.add ng_id is) acc
            else acc
          ) x.t_varRes x.t_varRes in
      let nindexRes = IntMap.map refreshS x.t_indexRes in
      let nindexRes =
        IntMap.fold
          (fun key _ acc ->
            let ori_fld_dim = Bi_fun.image (g_id, key) dimensions in
            if IntMap.mem ori_fld_dim acc then
              let tSet = IntMap.find ori_fld_dim acc in
              let new_fld_dim = Bi_fun.image (ng_id, key) dimensions in
              IntMap.add new_fld_dim tSet acc
            else acc
          ) x.t_fields nindexRes in
      let nvarRes =
        match var with
        | None -> nvarRes
        | Some v ->
            let nvarR = IntMap.add v (IntSet.singleton ng_id) nvarRes in
            let eq_cl = Op.get_eq_class v main in
            let eq_cl =
              IntSet.filter
                (fun adim -> not (Bi_fun.mem_inv adim dimensions)) eq_cl in
            IntSet.fold
              (fun key acc ->
                IntMap.add key (IntSet.singleton ng_id) acc
              ) eq_cl nvarR in
      main, { x with
              t_groups = ngroups;
              t_indexRes = nindexRes;
              t_varRes = nvarRes;
              t_dimensions = dimensions; }

    (* Operator Merge:
     * Merge two groups into one group, the properties of the new group is the
     * over-approximation of the two old groups*)
    let merge (gl: int) (gr: int) (x: t) (main: Op.t): t * Op.t =
      let merge_dim (key: int) (m: Op.t)=
        let l_fld_dim = Bi_fun.image (gl, key) x.t_dimensions in
        let r_fld_dim = Bi_fun.image (gr, key) x.t_dimensions in
        Op.compact l_fld_dim r_fld_dim m in
      let main =
        IntMap.fold (fun key _ acc -> merge_dim key acc) x.t_fields main in
      let l_sz_dim = Bi_fun.image (gl, g_size) x.t_dimensions in
      let r_sz_dim = Bi_fun.image (gr, g_size) x.t_dimensions in
      let sz_expr = Ne_bin (Texpr1.Add, Ne_var l_sz_dim, Ne_var r_sz_dim) in
      let main = Op.update_subs_elt l_sz_dim sz_expr main in
      let main = Op.rem_node r_sz_dim main in
      let main = merge_dim g_index main in
      let refreshS elt =
        if IntSet.mem gr elt then
          IntSet.add gl (IntSet.remove gr elt)
        else elt in
      let nvarRes = IntMap.map refreshS x.t_varRes in
      let nindexRes = IntMap.map refreshS x.t_indexRes in
      let nindexRes =
        IntMap.fold
          (fun key _ acc ->
            let l_fld_dim = Bi_fun.image (gl, key) x.t_dimensions in
            let r_fld_dim = Bi_fun.image (gr, key) x.t_dimensions in
            if IntMap.mem r_fld_dim nindexRes then
              let r_set = IntMap.find r_fld_dim acc in
              let acc =
                if IntMap.mem l_fld_dim nindexRes then
                  let l_set = IntMap.find l_fld_dim acc in
                  IntMap.add l_fld_dim (IntSet.union l_set r_set) acc
                else
                  IntMap.add l_fld_dim  r_set acc in
              IntMap.remove r_fld_dim acc
            else acc
          ) x.t_fields nindexRes in
      let ndimensions =
        IntMap.fold
          (fun key _ acc ->
            Bi_fun.rem_dir (gr, key) acc
          ) x.t_fields x.t_dimensions in
      let ndimensions = Bi_fun.rem_dir (gr, g_size) ndimensions in
      let ndimensions = Bi_fun.rem_dir (gr, g_index) ndimensions in
      let ngroups = IntSet.remove gr x.t_groups in
      let x =
        { x with
          t_groups = ngroups ;
          t_dimensions = ndimensions;
          t_varRes = nvarRes ;
          t_indexRes = nindexRes; } in
      x, nc_size x main

    (* Operator Create:
     * Create a new group of 0 elements, all its properties are from
     * model (the corresponding group in join algorithm). *)
    let create (fresh: int) (model: int)  (x: t) (main: Op.t)
        (model_x: t) (model_m: Op.t): t * Op.t  =
      let index_dim = get_new_dim () in
      let size_dim = get_new_dim () in
      let ndimensions = Bi_fun.add (fresh, g_size) size_dim x.t_dimensions in
      let ndimensions = Bi_fun.add (fresh, g_index) index_dim ndimensions in
      let cons_size = Nc_cons (Tcons1.EQ, Ne_var size_dim, (Ne_csti 0)) in
      let main = Op.add_node size_dim  false 1 (Some 1) main in
      let main = Op.add_node index_dim  true  0 (Some 0) main in
      let main = Op.guard_s true cons_size main in
      let ndimensions, main =
        IntMap.fold
          (fun key _ (tdimensions, tmain) ->
            let ndim = get_new_dim () in
            (* caution: the constraints from model_m may not be recorded *)
            let tmain = Op.add_node ndim false 0 (Some 0) tmain in
            let odim = Bi_fun.image (model, key) model_x.t_dimensions in
            let tdimensions =
              Bi_fun.add (fresh, key) ndim tdimensions in
            let tmain = cons_copy odim model_m ndim tmain in
            tdimensions, tmain
          ) x.t_fields (ndimensions, main) in
      let ngroups = IntSet.add fresh x.t_groups in
      let nindexRes =
        IntMap.fold
          (fun key off acc ->
            let dim = Bi_fun.image (fresh, key) ndimensions in
            IntMap.add dim IntSet.empty acc
          ) x.t_fields x.t_indexRes in
      { x with
        t_groups = ngroups;
        t_indexRes = nindexRes;
        t_dimensions = ndimensions;}, main

    (* Attach a structrual predicate to a group if it has only cell *)
    let sing_2segorlist (ldef: l_def) (group: int) (t: t) (main: Op.t)
        : Op.t * t * bool =
      if IntMap.mem group t.t_pred then
        main, t, true
      else
        begin
          Log.warn "special off here";
          let indx_dim = Bi_fun.image (group, g_index) t.t_dimensions in
          let off_dim = Bi_fun.image (group, 1) t.t_dimensions in
          let emp_cons =
            Nc_cons (Tcons1.EQ, Ne_var off_dim, Ne_csti ldef.ld_emp_csti) in
          let local_h, alist = List_utils.sv_add_fresh
              ~root:true Ntaddr List_utils.lmem_empty in
          let h_dim = get_new_dim () in
          let main = Op.add_node h_dim false 1 (Some 1) main in
          let main = Op.guard_s true (Nc_cons (Tcons1.EQ, Ne_var indx_dim, Ne_var h_dim)) main in
          let l_env = Bi_fun.add local_h h_dim Bi_fun.empty_inj in
          let ref_c = IntMap.add h_dim 0 t.t_ref_count in
          let lc = {lc_def = ldef; lc_args = [] } in
          if Op.sat_s main emp_cons then
            let alist = List_utils.list_edge_add local_h lc alist in
            let main, x =
              sve_fix "" main
                { t with
                  t_pred = IntMap.add group
                    (Pred_list (local_h, alist, l_env)) t.t_pred;
                  t_ref_count = ref_c } in
            main, x, false
          else
            let local_e, alist = List_utils.sv_add_fresh
                ~root:true Ntaddr alist in
            let e_dim = get_new_dim () in
            let main = Op.add_node e_dim false 1 (Some 1) main in
            let main =
              Op.guard_s true
                (Nc_cons (Tcons1.EQ, Ne_var off_dim, Ne_var e_dim)) main in
            let l_env = Bi_fun.add local_e e_dim l_env in
            let ref_c = IntMap.add e_dim 0 ref_c in
            let alist = List_utils.lseg_edge_add local_h local_e lc alist in
            let main, x =
              sve_fix "" main
                { t with t_pred = IntMap.add group
                    (Pred_list (local_h, alist, l_env)) t.t_pred;
                  t_ref_count = ref_c } in
            main, x, true
        end

    (* Attach a predicate to newly created empty group  *)
    let create_pred (ldef: l_def) (model: int)  (x: t) (main: Op.t) (model_x: t)
        (model_m: Op.t) (eq_var: int -> Op.t -> IntSet.t)
        : (t * Op.t * int) option =
      let get_nlenv (lenv: (int, int) Bi_fun.t) =
        Bi_fun.fold_dom
          (fun local glo (flag, realmap) ->
            let vars = eq_var glo model_m in
            if not flag || IntSet.is_empty vars then
              false, realmap
            else
              flag, (Bi_fun.add local (IntSet.min_elt vars) realmap)
          ) lenv (true, lenv) in
      let model_m, model_x, _ =
        if (IntMap.mem model model_x.t_pred) then model_m, model_x, true
        else sing_2segorlist ldef model model_x model_m in
      match IntMap.find model model_x.t_pred with
      | Pred_list (ai, lm, lenv) ->
          let eq_cl = eq_var (Bi_fun.image ai lenv) model_m in
          assert (not (IntSet.is_empty eq_cl));
          let var_h = IntSet.min_elt eq_cl in
          let empty_cons =
            Nc_cons (Tcons1.EQ, Ne_var var_h, Ne_csti ldef.ld_emp_csti) in
          if  Op.sat_s main empty_cons then
            let ng = get_new_group () in
            let x, m = create ng model x main  model_x model_m  in
            let alist = List_utils.sv_add ai
                  ~root:true Ntaddr List_utils.lmem_empty in
            let nenv = Bi_fun.add ai var_h Bi_fun.empty_inj in
            let ref_c = preprocess_pro_var var_h x.t_ref_count in
            let lc = {lc_def = ldef; lc_args = [] } in
            let alist = List_utils.list_edge_add ai lc alist in
            let m, x =
              sve_fix "" m { x with
                             t_pred = IntMap.add ng
                               (Pred_list (ai, alist, nenv)) x.t_pred;
                             t_ref_count = ref_c }
            in Some (x, m, ng)
          else None
      | Pred_pure (pm, lenv) ->
          let flag, nlenv = get_nlenv lenv in
          if not flag then
            None
          else
            let unfold_result =
              Array_ppred_utils.unfold pm in
            let is_empty =
              List.fold_left
                (fun acc pr ->
                  match pr.pu_pr_type with
                  | PURE_EMPTY ->
                      let nconsl = List.map
                          (n_cons_map (fun key -> Bi_fun.image key nlenv))
                          pr.pu_pr_cons in
                      let is_emp =
                        List.fold_left
                          (fun iac acon -> iac && Op.sat_s main acon
                          ) true nconsl in
                      is_emp || acc
                    | PURE_TRUE ->
                        true
                    | PURE_SINGLE ->
                        acc
                 ) false unfold_result in
            if is_empty then
              let ng = get_new_group () in
              let nx, nm = create ng model x main  model_x model_m in
              let _, refc, nx, nm =
                Bi_fun.fold_dom
                  (fun key _ acc ->
                    sve_add key Ntaddr acc
                   ) nlenv  (nlenv, x.t_ref_count, nx, nm) in
              Some ({ nx with
                      t_ref_count = refc;
                      t_pred = IntMap.add ng (Pred_pure (pm, nlenv)) nx.t_pred},
                    nm, ng)
            else None

    (* Operator Rename:
     * Give a fresh name to a group. This operator is used to make
     * groups in two states have the same set of names*)
    let rename_group (lold: int) (rold: int) (fresh: int) (lm:Op.t) (lx: t)
        (rm: Op.t) (rx: t): Op.t * t * Op.t * t =
      let index_dim = get_new_dim () in
      let size_dim = get_new_dim () in
      let update_spcl old fresh sdim idim m x =
        let osize_dim = Bi_fun.image (old, g_size) x.t_dimensions in
        let oindex_dim = Bi_fun.image (old, g_index) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old, g_size) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old, g_index) ndimens in
        let ndimens = Bi_fun.add (fresh, g_size) size_dim ndimens in
        let ndimens = Bi_fun.add (fresh, g_index) index_dim ndimens in
        let nm = Op.rename_var osize_dim sdim m in
        let nm = Op.rename_var oindex_dim idim nm in
        let x = { x with t_dimensions = ndimens } in
        nm, x in
      let lm, lx = update_spcl lold fresh size_dim index_dim lm lx in
      let rm, rx = update_spcl rold fresh size_dim index_dim  rm rx in
      let fldim =
        IntMap.fold (fun key off acc -> IntMap.add key (get_new_dim ()) acc)
          lx.t_fields IntMap.empty in
      let update_fld old fresh fd m x =
        let ndimens, nm, nidxRes =
          IntMap.fold
            (fun key dim (tdimens, tm, tidxRes) ->
              let odim = Bi_fun.image (old, key) tdimens in
              let tdimens = Bi_fun.rem_dir (old, key) tdimens in
              let tdimens = Bi_fun.add (fresh, key) dim tdimens in
              let tm = Op.rename_var odim dim tm in
              let tidxRes =
                if IntMap.mem odim tidxRes then
                  let g = IntMap.find odim tidxRes in
                  let tidxRes = IntMap.remove odim tidxRes in
                  IntMap.add dim g tidxRes
                else
                  tidxRes in
              (tdimens, tm, tidxRes)
            ) fd (x.t_dimensions, m, x.t_indexRes) in
        nm, { x with
              t_dimensions = ndimens;
              t_indexRes   = nidxRes; } in
      let lm, lx = update_fld lold fresh fldim lm lx in
      let rm, rx = update_fld rold fresh fldim rm rx in
      let re_in_group old fresh gp =
        if IntSet.mem old gp then
          let gp = IntSet.remove old gp in IntSet.add fresh gp
        else gp in
      let lngroups = re_in_group lold fresh lx.t_groups in
      let rngroups = re_in_group rold fresh rx.t_groups in
      let lnvarRes = IntMap.map (re_in_group lold fresh) lx.t_varRes in
      let rnvarRes = IntMap.map (re_in_group rold fresh) rx.t_varRes in
      let lnidxRes = IntMap.map (re_in_group lold fresh) lx.t_indexRes in
      let rnidxRes = IntMap.map (re_in_group rold fresh) rx.t_indexRes in
      let refresh_pred (og: int) (ng: int) (ox: t) =
        if IntMap.mem og ox.t_pred then
          let apred = IntMap.find og ox.t_pred in
          let npred = IntMap.add ng apred (IntMap.remove og ox.t_pred) in
          { ox with t_pred = npred }
        else ox in
      let lx = refresh_pred lold fresh lx in
      let rx = refresh_pred rold fresh rx in
      let lx = { lx with
                 t_groups = lngroups ;
                 t_varRes = lnvarRes ;
                 t_indexRes = lnidxRes } in
      let rx = { rx with
                 t_groups = rngroups ;
                 t_varRes = rnvarRes ;
                 t_indexRes = rnidxRes } in
      lm, lx, rm, rx

    (* The only difference between rename_group_in_le and rename_group is
     * that is uses temporary dimension names  *)
    let rename_group_in_le (lold: int) (rold: int) (fresh: int) (lm:Op.t)
        (lx: t) (rm: Op.t) (rx: t): Op.t * t * Op.t * t =
      let size_dim = get_tmp_dim () in
      let index_dim = get_tmp_dim () in
      let update_spcl old fresh m x =
        let osize_dim = Bi_fun.image (old, g_size) x.t_dimensions in
        let oindex_dim = Bi_fun.image (old, g_index) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old, g_size) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old, g_size) ndimens in
        let ndimens = Bi_fun.add (fresh, g_size) size_dim ndimens in
        let ndimens = Bi_fun.add (fresh, g_index) index_dim ndimens in
        let nm = Op.rename_var osize_dim size_dim m in
        let nm = Op.rename_var oindex_dim index_dim nm in
        let x = { x with t_dimensions = ndimens } in
        nm, x in
      let lm, lx = update_spcl lold fresh lm lx in
      let rm, rx = update_spcl rold fresh rm rx in
      let fldim =
        IntMap.fold (fun key off acc -> IntMap.add key (get_tmp_dim ()) acc)
          lx.t_fields IntMap.empty in
      let update_fld old fresh fd m x =
        let ndimens, nm, nidxRes =
          IntMap.fold
            (fun key dim (tdimens, tm, tidxRes) ->
              let odim = Bi_fun.image (old, key) tdimens in
              let tdimens = Bi_fun.rem_dir (old, key) tdimens in
              let tdimens = Bi_fun.add (fresh, key) dim tdimens in
              let tm = Op.rename_var odim dim tm in
              let tidxRes =
                if IntMap.mem odim tidxRes then
                  let g = IntMap.find odim tidxRes in
                  let tidxRes = IntMap.remove odim tidxRes in
                  IntMap.add dim g tidxRes
                else
                  tidxRes in
              (tdimens, tm, tidxRes)
            ) fd (x.t_dimensions, m, x.t_indexRes) in
        let x = { x with
                  t_dimensions = ndimens;
                  t_indexRes = nidxRes; } in
        nm, x in
      let lm, lx = update_fld lold fresh fldim lm lx in
      let rm, rx = update_fld rold fresh fldim rm rx in
      let re_in_group old fresh gp =
        if IntSet.mem old gp then
          IntSet.add fresh (IntSet.remove old gp)
        else
          gp in
      let lngroups = re_in_group lold fresh lx.t_groups in
      let rngroups = re_in_group rold fresh rx.t_groups in
      let lnvarRes = IntMap.map (re_in_group lold fresh) lx.t_varRes in
      let rnvarRes = IntMap.map (re_in_group rold fresh) rx.t_varRes in
      let lnidxRes = IntMap.map (re_in_group lold fresh) lx.t_indexRes in
      let rnidxRes = IntMap.map (re_in_group rold fresh) rx.t_indexRes in
      let refresh_pred (og: int) (ng: int) (ox: t) =
        if IntMap.mem og ox.t_pred then
          let apred = IntMap.find og ox.t_pred in
          let npred = IntMap.add ng apred (IntMap.remove og ox.t_pred) in
          { ox with t_pred = npred }
        else  ox in
      let lx = refresh_pred lold fresh lx in
      let rx = refresh_pred rold fresh rx in
      let lx = { lx with
                 t_groups = lngroups ;
                 t_varRes = lnvarRes ;
                 t_indexRes = lnidxRes;} in
      let rx = { rx with
                 t_groups = rngroups ;
                 t_varRes = rnvarRes ;
                 t_indexRes = rnidxRes;} in
      lm, lx, rm, rx


    (* Unfold result for inductive predicates *)
    type sub_unfold_result =
        { sur_is_empty: bool;
          sur_is_mater: bool;
          sur_is_single: bool;
          sur_rem_var: (int, int) Bi_fun.t;
          sur_maya_off: int list;
          sur_pred: array_pred option;
          sur_vmap: (int, int) Bi_fun.t;
          sur_mcons: mform list; }

    (* A base unfold result *)
    let sub_no_unfold =
      { sur_is_empty = false;
        sur_is_mater = false;
        sur_is_single = false;
        sur_maya_off = [];
        sur_rem_var = Bi_fun.empty_inj;
        sur_pred  = None;
        sur_vmap = Bi_fun.empty_inj;
        sur_mcons = []; }

    (* Unfold an inductive predicate attached to a group  *)
    let unfold_at_group (group: int)  (x: t) (main: Op.t): sub_unfold_result =
      if not (IntMap.mem group x.t_pred) then
        sub_no_unfold
      else
        match IntMap.find group x.t_pred with
        | Pred_list (ai, lm, lenv) ->
            let ur_list = List_mat.unfold ai  false lm in
            begin
              match ur_list with
              | ur_next::ur_emp::[] ->
                  let key_map = function key -> Bi_fun.image key lenv in
                  let emp_cons = List.hd ur_emp.ur_cons in
                  let emp_cons = n_cons_map key_map emp_cons in
                  if Op.sat_s main emp_cons then
                    { sur_is_empty = true;
                      sur_is_mater = false;
                      sur_is_single = false;
                      sur_maya_off = List_utils.get_maya_off ai lm;
                      sur_pred  = None;
                      sur_rem_var = lenv;
                      sur_vmap = Bi_fun.empty_inj;
                      sur_mcons = ur_next.ur_mcons;
                    }
                  else
                    let next_cons = List.hd ur_next.ur_cons in
                    let next_cons = n_cons_map key_map next_cons in
                    if Op.sat_s main next_cons then
                      begin
                        let nlm = sv_unroot ai ur_next.ur_lmem in
                        let nlm = sv_rem ai nlm in
                        let varS = sv_col nlm in
                        let nai =
                          IntSet.fold
                            (fun key acc ->
                              if sv_is_ind key nlm then key else acc)
                            varS (-1) in
                        let nlm = sv_root nai nlm in
                        assert (not (nai = -1));
                        { sur_is_empty = false;
                          sur_is_mater = true;
                          sur_is_single = false;
                          sur_rem_var = Bi_fun.empty_inj;
                          sur_maya_off = List_utils.get_maya_off nai nlm;
                          sur_pred  = Some (Pred_list (nai, nlm, lenv));
                          sur_vmap = Bi_fun.add nai 1 Bi_fun.empty_inj;
                          sur_mcons = ur_next.ur_mcons; }
                      end
                    else
                      { sub_no_unfold with
                        sur_rem_var = lenv}
              | _ -> Log.fatal_exn "unexpected case in unfold"
            end
        | Pred_pure (pm, lenv) ->
            let purl = Array_ppred_utils.unfold pm in
            let leftp, unsat =
              List.fold_left
                (fun (ileft, iun) pur ->
                  if List.length pur.pu_pr_cons = 0 then
                    ileft, iun+1
                  else
                    let cons = List.hd pur.pu_pr_cons in
                    let key_map = function key -> Bi_fun.image key lenv in
                    let cons = n_cons_map key_map cons in
                    if Op.sat_s main cons then
                      (Some pur, iun)
                    else
                      (ileft, iun + 1)
                ) (None, 0) purl in
            let p_unfold_no_r =
              { sub_no_unfold with sur_rem_var = lenv } in
            if unsat + 1 = (List.length purl) then
              match leftp with
              | Some pmu ->
                  begin
                    match pmu.pu_pr_type with
                    | PURE_EMPTY ->
                        { p_unfold_no_r with
                          sur_is_empty = true;}
                    | PURE_SINGLE ->
                        { p_unfold_no_r with
                          sur_is_single = true;
                          sur_is_mater = true;}
                    | PURE_TRUE ->
                        begin
                          match pmu.pu_pr_pm with
                          | Some npm ->
                              { p_unfold_no_r with
                                sur_is_mater = true;
                                sur_pred = Some (Pred_pure (npm, lenv))}
                          | None ->
                              Log.fatal_exn "Pure_Ture without unfolded npm"
                        end
                  end
              | None -> Log.fatal_exn "unexpected case in unfold on pure pred"
            else
              p_unfold_no_r


    (* Unfold an inductive predicate the head
     * node of which is an program variable *)
    let unfold_at_var (var: int) (main: Op.t) (x: t)
        : int option * sub_unfold_result  =
      let is_ind (var: int) (ai: int) (main: Op.t) (lenv: local_env): bool =
        let acons =
          Nc_cons (Apron.Tcons1.EQ, Ne_var var,
                   Ne_var (Bi_fun.image ai lenv)) in
        Op.sat_s main acons in
      let opgroup =
        IntMap.fold
          (fun key ap acc ->
            match ap with
            | Pred_list (ai, _, lenv) ->
                if is_ind var ai main lenv then Some key
                else acc
            | Pred_pure (pm, lenv) ->
                begin
                  match pm.pm_mpar with
                  | Some mp ->
                      if is_ind var mp main lenv then
                        Some key
                      else
                        acc
                  | None -> acc
                end
          ) x.t_pred None in
      match opgroup with
      | Some group ->
          opgroup, unfold_at_group group x main
      | None ->
          opgroup, sub_no_unfold


    (* Applying maya constraints from unfolding *)
    let apply_mform (is_unfolding: bool) (old_group: int)
        (new_group: int option) (ml: mform list) (offs: int list)
        (x: t) (main: Op.t) =
      let tr_cb_2cons (cb: c_binop) (ex1: n_expr) (ex2: n_expr) =
        let op, ex1, ex2 =
          match cb with
          | Cbeq -> Tcons1.EQ, ex1, ex2
          | Cbne -> Tcons1.EQ, ex1, ex2
          | Cbge -> Tcons1.SUPEQ, ex1, ex2
          | Cbgt -> Tcons1.SUP, ex1, ex2
          | Cble -> Tcons1.SUPEQ, ex2, ex1
          | Cblt -> Tcons1.SUP, ex2, ex1
          | _ -> Log.fatal_exn "unsupporte bin_op in tr_cb_2cons" in
        Nc_cons (op, ex1, ex2) in
      let get_group_off (ma: formal_maya_arg) =
        match ma with
        | Fa_par_maya i ->
            Some (old_group, List.nth offs i)
        | Fa_par_nmaya i ->
            begin
              match new_group with
              | Some ng ->
                  Some (ng, List.nth offs i)
              | None -> None
            end in
      List.fold_left
        (fun accm mf ->
          match mf with
          | Ai_Mf_cardinality (ma, si) ->
              if is_unfolding then
                match get_group_off ma with
                | Some _ ->
                    let dim = Bi_fun.image (old_group, g_size) x.t_dimensions in
                    Op.guard_s true
                      (Nc_cons (Tcons1.EQ, Ne_var dim, Ne_csti si)) accm
                | None -> accm
              else accm
          | Ai_Mf_cons (bin_op, fm, ae) ->
              begin
                match get_group_off fm with
                | Some (g, off) ->
                    let roff = if off = -1 then g_index else off in
                    let dim = Bi_fun.image (old_group, roff) x.t_dimensions in
                    let rexpr =
                      match ae with
                      | Ind_sig.Ae_cst ai -> Ne_csti ai
                      | Ind_sig.Ae_var _ ->
                          Log.warn "no parser offset information";
                          Log.warn "off in maya parmeters";
                          let fr_dim = Bi_fun.image (g, roff) x.t_dimensions in
                          Ne_var fr_dim
                      | _ -> Log.todo_exn "other arithm" in
                    let cons = tr_cb_2cons bin_op (Ne_var dim) rexpr in
                    if is_unfolding then
                      Op.guard_s true cons accm
                    else if Op.sat_s accm cons then accm
                    else Op.bot
                | None -> accm
              end
          | _ -> Log.todo_exn "MF operations need to be supported"
         ) main ml

    (* Remove a group  *)
    let clean_group (g_id: int) (x: t) (m: Op.t): t * Op.t =
      let ngroups = IntSet.remove g_id x.t_groups in
      let ndimensions, dims =
        IntMap.fold
          (fun key _ acc ->
            let tndim, tdims = acc in
            let kdim = Bi_fun.image (g_id, key) tndim in
            let tndim = Bi_fun.rem_dir (g_id, key) tndim in
            let tdims = IntSet.add kdim tdims in
            tndim, tdims
          ) x.t_fields (x.t_dimensions, IntSet.empty) in
      let ndimensions = Bi_fun.rem_dir (g_id, g_size) ndimensions in
      let ndimensions = Bi_fun.rem_dir (g_id, g_index) ndimensions in
      let dim = Bi_fun.image (g_id, g_size) x.t_dimensions in
      let idx = Bi_fun.image (g_id, g_index) x.t_dimensions in
      let nindexRes =
        IntSet.fold IntMap.remove dims x.t_indexRes in
      let nindexRes = IntMap.map (IntSet.remove g_id) nindexRes in
      let nvarRes = IntMap.map (IntSet.remove g_id) x.t_varRes in
      let nmain = IntSet.fold Op.rem_node dims m in
      let nmain = Op.rem_node dim nmain in
      let nmain = Op.rem_node idx nmain in
      let refc, x, nmain =
        if IntMap.mem g_id x.t_pred then
          match IntMap.find g_id x.t_pred with
          | Pred_list (_, _, lenv)
          | Pred_pure (_, lenv) ->
              let _, irefc, ix, imain =
                Bi_fun.fold_dom (fun a _ acc -> sve_rem a acc)
                  lenv (lenv, x.t_ref_count, x, nmain) in
              irefc, ix, imain
        else x.t_ref_count, x, nmain in
      let nx = { x with
                 t_groups = ngroups;
                 t_pred = IntMap.remove g_id x.t_pred;
                 t_ref_count = refc;
                 t_dimensions = ndimensions;
                 t_indexRes = nindexRes;
                 t_varRes = nvarRes } in
      nx, nmain

    (* Remove the groups that contain 0 element *)
    let cleanup (x: t) (main: Op.t): t * Op.t =
      IntSet.fold
        (fun g_id acc ->
          let tx, tmain = acc in
          if Op.is_bot tmain then
            acc
          else
            let idx = Bi_fun.image (g_id, g_index) tx.t_dimensions in
            if Op.is_bot (Op.assert_non_empty idx main) then
              let dim = Bi_fun.image (g_id, g_size) tx.t_dimensions in
              let cons = Nc_cons (Tcons1.EQ, Ne_var dim, Ne_csti 0) in
              if not (Op.is_bot (Op.guard_s true cons tmain)) then
                clean_group g_id tx tmain
              else tx, Op.bot
            else acc
        ) x.t_groups (x, main)

    let sing_2seg (ldef: l_def) (group: int) (t: t) (main: Op.t): Op.t * t =
      if IntMap.mem group t.t_pred then main, t
      else
        let local_h, alist =
          List_utils.sv_add_fresh
            ~root:true Ntaddr List_utils.lmem_empty in
        let local_e, alist =
          List_utils.sv_add_fresh
            ~root:true Ntaddr alist in
        let h_dim = get_new_dim () in
        let e_dim = get_new_dim () in
        (* Log.warn "special off here"; *)
        let indx_dim = Bi_fun.image (group, g_index) t.t_dimensions in
        let off_dim = Bi_fun.image (group, 1) t.t_dimensions in
        let main = Op.add_node h_dim false 1 (Some 1) main in
        let main = Op.add_node e_dim false 1 (Some 1) main in
        let main =
          Op.guard_s true
            (Nc_cons (Tcons1.EQ, Ne_var indx_dim, Ne_var h_dim)) main in
        let main =
          Op.guard_s true
            (Nc_cons (Tcons1.EQ, Ne_var off_dim, Ne_var e_dim)) main in
        let l_env = Bi_fun.add local_h h_dim Bi_fun.empty_inj in
        let l_env = Bi_fun.add local_e e_dim l_env in
        let ref_c = IntMap.add h_dim 0 t.t_ref_count in
        let ref_c = IntMap.add e_dim 0 ref_c in
        let lc = {lc_def = ldef; lc_args = [] } in
        let alist = List_utils.lseg_edge_add local_h local_e lc alist in
        sve_fix "" main
          { t with
            t_pred = IntMap.add group
              (Pred_list (local_h, alist, l_env)) t.t_pred;
            t_ref_count = ref_c }

    (* Groups merging with folding on list segments *)
    let list_merge (l_g: int) (r_g: int) (x: t) (m: Op.t) =
      let opldef =
        StringMap.fold
          (fun _ adef acc ->
            match acc with
            | Some def -> acc
            | None ->
                let tm =
                  apply_mform false r_g (Some l_g) adef.ld_next_mcons
                    adef.ld_m_offs x m in
                if Op.is_bot tm then None else Some adef
          ) !array_list_ind_defs None in
      let ldef =
        match opldef with
        | Some ld -> ld
        | None -> Log.fatal_exn "folding fails" in
      let m, x, _ = sing_2segorlist ldef l_g x m in
      let m, x, _ = sing_2segorlist ldef r_g x m in
      match IntMap.find l_g x.t_pred, IntMap.find r_g x.t_pred with
      | Pred_list (lai, llm, lenv), Pred_list (rai, rlm, renv) ->
          let x, m = merge l_g r_g x m in
          let mid = Bi_fun.image rai renv in
          let renv = Bi_fun.add rai (Bi_fun.image lai lenv) renv in
          let lenv = Bi_fun.add lai mid lenv in
          let apred =
            IntMap.add l_g (Pred_list (rai, rlm, renv))
              (IntMap.remove r_g x.t_pred) in
          let _, refc, x, m =
            Bi_fun.fold_dom (fun a _ acc -> sve_rem a acc)
              lenv (lenv, x.t_ref_count, x, m) in
          let rset = List_utils.lmem_reach rlm (IntSet.singleton rai) in
          let rset = IntSet.remove rai rset in
          let tail =
            if IntSet.is_empty rset then None
            else
              let at = IntSet.choose rset in
              Some (Bi_fun.image at renv) in
          { x with t_pred = apred; t_ref_count = refc }, m,
          Bi_fun.image rai renv, tail
      | _, _ -> Log.fatal_exn "list_merging groups without lists"

    (* Collect groups that the inductive predicates on them can be folded *)
    let get_pairs (ldef: l_def) (is_var: int -> bool) (ax: t) (am: Op.t):
        (int * int) IntMap.t * int IntMap.t
        * (IntSet.t * string) IntMap.t * IntSet.t =
      let off = 1 in
      IntSet.fold
        (fun key (accl, acch, accs, acci) ->
          if IntMap.mem key ax.t_pred then
            match IntMap.find key ax.t_pred with
            | Pred_list (ai, lm, lenv) ->
                let rset = List_utils.lmem_reach lm (IntSet.singleton ai) in
                let rset = IntSet.remove ai rset in
                if IntSet.is_empty rset then
                  let acch = IntMap.add key (Bi_fun.image ai lenv) acch in
                  accl, acch, accs, acci
                else
                  let at = IntSet.choose rset in
                  let accl =
                    IntMap.add (Bi_fun.image at lenv)
                      (key, (Bi_fun.image ai lenv)) accl in
                  accl, acch, accs, acci
            | Pred_pure (pm, lenv) ->
                let ipar = IntSet.of_list pm.pm_ipar in
                let name = pm.pm_def.p_name in
                let ipar =
                  match pm.pm_mpar with
                  | Some mm -> IntSet.add mm ipar
                  | None -> ipar in
                accl, acch, IntMap.add key (ipar, name) accs, acci
          else
            let sdim = Bi_fun.image (key, g_size) ax.t_dimensions in
            let inter = Op.bound_variable sdim am in
            match inter.intv_inf, inter.intv_sup with
            | Some 1, Some 1 ->
                let index_dim = Bi_fun.image (key, g_index) ax.t_dimensions in
                let off_dim = Bi_fun.image (key, off) ax.t_dimensions in
                let emp_cons =
                  Nc_cons (Tcons1.EQ, Ne_var off_dim,
                           Ne_csti ldef.ld_emp_csti) in
                let accl, acch =
                  if Op.sat_s am emp_cons then
                    accl, IntMap.add key index_dim acch
                  else
                    (IntMap.add off_dim  (key, index_dim ) accl), acch in
                accl, acch, accs, (IntSet.add key acci)
            | _ -> (accl, acch, accs, acci)
         ) ax.t_groups (IntMap.empty, IntMap.empty, IntMap.empty, IntSet.empty)

    (* Join on groups with inductive predicates *)
    let pred_join (is_widen: bool) (lx: t) (lm: Op.t) (rx: t)
        (rm: Op.t) (is_var: int -> bool)
        : t * Op.t * t * Op.t * (int IntMap.t) * (int IntMap.t) =
      let empty_pred_clean (x: t) (m: Op.t): t * Op.t =
        IntMap.fold
          (fun group _ (acc_t, acc_m) ->
            let ur_result = unfold_at_group group acc_t acc_m in
            if ur_result.sur_is_empty then
              clean_group group acc_t acc_m
            else
              acc_t, acc_m
           ) x.t_pred (x, m) in
      let empty_tail_clean (lx: t) (lm: Op.t) =
        IntMap.fold
          (fun group apred (ax, am) ->
            match apred with
            | Pred_list (ai, ll, lenv) ->
                let ldef = List_utils.get_def ll in
                if Bi_fun.size lenv > 1 then
                  let lset = List_utils.lmem_reach ll (IntSet.singleton ai) in
                  let ti = IntSet.min_elt (IntSet.remove ai lset) in
                  let cons =
                    Nc_cons (Tcons1.EQ,
                             Ne_var (Bi_fun.image ti lenv),
                             Ne_csti ldef.ld_emp_csti) in
                  if Op.sat_s am cons then
                    let ll = List_utils.lseg_2list ai ll in
                    let am, ax =
                      sve_fix "" am
                        { ax with
                          t_pred = IntMap.add group (Pred_list (ai, ll, lenv))
                            ax.t_pred } in
                    ax, am
                  else ax, am
                else ax, am
            | _ -> ax, am
          ) lx.t_pred (lx, lm) in
      let list_2seg (ldef: l_def) (x: t) (m: Op.t) (group: int) (var: int) =
        if group = -1 then m, x
        else
          let m, x, flag =
            if IntMap.mem group x.t_pred then m, x, false
            else sing_2segorlist ldef group x m in
          assert (IntMap.mem group x.t_pred);
          let m, x =
            if not flag then
              match IntMap.find group x.t_pred with
              | Pred_list (ai, lm, lenv) ->
                  let lc = { lc_def = ldef; lc_args = [] } in
                  let local_e, lm =
                    List_utils.sv_add_fresh ~root:true Ntaddr lm in
                  let lm = List_utils.list_edge_rem ai lm in
                  let lm = List_utils.lseg_edge_add ai local_e lc lm in
                  let lenv = Bi_fun.add local_e var lenv in
                  let ref_c = preprocess_pro_var var x.t_ref_count in
                  sve_fix "" m
                    { x with
                      t_pred = IntMap.add group (Pred_list (ai, lm, lenv))
                        x.t_pred;
                      t_ref_count = ref_c }
              | _ -> Log.fatal_exn "list_2seg on pure predicates"
            else m, x in
          m, x in
      if StringMap.is_empty !array_list_ind_defs then
        lx, lm, rx, rm, IntMap.empty, IntMap.empty
      else
        begin
          let lx, lm = empty_pred_clean lx lm in
          let rx, rm = empty_pred_clean rx rm in
          (* assert (StringMap.cardinal !list_ind_defs = 1); *)
          Log.warn
            "list predicates always folded with the first list definition";
          let _, ldef = StringMap.min_binding !array_list_ind_defs in
          Log.warn "next_off is with hack";
          let eq_vars (i: int) (m: Op.t) =
            IntSet.filter is_var (Op.get_eq_class i m) in
          let lx, lm = empty_tail_clean lx lm in
          let rx, rm = empty_tail_clean rx rm in
          (* get list information of the two states *)
          let l_seg, l_ind, l_pure_map, l_single_set =
            get_pairs ldef is_var lx lm in
          let r_seg, r_ind, r_pure_map, r_single_set =
            get_pairs ldef is_var rx rm in
          (* get lists in two states *)
          let rec gen_list (seg: (int * int) IntMap.t)
              (llist: (int * IntSet.t * IntSet.t) list) (am: Op.t) =
            assert (List.length llist > 0);
            let (curg, curdims, accdims) = List.hd llist in
            let curheads =
              IntSet.filter (fun el -> IntMap.mem el seg) curdims in
            if IntSet.is_empty curheads then
              llist
            else
              let curhead = IntSet.min_elt curheads in
              let (nextg, nextdim) = IntMap.find curhead seg in
              let llist =
                (nextg, Op.get_eq_class nextdim am,
                 IntSet.union curdims accdims) :: llist in
              gen_list seg llist am in
          let gen_lists (seg: (int * int) IntMap.t)
              (am: Op.t) (aind: int IntMap.t) =
            IntMap.mapi
              (fun group ahead ->
                let alist = [ group, Op.get_eq_class ahead am, IntSet.empty ] in
                let alist = gen_list seg alist am in
                List.map
                  (fun (g, dims, alldims) ->
                    g, IntSet.filter is_var dims, IntSet.filter is_var alldims
                  ) alist
              ) aind in
          let llists = gen_lists l_seg lm l_ind in
          let rlists = gen_lists r_seg rm r_ind in
          (* real join algorithm, merge and create here *)
          let rec bind_cornor_case (ilx: t) (ilm: Op.t) (irx: t) (irm: Op.t)
              (ilmap: int IntMap.t) (irmap: int IntMap.t)
              (last_lg: int) (last_rg: int) (lg: int) (lcurvars: IntSet.t)
              (ll: (int * IntSet.t * IntSet.t) list) =
            if IntSet.is_empty lcurvars then
              if last_lg = -1 then
                Log.fatal_exn "list head lost"
              else
                let ilx, ilm, _, _ = list_merge  last_lg lg ilx ilm in
                gen_binding ilx ilm irx irm ilmap irmap ll [] last_lg last_rg
            else
              let lvar = IntSet.min_elt lcurvars in
              let create_result = create_pred ldef lg irx irm ilx ilm eq_vars in
              match create_result with
              | Some (irx, irm, rng) ->
                  let ilx, ilm =
                    List.fold_left
                      (fun (iilx, iilm) (ilg, _, _) ->
                        let iilx, iilm, _, _ = list_merge  lg ilg iilx iilm in
                        iilx, iilm
                      ) (ilx, ilm) ll in
                  let irm, irx =
                    if last_rg = -1 || not (IntMap.mem last_lg ilx.t_pred) then
                      irm, irx
                    else list_2seg ldef irx irm last_rg lvar  in
                  ilx, ilm, irx, irm,
                  IntMap.add lg rng ilmap,
                  IntMap.add rng lg irmap
              | None ->
                  if last_rg = -1 then
                    ilx, ilm, irx, irm, ilmap, irmap
                      (* Log.fatal_exn "one list corresponds to none" *)
                  else
                    let ilx, ilm, _, _ = list_merge  last_lg lg ilx ilm in
                    gen_binding ilx ilm irx irm ilmap irmap ll []
                      last_lg last_rg
          and gen_binding (ilx: t) (ilm: Op.t) (irx: t) (irm: Op.t)
              (ilmap: int IntMap.t) (irmap: int IntMap.t)
              (illist: (int * IntSet.t * IntSet.t) list)
              (irlist: (int * IntSet.t * IntSet.t) list)
              (last_lg: int) (last_rg: int) =
            match illist, irlist with
            | [], [] -> ilx, ilm, irx, irm, ilmap, irmap
            | (lg, lcurvars, lallvars)::ll, [] ->
                bind_cornor_case ilx ilm irx irm ilmap irmap
                  last_lg last_rg lg lcurvars ll
            | [], (rg, rcurvars, rallvars)::rr ->
                let irx, irm, ilx, ilm, irmap, ilmap =
                  bind_cornor_case irx irm ilx ilm irmap
                    ilmap last_rg last_lg rg rcurvars rr in
                ilx, ilm, irx, irm, ilmap, irmap
            | (lg, lcurvars, lallvars)::ll, (rg, rcurvars, rallvars)::rr ->
                if IntSet.is_empty (IntSet.inter lcurvars rcurvars) then
                  if last_lg = -1 || last_rg = -1 then
                    Log.fatal_exn "unexpected case in gen_binding"
                  else
                    if IntSet.is_empty (IntSet.inter lcurvars rallvars) then
                      let ilx, ilm, _, _ = list_merge last_lg lg ilx ilm in
                      gen_binding ilx ilm irx irm ilmap irmap ll
                        irlist last_lg last_rg
                    else
                      let irx, irm, _, _ = list_merge last_rg rg irx irm in
                      gen_binding ilx ilm irx irm ilmap irmap illist
                        rr last_lg last_rg
                else
                  gen_binding ilx ilm irx irm (IntMap.add lg rg ilmap)
                    (IntMap.add rg lg irmap) ll rr lg rg in
          (* list-wise map *)
          let lx, lm, rx, rm, lmap, rmap, visited_rgs =
            IntMap.fold
              (fun lg llist (ilx, ilm, irx, irm, ilmap, irmap, ivisited) ->
                assert (List.length llist > 0);
                let (lgroup, hdims, alldims) = List.hd llist in
                let ff, rg =
                  IntMap.fold
                    (fun rgroup rl (flag, irgop)->
                      assert (List.length rl > 0);
                      let (_, rdims, _) = List.hd rl in
                      if IntSet.is_empty (IntSet.inter rdims hdims) then
                        flag, irgop
                      else if flag then
                        Log.fatal_exn "two rlists correspond to one llist"
                      else true, rgroup
                    ) rlists (false, -1) in
                if ff then
                  begin
                    assert (IntMap.mem rg rlists);
                    let rlist = IntMap.find rg rlists in
                    let ilx, ilm, irx, irm, ilmap, irmap =
                      gen_binding ilx ilm irx irm ilmap irmap
                        llist rlist (-1) (-1) in
                    ilx, ilm, irx, irm, ilmap, irmap, (IntSet.add rg ivisited)
                  end
                else
                  let ilx, ilm, irx, irm, ilmap, irmap =
                    gen_binding ilx ilm irx irm ilmap irmap
                      llist [] (-1) (-1) in
                  ilx, ilm, irx, irm, ilmap, irmap, ivisited
              ) llists
              (lx, lm, rx, rm, IntMap.empty, IntMap.empty, IntSet.empty) in
          let lx, lm, rx, rm, lmap, rmap =
            IntMap.fold
              (fun rg rlist  (ilx, ilm, irx, irm, ilmap, irmap ) ->
                if IntSet.mem rg visited_rgs then
                  (ilx, ilm, irx, irm, ilmap, irmap)
                else
                  gen_binding ilx ilm irx irm ilmap irmap [] rlist (-1) (-1)
              ) rlists (lx, lm, rx, rm, lmap, rmap) in
          let lx, lm, rx, rm =
            IntMap.fold
              (fun l_g r_g (ilx, ilm, irx, irm) ->
                match IntMap.mem l_g ilx.t_pred, IntMap.mem r_g irx.t_pred with
                | true, true ->  (ilx, ilm, irx, irm)
                | true, false ->
                    let irm, irx, _ = sing_2segorlist ldef r_g irx irm in
                    (ilx, ilm, irx, irm)
                | false, true ->
                    let ilm, ilx, _ = sing_2segorlist ldef l_g ilx ilm in
                    (ilx, ilm, irx, irm)
                | false, false ->
                    ilx, ilm, irx, irm
               ) lmap (lx, lm, rx, rm) in
          lx, lm, rx, rm, lmap, rmap
        end

    (* Group mapping to guide inclusion check *)
    let inclmap (lx: t) (lm: Op.t) (rx: t) (rm: Op.t) (is_var: int -> bool)
        : t * Op.t * (IntSet.t IntMap.t) * bool =
      (* synchronize predicates between tuples *)
      let lx, lm, lmap, rmap, flag =
        if StringMap.cardinal !array_list_ind_defs > 0 then
          let _, ldef = StringMap.min_binding !array_list_ind_defs in
          let lx, lm, nrx, nrm, lmap, rmap =
            pred_join true lx lm rx rm is_var in
          let lx, lm, rx, rm, lmap, rmap, flag =
            IntMap.fold
              (fun l_g r_g (ilx, ilm, irx, irm, ilj, irj, acc) ->
                match IntMap.mem l_g ilx.t_pred, IntMap.mem r_g irx.t_pred with
                | true, true ->  ilx, ilm, irx, irm, ilj, irj, acc
                | true, false ->
                    ilx, ilm, irx, irm, ilj, irj, false
                | false, true ->
                    let ilm, ilx = sing_2seg ldef l_g ilx ilm in
                    ilx, ilm, irx, irm, ilj, irj, acc
                | false, false ->
                    ilx, ilm, irx, irm, ilj, irj, acc
               ) lmap (lx, lm, rx, rm, lmap, rmap, true) in
          if nrx.t_groups < rx.t_groups  || not flag then
            lx, lm, IntMap.empty, IntMap.empty, true
          else  lx, lm, lmap ,rmap, false
        else lx, lm, IntMap.empty, IntMap.empty, false in
      if flag then lx, lm, IntMap.empty, true
      else
        let imap =
          IntSet.fold
            (fun lg_id oacc ->
              IntSet.fold
                (fun rg_id acc ->
                  match IntMap.mem lg_id lmap, IntMap.mem rg_id rmap with
                  | true, _ ->
                      IntMap.add lg_id
                        (IntSet.singleton (IntMap.find lg_id lmap)) acc
                  | false, true ->
                      IntMap.add (IntMap.find rg_id rmap)
                        (IntSet.singleton rg_id) acc
                  | _, _ ->
                      let bound_of_field g f x m =
                        let dim = Bi_fun.image (g, f) x.t_dimensions in
                        Op.bound_variable dim m in
                      let comp_opint lop rop isinf =
                        match (lop, rop) with
                        | None, None -> true
                        | _, None -> not isinf
                        | None, _ -> isinf
                        | Some a, Some b -> a <= b in
                      let comp_field lg rg f =
                        let lb = bound_of_field lg f lx lm in
                        let rb = bound_of_field rg f rx rm in
                        ( comp_opint rb.intv_inf lb.intv_inf true )  &&
                        ( comp_opint lb.intv_sup rb.intv_sup false)  in
                      let mle = comp_field lg_id rg_id g_index in
                      let mle =
                        IntMap.fold
                          (fun key _ iacc ->
                            iacc && comp_field lg_id rg_id key
                          ) lx.t_fields mle in
                      if mle then
                        let rgp =
                          try IntSet.add rg_id (IntMap.find lg_id acc)
                          with Not_found -> IntSet.singleton rg_id in
                        IntMap.add lg_id rgp acc
                      else acc
                ) rx.t_groups oacc
            ) lx.t_groups IntMap.empty in
          lx, lm, imap, IntMap.cardinal imap < IntSet.cardinal lx.t_groups

    (* Propatege in relation to numeric part, mainly the index information. *)
    let rlvar_2num (var: int)  (array: t) (main: Op.t): Op.t =
      let groups = IntMap.find var array.t_varRes in
      let group = IntSet.choose groups in
      let nm =
        IntSet.fold
          (fun key m ->
            if IntSet.mem key groups then m
            else
              let dim_index = Bi_fun.image (key, g_index) array.t_dimensions in
              let lwer = Nc_cons (Tcons1.SUP, Ne_var dim_index, Ne_var var) in
              let uper = Nc_cons (Tcons1.SUP, Ne_var var, Ne_var dim_index) in
              let m1 = Op.guard_s true uper m in
              let m2 = Op.guard_s true lwer m in
              let m1 = Op.assert_non_empty dim_index m1 in
              let m2 = Op.assert_non_empty dim_index m2 in
              Op.upper_bnd Jjoin m1 m2
          ) array.t_groups main in
      let index_dim = Bi_fun.image (group, g_index) array.t_dimensions in
      Op.assert_non_empty index_dim nm

    (* Derive relation information from numeric part *)
    let num_2rl (main: Op.t)  (var: int) (x: t) : t =
      let lwer = Nc_cons (Tcons1.SUP, (Ne_csti 0), (Ne_var var)) in
      let uper = Nc_cons (Tcons1.SUPEQ, (Ne_var var), (Ne_csti x.t_size))  in
      if not (Op.is_bot (Op.guard_s true  lwer main))
          && not (Op.is_bot (Op.guard_s true uper main)) then x
      else
        let groups, issole =
          IntSet.fold
            (fun g_id acc ->
              let tg, found = acc in
              if found then acc
              else
                let dim_index = Bi_fun.image (g_id, g_index) x.t_dimensions in
                let eq =
                  Nc_cons (Tcons1.EQ, Ne_var var, Ne_var dim_index) in
                let tm = Op.assert_non_empty dim_index main in
                if Op.is_bot (Op.guard_w true eq tm) then acc
                else
                  let intvar = Op.bound_variable var main in
                  let g1 = IntSet.add g_id tg in
                  match intvar.intv_inf, intvar.intv_sup with
                  | Some v1, Some v2 ->
                      begin
                        let index = Op.bound_variable dim_index main in
                        match index.intv_inf, index.intv_sup with
                        |  Some ii, Some is ->
                            if ii <= v1 && v2 <= is then
                              let dim_size =
                                Bi_fun.image (g_id, g_size) x.t_dimensions in
                              let size = Op.bound_variable dim_size main in
                              match size.intv_inf, size.intv_sup with
                              | Some si, Some ss ->
                                  if si = (is - ii + 1) && si = ss then
                                    let g2 = IntSet.singleton g_id in
                                    g2, true
                                  else
                                    g1, false
                              | _, _ -> g1, false
                            else g1, false
                        | _, _ -> g1, false
                      end
                  | _, _ -> g1, false
            ) x.t_groups (IntSet.empty, false) in
        let ogroups =
          try IntMap.find var x.t_varRes
          with Not_found -> x.t_groups in
        (* TODO: More precise inference,
         * e.g. IN cleanup,if parent = 2, and index_1 = 2, then
         * parent \in S_1 *)
        let nvarRes =
          IntMap.add var (IntSet.inter groups ogroups) x.t_varRes in
        { x with t_varRes = nvarRes }

    (** Bottom check  *)
    let is_bot (m: Op.t) (x: t): bool =
      IntSet.for_all
        (fun key  ->
          let dim_size = Bi_fun.image (key, g_size) x.t_dimensions in
          let dim_index = Bi_fun.image (key, g_index) x.t_dimensions in
          let equal0 = Nc_cons (Tcons1.EQ, Ne_var dim_size, Ne_csti 0) in
          not (Op.sat_s m equal0)
            && Op.is_bot (Op.assert_non_empty  dim_index m)
        ) x.t_groups

    (* Find the definition of a list by its name *)
    let ind_extract_list (name: string): l_def =
      try StringMap.find name !array_list_ind_defs
      with Not_found -> Log.fatal_exn "definition: %s not found" name

    (* Partitions according to memcad_assume *)
    let re_arrange_groups (num: int) (x: t) (main: Op.t): t * Op.t =
      let agroup = IntSet.min_elt x.t_groups in
      let groups = IntSet.remove agroup x.t_groups in
      let tx, tmain =
        IntSet.fold (fun key (ix, imain) -> merge agroup key ix imain)
          groups (x, main) in
      let rec cut tnum ix imain =
        if tnum = 1 then ix, imain
        else
          let ng = get_new_group () in
          let imain, ix = split get_new_dim agroup ng None None imain ix in
          cut (tnum - 1) ix imain in
      cut num tx tmain

    (* Add a list segment predicate *)
    let var_lseg_add (var_h: int) (var_e: int) (ai: svo gen_ind_call)
        (group: int) (main: Op.t) (x: t): Op.t * t =
      let ld_h = ind_extract_list ai.ic_name in
      let local_h, alist = List_utils.sv_add_fresh
          ~root:true Ntaddr List_utils.lmem_empty in
      let local_e, alist = List_utils.sv_add_fresh
          ~root:true Ntaddr alist in
      let l_env = Bi_fun.add local_h var_h Bi_fun.empty_inj in
      let l_env = Bi_fun.add local_e var_e l_env in
      let ref_c = preprocess_pro_var var_h x.t_ref_count in
      let ref_c = preprocess_pro_var var_e ref_c in
      let pars =
        match ai.ic_pars with
        | None -> [ ]
        | Some ind_pars -> ind_pars.ic_ptr in
      let pars = List.map fst pars in
      assert (pars = []);
      let lc = {lc_def = ld_h; lc_args = pars } in
      let alist = List_utils.lseg_edge_add local_h local_e lc alist in
      let main =
        apply_mform true group None ld_h.ld_next_mcons ld_h.ld_m_offs x main in
      sve_fix "" main
        {x with
         t_pred = IntMap.add group (Pred_list (local_h, alist, l_env)) x.t_pred;
         t_ref_count = ref_c}

    (* Add a list  predicate *)
    let var_list_add (var_h: int)  (ai: svo gen_ind_call)
        (group: int) (main: Op.t) (x: t): Op.t * t =
      let ld_h = ind_extract_list ai.ic_name in
      let local_h, alist = List_utils.sv_add_fresh
          ~root:true Ntaddr List_utils.lmem_empty in
      let l_env = Bi_fun.add local_h var_h Bi_fun.empty_inj in
      let ref_c = preprocess_pro_var var_h x.t_ref_count in
      let pars =
        match ai.ic_pars with
        | None -> [ ]
        | Some ind_pars -> ind_pars.ic_ptr in
      let pars = List.map fst pars in
      assert (pars = []);
      let lc = {lc_def = ld_h; lc_args = pars } in
      let alist = List_utils.list_edge_add local_h  lc alist in
      let main =
        apply_mform true group None ld_h.ld_next_mcons ld_h.ld_m_offs x main in
      sve_fix "" main
        { x with
          t_pred = IntMap.add group
            (Pred_list (local_h, alist, l_env)) x.t_pred;
          t_ref_count = ref_c }


    (* Add pure numeric constraints
     * One thing could be optimized: When var is not needed as mpar, we do not
     * refer to it in x.t_ref_count *)
    let var_pure_add (var: int) (ai: svo gen_ind_call) (group: int)
        (main: Op.t) (x: t): Op.t * t =
      let pdef =
        try
          StringMap.find ai.ic_name !Array_ppred_sig.ppred_defs
        with | Not_found -> Log.fatal_exn "unknown pure predicate" in
      let ipar =
        match ai.ic_pars with
        | Some pars ->
            List.fold_left
              (fun (acc_i) node ->
                match node with
                | Ii_lval c ->
                    assert (Offs.is_zero (snd c));
                    fst c :: acc_i
                | _ -> Log.fatal_exn "const parameter"
              ) [] pars.ic_int
        | None -> [] in
      let svm, l_env, ref_c =
        List.fold_left
          (fun (isvm, ilenv, irefc) iv ->
            let isvm = Dom_utils.svenv_add iv Ntaddr isvm in
            let ilenv = Bi_fun.add iv iv ilenv in
            let irefc = preprocess_pro_var iv irefc in
            isvm, ilenv, irefc
          ) (svenv_empty, Bi_fun.empty_inj, x.t_ref_count) (var :: ipar) in
      let pm =
        { pm_def = pdef;
          pm_mpar = None;
          pm_svemod = svm; pm_ipar = ipar } in
      let main =
        if List.length pdef.p_rules > 0 then
          let pr = List.hd pdef.p_rules in
          apply_mform true group None pr.pr_maya_cons pdef.p_maya_offs x main
        else main in
      let pm =
        if pdef.p_single_node then { pm with pm_mpar = Some var }
        else pm in
      sve_fix "" main
        { x with
          t_pred = IntMap.add group (Pred_pure (pm, l_env)) x.t_pred;
          t_ref_count = ref_c }

    (** Transfer functions *)
    (* Guard *)
    let guard (typ: bool) (cons: n_cons) (main: Op.t) (x: t):Op.t * t =
      let x = n_cons_fold (num_2rl main) cons x in
      main, x

    (* Propagate information in relation part to numeric part,
     * mainly the size information.
     * e.g. a \in group_1 then size_1 >= 1*)
    let rlgroup_2num (group: int) (array: t) (main: Op.t): t * Op.t =
      (* todo: everything *)
      (* todo: add this function to materialize *)
      array, main

    (* XR: I cannot understand this comment *)
    (* In upper layer, array cell "a[i].f" is resolveed into a + i * size + c
     *  (c is the offset of "f"), This function do the reverse thing.*)
    let resolve (array:t) (off:Offs.t) =
      let off = Offs.to_n_expr off in
      let cst, lin =
        match off with
        | Ne_bin (Texpr1.Add, Ne_csti cst, lin) -> cst, lin
        | lin -> 0, lin in
      let ali, var =
        match lin with
        | Ne_bin (Texpr1.Mul, Ne_csti ali, Ne_var var)-> ali, var
        | _ -> Log.fatal_exn "unexpected case in deref linexpr" in
      (* for now we only deals with variables as index  *)
      assert (cst < array.t_align);
      let fld, left =
        IntMap.fold
          (fun key sz acc ->
            let k, left = acc in
            if k > 0  then
              k, left
            else
              if left = 0 then
                key, 0
              else
                k, left - sz
          ) array.t_fields (-1, cst)  in
      assert (fld > 0);
      assert (ali = array.t_align);
      fld, var

    (* Find the group in which the array cell is, if there are several groups
     * in the array the cell might be belong to, we create disjunctions *)
    let deref_in_expr  (off:Offs.t) (main:Op.t) (array:t) =
      let fld, var = resolve array off in
      let array = num_2rl main var array in
      let groups =
        try IntMap.find var array.t_varRes
        with
        | Not_found -> Log.fatal_exn "Out of bound access found\n" in
      IntSet.fold
        (fun g_id acc ->
          let nvarRes =
            IntMap.add var (IntSet.singleton g_id) array.t_varRes in
          let narr = { array with t_varRes = nvarRes } in
          let nmain = rlvar_2num var narr main in
          let dim = Bi_fun.image (g_id, fld) narr.t_dimensions in
          (dim, nmain, narr) :: acc
        ) groups []

    (* For a variable, if the groups it belongs to is not determinestic
     * then merge all possible groups;
     * to make the l-value a non-summarizing dimension, split a group
     * which contains only the index varialbe *)
    let materialize (array: t) (fld: int) (var: int) (opg: int option)
        (ur_result: sub_unfold_result)
        (main: Op.t): t * Op.t * int * int * int =
      let array = num_2rl main var array in
      (* predicate unfold *)
      let dstgroup, array, main, ur_result =
        match opg with
        | Some group ->
              assert (ur_result.sur_is_mater);
              group, array, main, ur_result
        | None ->
            let groups =
              try IntMap.find var array.t_varRes
              with Not_found -> Log.fatal_exn "Out of bound access found\n" in
            let dstgroup = IntSet.choose groups in
            let groups = IntSet.remove dstgroup groups in
            let array, main =
              IntSet.fold
                (fun group acc ->
                  let tp_array, tp_main = acc in
                  merge dstgroup group tp_array tp_main
                ) groups (array, main) in
            dstgroup, array, main, (unfold_at_group dstgroup array main) in
      let tpred =
        match ur_result.sur_pred with
        | Some ap -> IntMap.add dstgroup ap array.t_pred
        | None -> IntMap.remove dstgroup array.t_pred in
      let main, array = sve_fix "" main { array with t_pred = tpred } in
      let _, refc, array, main =
        Bi_fun.fold_dom (fun a _ acc -> sve_rem a acc) ur_result.sur_rem_var
          (ur_result.sur_rem_var, array.t_ref_count, array, main) in
      let array = { array with t_ref_count = refc } in
      let main =
        apply_mform true dstgroup None ur_result.sur_mcons
          ur_result.sur_maya_off array main in
      let sz_dim = Bi_fun.image (dstgroup, g_size) array.t_dimensions in
      let cons = Nc_cons (Tcons1.EQ, Ne_var sz_dim, Ne_csti 1) in
      let array, main, ngroup =
        if not (Op.sat_s main cons) && not ur_result.sur_is_single then
          let ng = get_new_group () in
          let main, array =
            split get_new_dim dstgroup ng (Some var) (Some 1) main array in
          array, main, ng
        else
          let index_dim =
            Bi_fun.image (dstgroup, g_index) array.t_dimensions in
          let frsh_agn_expr = Ne_csti 1 in
          let main = Op.size_assign index_dim frsh_agn_expr main in
          let main =
            IntMap.fold
              (fun key _ acc ->
                let fdim =  Bi_fun.image (dstgroup, key) array.t_dimensions in
                Op.scalar_to_single fdim acc
              ) array.t_fields main in
          array, main, dstgroup in
      let dim = Bi_fun.image (ngroup, fld) array.t_dimensions in
      let main = Bi_fun.fold_dom
          (fun isv ifld acc ->
            let fdim = Bi_fun.image (ngroup, ifld) array.t_dimensions in
            match IntMap.find dstgroup array.t_pred with
            | Pred_list (_, _, lenv) ->
                let idim = Bi_fun.image isv lenv in
                Op.guard_s
                  true (Nc_cons (Tcons1.EQ, Ne_var idim, Ne_var fdim)) acc
            | _ -> Log.fatal_exn "unexpected case in vmap"
          ) ur_result.sur_vmap main in
      let main =
        apply_mform true dstgroup (Some ngroup) ur_result.sur_mcons
          ur_result.sur_maya_off array main in
      array, main, dim, dstgroup, ngroup

    (* Materialization on l-value *)
    let materialize_on_lv (array: t) (off: Offs.t) (main: Op.t)
        : t * Op.t * int =
      let fld, var = resolve array off in
      let opg, ur_result = unfold_at_var var main array in
      let array, main, dim, dstgroup, ngroup =
        materialize array fld var opg ur_result main in
      array, main, dim

    (* Dereference on array cells: from offset to dimensions *)
    let sv_array_deref (mv: IntSet.t) (off: Offs.t) (main: Op.t) (x: t)
        : Op.t * t =
      let fld, var = resolve x off in
      let (opg, ur_result) = unfold_at_var var main x in
      if not (opg = None) then
        (* if not (opg = None) || IntSet.mem var mv then *)
        let x, main, dim, dstgroup, ngroup =
          materialize x fld var opg ur_result main in
        main, x
      else
        main, x

    (* Remove the structural predicates on a groups *)
    let rem_pred (group: int) (x: t) (main: Op.t) =
      assert (IntMap.mem group x.t_pred);
      let lenv =
        match IntMap.find group x.t_pred with
        | Pred_list (_, _, lenv) -> lenv
        | Pred_pure (_, lenv) -> lenv in
      let _, refc, x, main =
        Bi_fun.fold_dom
          (fun av _ acc ->
            sve_rem av acc
           )lenv (lenv, x.t_ref_count, x, main) in
      { x with
        t_ref_count = refc;
        t_pred = IntMap.remove group x.t_pred}, main

    (* Synchronize the names from predicates of two states *)
    let pred_name_sync
        (is_le: bool) (l_g: int) (r_g: int)
        (lx: t) (lm: Op.t) (rx: t) (rm: Op.t) =
      let is_seg_alist (h: int) (tail: int)
          (lm: lmem) (ienv: local_env) (x: t) (m: Op.t) =
        let ur_emp = List.nth (List_mat.unfold h false lm) 1 in
        let key_map = fun _ -> Bi_fun.image tail ienv in
        let emp_cons = List.hd ur_emp.ur_cons in
        let emp_cons = n_cons_map key_map emp_cons in
        Op.sat_s m emp_cons in
      let sync_name (lsv: int) (rsv: int) (ilx: t)
          (ilm: Op.t) (irx: t) (irm: Op.t) (ilenv: local_env)
          (irenv: local_env) =
        let ld = Bi_fun.image lsv ilenv in
        let rd = Bi_fun.image rsv irenv in
        if ld = rd then
          ilenv, irenv, ilx, ilm, irx, irm
        else
          let ndim = if is_le then get_tmp_dim () else get_new_dim () in
          let ilm = Op.add_node ndim false 1 (Some 1) ilm in
          let irm = Op.add_node ndim false 1 (Some 1) irm in
          let ilm = Op.guard_s
              true (Nc_cons (Tcons1.EQ, Ne_var ndim, Ne_var ld)) ilm in
          let irm = Op.guard_s
              true (Nc_cons (Tcons1.EQ, Ne_var ndim, Ne_var rd)) irm in
          let ilenv, lref, ilx, ilm =
            sve_rem lsv (ilenv, ilx.t_ref_count, ilx, ilm) in
          let irenv, rref, irx, irm =
            sve_rem rsv (irenv, irx.t_ref_count, irx, irm) in
          let lref = IntMap.add ndim 1 lref in
          let rref = IntMap.add ndim 1 rref in
          let ilenv = Bi_fun.add lsv ndim ilenv in
          let irenv = Bi_fun.add rsv ndim irenv in
          let refreshVarRe (ov: int) (nv: int) (vr: IntSet.t IntMap.t) =
            if IntMap.mem ov vr then
              let set = IntMap.find ov vr in
              IntMap.add nv set (IntMap.remove ov vr)
            else vr in
          let ilvarRes = refreshVarRe ld ndim ilx.t_varRes in
          let irvarRes = refreshVarRe rd ndim irx.t_varRes in
          ilenv, irenv,
          {ilx with t_ref_count = lref; t_varRes = ilvarRes}, ilm,
          {irx with t_ref_count = rref; t_varRes = irvarRes}, irm in
      match IntMap.mem l_g lx.t_pred, IntMap.mem r_g rx.t_pred with
      | false, false -> lx, lm, rx, rm
      | true, true ->
          begin
            assert (IntMap.mem l_g lx.t_pred);
            assert (IntMap.mem r_g rx.t_pred);
            match IntMap.find l_g lx.t_pred, IntMap.find r_g rx.t_pred with
            | Pred_list (lai, ll, lenv), Pred_list (rai, rl, renv) ->
                let nlenv, nrenv, lx, lm, rx, rm =
                  sync_name lai rai lx lm rx rm lenv renv in
                let nlenv, nrenv, lx, lm, rx, rm =
                  match Bi_fun.size lenv, Bi_fun.size renv with
                  | 1, 1 -> nlenv, nrenv, lx, lm, rx, rm
                  | 2, 2 ->
                      let lset =
                        List_utils.lmem_reach ll (IntSet.singleton lai) in
                      let rset =
                        List_utils.lmem_reach rl (IntSet.singleton rai) in
                      let lset = IntSet.remove lai lset in
                      let rset = IntSet.remove rai rset in
                      let lv = IntSet.choose lset in
                      let rv = IntSet.choose rset in
                      sync_name lv rv lx lm rx rm nlenv nrenv
                  | 1, 2 ->
                      let rset =
                        List_utils.lmem_reach rl (IntSet.singleton rai) in
                      let rset = IntSet.remove rai rset in
                      let rv = IntSet.choose rset in
                      assert (is_seg_alist rai rv rl renv rx rm);
                      let nrenv, refc, rx, rm =
                        sve_rem rv (nrenv, rx.t_ref_count, rx, rm) in
                      nlenv, nrenv, lx, lm, {rx with t_ref_count = refc}, rm
                  | 2, 1 ->
                      let lset =
                        List_utils.lmem_reach ll (IntSet.singleton lai) in
                      let lset = IntSet.remove lai lset in
                      let lv = IntSet.choose lset in
                      assert (is_seg_alist lai lv ll lenv lx lm);
                      let nlenv, refc, lx, lm =
                        sve_rem lv (nlenv, lx.t_ref_count, lx, lm) in
                      nlenv, nrenv, lx, lm, {rx with t_ref_count = refc}, rm
                  | _,_ ->
                      Log.fatal_exn "unexpected env size in pred_name_sync" in
                { lx with
                  t_pred = IntMap.add l_g
                    (Pred_list (lai, ll, nlenv)) lx.t_pred },
                lm,
                { rx with
                  t_pred = IntMap.add r_g
                    (Pred_list (lai, ll, nlenv)) rx.t_pred },
                rm
            | Pred_pure (lp, lenv), Pred_pure (rp, renv) ->
                let tl, tr, nlenv, nrenv, lx, lm, rx, rm =
                  match lp.pm_mpar, rp.pm_mpar with
                  | Some lv, Some rv ->
                      let nlenv, nrenv, lx, lm, rx, rm =
                        sync_name lv rv lx lm rx rm lenv renv in
                      (Bi_fun.rem_dir lv lenv),
                      (Bi_fun.rem_dir rv renv),
                      nlenv, nrenv, lx, lm, rx, rm
                  | _, _ -> lenv, renv, lenv, renv, lx, lm, rx, rm in
                let nlenv, nrenv, lx, lm, rx, rm =
                  if Bi_fun.size tl = 0 then
                    nlenv, nrenv, lx, lm, rx, rm
                  else
                    begin
                      assert (Bi_fun.size tl = 1);
                      let alv = Bi_fun.fold_dom (fun key _ _ -> key) tl 0 in
                      let arv = Bi_fun.fold_dom (fun key _ _ -> key) tr 0 in
                      sync_name alv arv lx lm rx rm nlenv nrenv
                    end in
                { lx with
                  t_pred = IntMap.add l_g (Pred_pure (lp, nlenv)) lx.t_pred },
                lm,
                { rx with
                  t_pred = IntMap.add r_g (Pred_pure (lp, nlenv)) rx.t_pred },
                rm
            | _, _ -> Log.fatal_exn "not compatible pred in rename"
          end
      | true, false ->
          Log.warn "not synchronize pred to be renamed";
          let lx, lm = rem_pred l_g lx lm in
          lx, lm, rx, rm
      | false, true ->
          Log.warn "not synchronize pred to be renamed";
          let rx, rm = rem_pred r_g rx rm in
          lx, lm, rx, rm

    (* Apply operators split,create on two states
     * to make two states ready for includsion check *)
    let apply_inclmap (inclmap: IntSet.t IntMap.t) (la: t)
        (lm: Op.t) (ra: t) (rm: Op.t): Op.t * t * Op.t * t =
      let lmap = inclmap in
      (* build rmap*)
      let rmap =
        IntMap.fold
          (fun key set acc ->
            IntSet.fold
              (fun elt iacc ->
                let lgroup =
                  try IntMap.find elt iacc with Not_found -> IntSet.empty in
                let lgroup = IntSet.add key lgroup in
                IntMap.add elt lgroup iacc
              ) set acc
          ) lmap IntMap.empty in
      (* eliminate the chain case like l1-r1 l2-r1 l1-r2 *)
      let lmap, rmap =
        IntSet.fold
          (fun key acc ->
            let ltmap, rtmap = acc in
            if IntMap.mem key ltmap then
              let set = IntMap.find key ltmap in
              if IntSet.cardinal set > 1 then
                IntSet.fold
                  (fun elt ((lt, rt) as iacc) ->
                    let lset = IntMap.find key lt in
                    if IntSet.cardinal lset > 1 && elt != key then
                      let rset = IntMap.find elt rt in
                      if IntSet.cardinal rset > 1 then
                        let lset = IntSet.remove elt lset in
                        let rset = IntSet.remove key rset in
                        let lt = IntMap.add key lset lt in
                        let rt = IntMap.add elt rset rt in
                        lt, rt
                      else iacc
                    else iacc
                  ) set (ltmap, rtmap)
              else acc
            else acc
          ) la.t_groups (lmap, rmap) in
      (* split phase *)
      let size_bound (x: t) (m: Op.t) (g: int): int =
        let dim = Bi_fun.image (g, g_size) x.t_dimensions in
        let bound = Op.bound_variable dim m in
        match bound.intv_inf with
        | None -> Log.fatal_exn "size bound Log.fatal_exn"
        | Some i -> i in
      let lmap, rmap, la, lm =
        IntMap.fold
          (fun key set acc ->
            let tlmap, trmap, tla, tlm = acc in
            if IntSet.cardinal set > 1 then
              let host =
                if IntSet.mem key set then key
                else IntSet.choose set in
              let tlmap = IntMap.add key (IntSet.singleton host) tlmap in
              let trmap = IntMap.add host (IntSet.singleton key) trmap in
              let set = IntSet.remove key set in
              IntSet.fold
                (fun elt iacc ->
                  let ilmap, irmap, ila, ilm = iacc in
                  let ng_id = get_tmp_dim () in
                  let l_size = size_bound ila ilm key in
                  let r_size = size_bound ra rm elt in
                  let num = if l_size >= r_size then r_size else 0 in
                  let ilm, ila =
                    split get_tmp_dim key ng_id None (Some num)  ilm ila in
                  let ilmap =
                    IntMap.add ng_id (IntSet.singleton elt) ilmap in
                  let irmap =
                    IntMap.add elt (IntSet.singleton ng_id) irmap in
                  ilmap, irmap, ila, ilm
                ) set (tlmap, trmap, tla, tlm)
            else
              acc
          ) lmap (lmap, rmap, la, lm) in
      (* create phase*)
      let lmap, rmap, la, lm =
        IntSet.fold
          (fun elt acc ->
            let tlmap, trmap, tla, tlm = acc in
            if IntMap.mem elt trmap then
              acc
            else
              let fresh = get_tmp_dim () in
              let tla, tlm = create fresh elt  tla tlm  ra rm  in
              let trmap = IntMap.add elt (IntSet.singleton fresh) trmap in
              let tlmap = IntMap.add fresh (IntSet.singleton elt) tlmap in
              tlmap, trmap, tla, tlm
          ) ra.t_groups (lmap, rmap, la, lm) in
      (* merge phase*)
      let merge_phase lmap rmap ra rm =
        IntMap.fold
          (fun key set acc ->
            let tlmap, trmap, tra, trm = acc in
            if IntSet.cardinal set > 1 then
              let host = IntSet.choose set in
              let set = IntSet.remove host set in
              let trmap, tra, trm =
                IntSet.fold
                  (fun elt acc ->
                    let irmap, ira, irm = acc in
                    let ira, irm =  merge host elt ira irm in
                    let irmap = IntMap.remove elt irmap in
                    irmap, ira, irm
                  ) set (trmap, tra, trm) in
              let set = IntSet.singleton host in
              let tlmap = IntMap.add key set tlmap in
              tlmap, trmap, tra, trm
            else acc
          ) lmap (lmap, rmap, ra, rm) in
      let rmap, lmap, la, lm = merge_phase rmap lmap la lm in
      (* rename phase *)
      IntMap.fold
        (fun lid rid acc ->
          let lm, la, rm, ra = acc in
          let rid = IntSet.choose rid in
          let la, lm, ra, rm = pred_name_sync true lid rid la lm ra rm in
          if lid = rid then lm, la, rm, ra
          else
            let fresh = get_tmp_dim () in
            rename_group_in_le lid rid fresh lm la rm ra
        ) lmap (lm, la, rm, ra)

    (* Apply operators split,create on two states to make them ready for join*)
    let apply_joinmap (rankscore: (int * int * int) list) (la: t)
        (lm: Op.t) (ra: t) (rm: Op.t):  Op.t * t * Op.t * t=
      let lg_num = IntSet.cardinal la.t_groups in
      let rg_num = IntSet.cardinal ra.t_groups in
      let g_num = if lg_num > rg_num then lg_num else rg_num  in
      let threhold = 7 in
      (* Selection of pairs *)
      let cmp a b =
        let a1, a2, a3 = a in
        let b1, b2, b3 = b in
        if a3 > b3 then -1
        else if a3 < b3 then 1
        else 0 in
      let rankscore = List.sort cmp rankscore in
      let rankscore =
        List.fold_left
          (fun acc elt ->
            let al, num = acc in
            let e1, e2, e3 = elt in
            if num < 1 || e3 < threhold then  acc
            else elt::al, (num - 1)
          ) ([], g_num) rankscore in
      let rankscore, num = rankscore in
      (*extract pairs  *)
      let lmap, rmap =
        List.fold_left
          (fun acc elt->
            let ltmap, rtmap = acc in
            let (el, er, e3) = elt in
            let lext = IntMap.mem el ltmap in
            let rext = (IntMap.mem er rtmap) in
            match lext, rext with
            | true, true -> acc
            | true, false ->
                let set = IntMap.find el ltmap in
                let set = IntSet.add er set in
                let ltmap = IntMap.add el set ltmap in
                let rtmap = IntMap.add er (IntSet.singleton el) rtmap in
                ltmap, rtmap
            | false, true ->
                let set = IntMap.find er rtmap in
                let set = IntSet.add el set in
                let rtmap = IntMap.add er set rtmap in
                let ltmap = IntMap.add el (IntSet.singleton er) ltmap in
                ltmap, rtmap
            | false, false ->
                let ltmap = IntMap.add el (IntSet.singleton er) ltmap in
                let rtmap = IntMap.add er (IntSet.singleton el) rtmap in
                ltmap, rtmap
          ) (IntMap.empty, IntMap.empty) rankscore in
      let lmap, rmap =
        IntSet.fold
          (fun key acc ->
            let ltmap, rtmap = acc in
            if IntMap.mem key ltmap then
              let set = IntMap.find key ltmap in
              if IntSet.cardinal set > 1 then
                IntSet.fold
                  (fun elt iacc ->
                    let lt, rt = iacc in
                    let lset = IntMap.find key lt in
                    if IntSet.cardinal lset > 1 then
                      let rset = IntMap.find elt rt in
                      if IntSet.cardinal rset > 1 then
                        let lset = IntSet.remove elt lset in
                        let rset = IntSet.remove key rset in
                        let lt = IntMap.add key lset lt in
                        let rt = IntMap.add elt rset rt in
                        lt, rt
                      else iacc
                    else iacc
                  ) set (ltmap, rtmap)
              else acc
            else acc
          ) la.t_groups (lmap, rmap) in
      (* merge phase*)
      let merge_phase lmap rmap ra rm =
        IntMap.fold
          (fun key set acc ->
            let tlmap, trmap, tra, trm = acc in
            if IntSet.cardinal set > 1 then
              let host = IntSet.choose set in
              let set = IntSet.remove host set in
              let trmap, tra, trm =
                IntSet.fold
                  (fun elt acc ->
                    let irmap, ira, irm = acc in
                    let ira, irm = merge host elt ira irm in
                    let irmap = IntMap.remove elt irmap in
                    irmap, ira, irm
                  ) set (trmap, tra, trm) in
              let set = IntSet.singleton host in
              let tlmap = IntMap.add key set tlmap in
              tlmap, trmap, tra, trm
            else acc
          ) lmap (lmap, rmap, ra, rm) in
      let lmap, rmap, ra, rm = merge_phase lmap rmap ra rm in
      let rmap, lmap, la, lm = merge_phase rmap lmap la lm in
      (* create phase*)
      let create_phase  lmap rmap la lm ra rm =
        IntSet.fold
          (fun elt acc ->
            let tlmap, trmap, tra, trm = acc in
            if IntMap.mem elt tlmap then acc
            else
              let fresh = get_new_group () in
              let tra, trm = create fresh elt tra trm la lm  in
              let tlmap = IntMap.add elt (IntSet.singleton fresh) tlmap in
              let trmap = IntMap.add fresh (IntSet.singleton elt) trmap in
              tlmap, trmap, tra, trm
          ) la.t_groups (lmap, rmap, ra, rm) in
      let lmap, rmap, ra, rm = create_phase lmap rmap la lm ra rm in
      let rmap, lmap, la, lm = create_phase rmap lmap ra rm la lm in
      IntMap.fold
        (fun lid rid acc ->
          let ilm, ila, irm, ira = acc in
          let rid = IntSet.choose rid in
          let ila, ilm, ira, irm =
            pred_name_sync false lid rid ila ilm ira irm in
          if lid = rid then
            ilm, ila, irm, ira
          else
            let fresh = get_new_group () in
            rename_group lid rid fresh ilm ila irm ira
        ) lmap (lm, la, rm, ra)

    (* apply operators split,create,merge on two states to make them
     * ready for widen *)
    let apply_widenmap (rankscore: (int * int * int) list) (la: t)
        (lm: Op.t) (ra: t) (rm: Op.t)
        : Op.t * t * Op.t * t =
      let cmp a b =
        let a1, a2, a3 = a in
        let b1, b2, b3 = b in
        if a3 > b3 then -1
        else if a3 < b3 then 1
        else 0 in
      let rankscore = List.sort cmp rankscore in
      (*extract pairs  *)
      let lmap, rmap =
        List.fold_left
          (fun acc elt ->
            let ltmap, rtmap = acc in
            let (el, er, e3) = elt in
            let lext = IntMap.mem el ltmap in
            let rext = (IntMap.mem er rtmap) in
            match lext, rext with
            | true, true -> acc
            | true, false ->
                let set = IntMap.find el ltmap in
                let set = IntSet.add er set in
                let ltmap = IntMap.add el set ltmap in
                let rtmap = IntMap.add er (IntSet.singleton el) rtmap in
                ltmap, rtmap
            | false, true ->
                let set = IntMap.find er rtmap in
                let set = IntSet.add el set in
                let rtmap = IntMap.add er set rtmap in
                let ltmap = IntMap.add el (IntSet.singleton er) ltmap in
                ltmap, rtmap
            | false, false ->
                let ltmap = IntMap.add el (IntSet.singleton er) ltmap in
                let rtmap = IntMap.add er (IntSet.singleton el) rtmap in
                ltmap, rtmap
          ) (IntMap.empty,IntMap.empty) rankscore in
      (* eliminate the chain case like l1-r1 l2-r1 l2-r2 *)
      let lmap, rmap =
        IntSet.fold
          (fun key acc ->
            let ltmap, rtmap = acc in
            if IntMap.mem key ltmap then
              let set = IntMap.find key ltmap in
              if IntSet.cardinal set > 1 then
                IntSet.fold
                  (fun elt ((lt, rt) as iacc) ->
                    let lset = IntMap.find key lt in
                    if IntSet.cardinal lset > 1 then
                      let rset = IntMap.find elt rt in
                      if IntSet.cardinal rset > 1 then
                        let lset = IntSet.remove elt lset in
                        let rset = IntSet.remove key rset in
                        let lt = IntMap.add key lset lt in
                        let rt = IntMap.add elt rset rt in
                        lt, rt
                      else iacc
                    else iacc
                  ) set (ltmap, rtmap)
              else acc
            else acc
          ) la.t_groups (lmap, rmap) in
      let merge_phase lmap rmap ra  rm =
        IntMap.fold
          (fun key set acc ->
            let tlmap, trmap, tra, trm = acc in
            if IntSet.cardinal set > 1 then
              let host = IntSet.choose set in
              let set = IntSet.remove host set in
              let trmap, tra, trm =
                IntSet.fold
                  (fun elt acc ->
                    let irmap, ira, irm = acc in
                    let ira, irm = merge host elt ira irm in
                    let irmap = IntMap.remove elt irmap in
                    irmap, ira, irm
                  ) set (trmap, tra, trm) in
              let set = IntSet.singleton host in
              let tlmap = IntMap.add key set tlmap in
              tlmap, trmap, tra, trm
            else acc
          ) lmap (lmap, rmap, ra, rm) in
      let lmap, rmap, ra, rm = merge_phase lmap rmap ra rm in
      let rmap, lmap, la, lm = merge_phase rmap lmap la lm in
      (* rename phase *)
      IntMap.fold
        (fun lid rid acc ->
          let lm, la, rm, ra = acc in
          let rid = IntSet.choose rid in
          let la, lm, ra, rm = pred_name_sync false lid rid la lm ra rm in
          if lid = rid then lm, la, rm, ra
          else
            let fresh = get_new_group () in
            rename_group lid rid fresh lm la rm ra
        ) lmap (lm, la, rm, ra)

    (* Remove all dimensions from a group *)
    let rem_dims (x: t) (m: Op.t): Op.t =
      Bi_fun.fold_dom (fun _ dim tm -> Op.rem_node dim tm) x.t_dimensions m

    (* Whether a dimension is live *)
    let is_dimension_in (dim: int) (x: t): bool =
      Bi_fun.mem_inv dim x.t_dimensions

    (** Caution: remove ref count when delete an predicates *)
    let pre_assign (id: int) (main: Op.t) (x: t): Op.t * t =
      if IntMap.mem id x.t_ref_count then
        let ref_c = IntMap.find id x.t_ref_count in
        if ref_c = 1 then
          main, {x with t_ref_count = IntMap.remove id x.t_ref_count}
        else
          let x = {x with t_ref_count = IntMap.remove id x.t_ref_count} in
          let ndim = get_new_dim () in
          let main = Op.add_node ndim false 1 (Some 1) main in
          let main = Op.update_subs_elt ndim (Ne_var id) main in
          let tpred =
            IntMap.map
              (fun ap ->
                match ap with
                | Pred_list (ai, al, lenv) ->
                    if Bi_fun.mem_inv id lenv then
                      Pred_list
                        (ai, al,
                         Bi_fun.add (Bi_fun.inverse_inj id lenv) ndim lenv)
                    else Pred_list (ai, al, lenv)
                | Pred_pure (al, lenv) ->
                    if Bi_fun.mem_inv id lenv then
                      Pred_pure
                        (al,
                         Bi_fun.add (Bi_fun.inverse_inj id lenv) ndim lenv)
                    else Pred_pure (al, lenv)
               ) x.t_pred in
          main, { x with
                  t_pred = tpred;
                  t_ref_count = IntMap.add ndim (ref_c - 1) x.t_ref_count }
      else main, x

    (* Assignment on array cells *)
    let assign_on_sum (dst: int) (expr: n_expr)  (main: Op.t) (x: t): Op.t * t =
      let nx = { x with t_indexRes =  IntMap.remove dst x.t_indexRes } in
    (* Maybe it is not needed with new numeric domain
     * Get the index relations after an assignment on summary dimension,
     * now only deal with  expression with non-summary dimensions *)
      let nx =
        match expr with
        | Ne_var var ->
            let nx = num_2rl main var nx in
            if IntMap.mem var nx.t_varRes then
              let group = IntMap.find var nx.t_varRes in
              let nindexRes = IntMap.add dst group nx.t_indexRes in
              { nx with t_indexRes = nindexRes }
            else nx
        | _ ->
            let lwer = Nc_cons (Tcons1.SUP, (Ne_csti 0), (Ne_var dst)) in
            let uper =
              Nc_cons (Tcons1.SUPEQ, (Ne_var dst), (Ne_csti nx.t_size)) in
            let domlw = Op.guard_w true uper main in
            let domup = Op.guard_w true lwer main in
            if not (Op.is_bot domlw) || not (Op.is_bot domup) then nx
            else
              let groups, _ =
                IntSet.fold
                  (fun g_id acc ->
                    let tg, found = acc in
                    if found then
                      acc
                    else
                      let dim = Bi_fun.image (g_id, g_index) nx.t_dimensions in
                      let eq =
                        Nc_cons (Tcons1.EQ, (Ne_var dst), (Ne_var dim)) in
                      let tm = Op.assert_non_empty dim  main in
                      let domeq = Op.guard_w true eq tm in
                      if Op.is_bot domeq  then
                        acc
                      else
                        let up =
                          Nc_cons (Tcons1.SUP, (Ne_var dst), (Ne_var dim)) in
                        let low =
                          Nc_cons (Tcons1.SUP, (Ne_var dim), (Ne_var dst)) in
                        (* ljc_caution a problem appears... *)
                        let domup = Op.guard_w true up main in
                        let domlow = Op.guard_w true low main in
                        let domneq = (Op.is_bot domup) && (Op.is_bot domlow) in
                        let index = Op.bound_variable dim main in
                        let size = Op.bound_variable dim main in
                        let g1 = IntSet.add g_id tg in
                        let g2 = IntSet.singleton g_id in
                        let tf =
                          match domneq, size.intv_inf, size.intv_sup with
                          | true, Some si, Some ss ->
                              begin
                                match index.intv_inf, index.intv_sup with
                                | Some ii, Some is ->
                                    si = (is - ii + 1) && si = ss
                                | _, _ -> false
                              end
                          | _, _, _ -> false in
                        if tf then g2, tf
                        else g1, tf
                ) nx.t_groups (IntSet.empty, false) in
              (* TODO: More precise inference,
               * e.g. IN cleanup,if parent = 2, and index_1 = 2, then
               * parent \in S_1 *)
              let nindexRes = IntMap.add dst groups nx.t_indexRes in
              { nx with t_indexRes = nindexRes } in
      main, nx

    (* Assignment on scalar variables *)
    let assign_on_sca (id: int) (expr: n_expr) (main: Op.t) (x: t): t =
      let assign_sca_for_predicate (id: int) (expr: n_expr)
          (main: Op.t) (x: t):  t =
        match expr with
        | Ne_var var ->
            if IntMap.mem var x.t_indexRes then
              let vr =
                IntMap.add id (IntMap.find var x.t_indexRes) x.t_varRes in
              { x with t_varRes = vr }
            else x
        | _ -> x in
      let nvarRes =  IntMap.remove id x.t_varRes in
      let nvarRes =
        match expr with
        | Ne_var var ->
            if IntMap.mem var nvarRes then
              IntMap.add id (IntMap.find var nvarRes) nvarRes
            else  nvarRes
        | _ -> nvarRes in
      let x =  { x with t_varRes = nvarRes } in
      let x = num_2rl main id x in
      assign_sca_for_predicate id expr main x

    (* get a new array content node *)
    let fresh_array_node (id: int) (size: int) (fields: int list)
        (m: Op.t) (* main numeric element  *)
        : t * Op.t =
      let fld_num, fields =
        List.fold_left
          (fun (f_counter, amap) size_of_field ->
            let f_counter = f_counter + 1 in
            let nmap = IntMap.add f_counter size_of_field amap in
            f_counter, nmap
          ) (0, IntMap.empty) fields in
      let align = IntMap.fold (fun _ fld acc -> acc + fld) fields 0 in
      let group_id = get_new_group () in
      let group = IntSet.singleton group_id in
      (* add dimensions to array_node and main numeric element *)
      let dim_index = get_new_dim () in
      let dim_size = get_new_dim () in
      let dimensions =
        Bi_fun.add (group_id, g_index) dim_index Bi_fun.empty_inj in
      let nm = Op.add_node dim_index true size (Some size) m in
      let dimensions =
        Bi_fun.add (group_id, g_size) dim_size dimensions in
      let nm = Op.add_node dim_size false 1 (Some 1) nm in
      let dimensions, nm =
        IntMap.fold
          (fun key _ (td, tm) ->
            let ndim = get_new_dim () in
            (Bi_fun.add (group_id, key) ndim td),
            (Op.add_node ndim false size (Some size) tm)
          ) fields (dimensions, nm) in
      (* add constraints on index *)
      let lwer = Nc_cons (Tcons1.SUPEQ, Ne_var dim_index, Ne_csti 0) in
      let uper = Nc_cons (Tcons1.SUP, Ne_csti size, Ne_var dim_index) in
      let nm = Op.guard_s true uper nm in
      let nm = Op.guard_s true lwer nm in
      (* add constraints on size *)
      let nexpr = Ne_csti size in
      let nm = Op.update_subs_elt dim_size nexpr nm in
      let x =
        { t_id = id;
          t_fields = fields;
          t_align = align;
          t_size = size;
          t_groups = group;
          t_dimensions = dimensions;
          t_varRes = IntMap.empty;
          t_indexRes = IntMap.empty;
          t_pred = IntMap.empty ;
          t_ref_count = IntMap.empty; } in
      x, nm

    (* Assume a list predicate on a group *)
    let assume_ind (var_h: int) (ai: svo gen_ind_call)
        (main: Op.t) (x: t): Op.t * t =
      let subm =
        match StringMap.mem ai.ic_name !array_list_ind_defs,
          StringMap.mem ai.ic_name !Array_ppred_sig.ppred_defs with
        | true, false ->
            let ld_h = ind_extract_list ai.ic_name in
            ld_h.ld_submem
        | false, true ->
            let pd_h = StringMap.find ai.ic_name !Array_ppred_sig.ppred_defs in
            Some pd_h.p_submem
        | _, _ -> Log.fatal_exn "wrong ind name" in
      (* Rearange groups since assumption needs specific number of groups *)
      let actype, ngs =
        match subm with
        | None -> Log.fatal_exn "non-submem inductive definition in submem"
        | Some sub_ind -> sub_ind.acc_type, sub_ind.groups in
      assert (actype = Access_by_offset);
      let get_free_group (tm: Op.t) (tx: t) =
        if IntMap.is_empty tx.t_pred then
          let tx, tm = re_arrange_groups ngs tx tm in
          IntSet.min_elt tx.t_groups, tx, tm
        else
          IntSet.min_elt
            (IntSet.filter (fun key -> not (IntMap.mem key tx.t_pred))
               tx.t_groups),
          tx, tm in
      let free_group, x, main = get_free_group main x in
      if StringMap.mem ai.ic_name !Array_ppred_sig.ppred_defs then
        var_pure_add var_h ai free_group main x
      else
        var_list_add var_h ai free_group main x

    (* Assume a list segment on a group *)
    let assume_seg (var_h: int) (ai: svo gen_ind_call)
        (var_e: int) (ai_e: svo gen_ind_call) (main: Op.t) (x: t): Op.t * t =
      let ld_h = ind_extract_list ai.ic_name in
      (* Rearange groups since assumption needs specific number of groups *)
      let actype, ngs =
        match ld_h.ld_submem with
        | None -> Log.fatal_exn "non-submem inductive definition in submem"
        | Some sub_ind -> sub_ind.acc_type, sub_ind.groups in
      assert (actype = Access_by_offset);
      let get_free_group (tm: Op.t) (tx: t) =
        if IntMap.is_empty tx.t_pred then
          let tx, tm = re_arrange_groups ngs tx tm in
          (IntSet.min_elt tx.t_groups), tx, tm
        else
          IntSet.min_elt
            (IntSet.filter
               (fun key ->
                 not (IntMap.mem key tx.t_pred)
               ) tx.t_groups), tx, tm in
      let free_group, x ,main = get_free_group main x in
      let main, x = var_lseg_add var_h var_e ai free_group main x in
      (* add tail inductive predicate *)
      let free_group, x, main = get_free_group main x in
      if StringMap.mem ai_e.ic_name !Array_ppred_sig.ppred_defs then
        var_pure_add var_e ai_e free_group main x
      else
        var_list_add var_e ai_e free_group main x

    (* Check whether predicates on arrays are satisfied  *)
    let array_check  (x: t) (main: Op.t): bool =
      Log.fatal_exn "array check"

    (* Check whether an inductive predicate is satisfied *)
    let check_ind  (var_h: int) (ai: svo gen_ind_call)
        (main: Op.t) (x: t): bool  =
      let x, main =
        IntSet.fold
          (fun key (ax, am) ->
            if IntMap.mem key ax.t_pred then
              ax, am
            else
              let sdim = Bi_fun.image (key, g_size) ax.t_dimensions in
              let inter = Op.bound_variable sdim am in
              match inter.intv_inf, inter.intv_sup with
              | Some 1, Some 1 ->
                  let am, ax =
                    sing_2seg (StringMap.find ai.ic_name !array_list_ind_defs)
                      key ax am in
                  ax, am
              | _ -> ax, am
           ) x.t_groups (x, main) in
      let sat_count =
        IntMap.fold
          (fun group apred acc ->
            match apred with
            | Pred_list (ai, lm, lenv) ->
                if Op.sat_s main
                    (Nc_cons
                       (Apron.Tcons1.EQ, (Ne_var var_h),
                        (Ne_var (Bi_fun.image ai lenv)))) then acc + 1
                else acc
            | Pred_pure (pm, env) -> acc + 1
          ) x.t_pred 0 in
      sat_count > 0

    (* Check whether an inductive segment is satisfied *)
    let check_seg (var_h: int) (ai: svo gen_ind_call)
        (var_e: int) (ai_e: svo gen_ind_call) (main: Op.t) (x: t): bool =
      let sat_count =
        IntMap.fold
          (fun group apred acc ->
            match apred with
            | Pred_list (ai, lm, lenv) ->
                if Op.sat_s main
                    (Nc_cons
                       (Apron.Tcons1.EQ, (Ne_var var_h),
                        (Ne_var (Bi_fun.image ai lenv)))) then acc + 1
                else acc
            | Pred_pure (pm, env) -> acc + 1
          ) x.t_pred 0 in
      sat_count > 0
  end
