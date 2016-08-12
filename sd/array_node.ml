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
open Graph_sig
open Ind_sig
open Nd_sig
open Svenv_sig

open Dom_utils
open Graph_utils
open Nd_utils
open Dom_val_maya
open Array_pred_utils
open Array_pred_sig
open Array_pred_impl
(* Apron library needed here *)
open Apron

module Log =
  Logger.Make(struct let section = "a_node__" and level = Log_level.DEBUG end)

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


(** Functions for debug **)
let ljc_map_2str m: string =
  let buff = Buffer.create 80 in
  IntMap.iter (fun key set ->
      Buffer.add_string buff (Printf.sprintf "%d -> %s\n" key (intset_2str set));
    ) m;
  Buffer.contents buff

let ljc_rankscore_2str l: string =
  let buff = Buffer.create 80 in
  List.iter (fun (l,r,score) ->
      Buffer.add_string buff (Printf.sprintf "%d----%d -> %d\n" l r score)
    ) l;
  Buffer.contents buff

(** A functor that describes the properties of an array **)
module Array_Node (Op: DOM_MAYA) =
  struct
    (** This module is about the information and operation on array node.
     ** For now, we just support varRe and indexRe predicates happen
     ** within an array.   *)

    module Pred =  Make_StaticList(Op)

    type predicates =
      | Uninitialized
      | NoPred
      | OnePred of Pred.t

    type t =
        { (* Id of this array node *)
          t_id: int;
          (* Offset of each field *) (* XR: looks like their offsets *)
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
          t_predicate: predicates;
        }

    (* XR: add support for indentation *)
    (** pretty print  *)
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
            let (g,f) = Bi_fun.inverse_inj di x.t_dimensions in
            let oline =
              Printf.sprintf
                "\n (%d,%d) <- %s \n"
                g f (intset_2str set ) in
            acc ^ oline
          ) x.t_indexRes "Index Relations:\n" in
      let strPred = match x.t_predicate with
      | OnePred pt -> Pred.t_2stri "The group holds predicates: \n" pt
      | _ -> "" in
      Printf.sprintf "%s ---------In Array Node: |%d|--------------
        \n %d Groups: %s\n\n\n %s \n\n %s \n %s \n\n"
        ind x.t_id (IntSet.cardinal x.t_groups) (intset_2str x.t_groups)
        strVarRe strIndexRe strPred


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

    (* Forget the information about the contents of a group.
     * This function is called in transfer functions on assignment *)
    let forget_indexRe (dim:int) (x:t): t =
      { x with t_indexRes =  IntMap.remove dim x.t_indexRes }

    (* XR: I do not understand this comment! *)
    (* Compute the similarity of the values of the two variables *)
    let var_compare (lv: int) (lm: Op.t) (rv: int) (rm:Op.t): int =
      let intevL = Op.bound_variable lv lm in
      let intevR = Op.bound_variable rv rm in
      let score (a: int option) b =
        match a,b with
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

    let inclmap (lx: t) (lm: Op.t) (rx: t) (rm: Op.t)
        : (IntSet.t IntMap.t) * bool =
      let imap =
        IntSet.fold
          (fun lg_id oacc ->
            IntSet.fold
              (fun rg_id acc ->
                let bound_of_field g f x m =
                  let dim = Bi_fun.image (g,f) x.t_dimensions in
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
                      iacc && ( comp_field lg_id rg_id key)
                    ) lx.t_fields ( mle ) in
                let mle =
                  match lx.t_predicate, rx.t_predicate with
                  | OnePred lp, OnePred rp ->
                      mle && Pred.is_incl_group lg_id rg_id lp rp
                  | _ -> mle in
                if mle then
                  let rgp =
                    try IntSet.add rg_id (IntMap.find lg_id acc)
                    with Not_found -> IntSet.singleton rg_id in
                  IntMap.add lg_id rgp acc
                else acc
              ) rx.t_groups oacc
          ) lx.t_groups IntMap.empty in
      imap, IntMap.cardinal imap < IntSet.cardinal lx.t_groups

    (* Inclusion check on two states with the same parition *)
    let flat_is_le (lx: t) (rx: t): bool =
      let compareRes lres rres =
        IntMap.fold
          (fun var set acc ->
            acc && ( not (IntMap.mem var lres)
                   || IntSet.subset (IntMap.find var lres) set)
          ) rres true in
      compareRes lx.t_varRes rx.t_varRes
        && compareRes lx.t_indexRes rx.t_indexRes

    (* Join function for two states with the same partition *)
    let flat_join (lx: t) (rx: t): t =
      let set_join key ls rs =
        match ls, rs with
        | None, _ -> None
        | _, None -> None
        | Some l, Some r -> Some (IntSet.union l r) in
      { lx with
        t_varRes   = IntMap.merge set_join lx.t_varRes rx.t_varRes;
        t_indexRes = IntMap.merge set_join lx.t_indexRes rx.t_indexRes }

    (* The numeric constraints for each index dimensions *)
    let base_index_cons (x: t) (m: Op.t): Op.t =
      let m =
        IntSet.fold
          (fun key acc ->
            let index_dim = Bi_fun.image (key,g_index) x.t_dimensions in
            let cons_idx_low =
              Nc_cons (Tcons1.SUPEQ,Ne_var index_dim,Ne_csti 0) in
            let cons_idx_up =
              Nc_cons (Tcons1.SUP,Ne_csti x.t_size,Ne_var index_dim) in
            let acc = Op.guard_s true cons_idx_low acc in
            Op.guard_s true cons_idx_up acc
          ) x.t_groups m in
      IntMap.fold
        (fun var _ acc ->
          let cons_idx_low = Nc_cons (Tcons1.SUPEQ,Ne_var var,Ne_csti 0) in
          let cons_idx_up = Nc_cons (Tcons1.SUP,Ne_csti x.t_size,Ne_var var) in
          let acc = Op.guard_s true cons_idx_low acc in
          Op.guard_s true cons_idx_up acc
        ) x.t_varRes m

    (* Constrain numeric elements in each group on the size of each group  *)
    let nc_size (array: t) (main: Op.t): Op.t=
      let expr =
        IntSet.fold
          (fun elt expr ->
            let dim = Bi_fun.image (elt,g_size) array.t_dimensions in
            Ne_bin (Texpr1.Add,expr,Ne_var dim)
          ) array.t_groups (Ne_csti 0) in
      let idx_size_expr =
        IntSet.fold
          (fun elt expr ->
            let dim = Bi_fun.image (elt,g_index) array.t_dimensions in
            Ne_bin (Texpr1.Add,expr,Ne_var dim)
          ) array.t_groups (Ne_csti 0) in
      let idx_cons =
        Nc_cons (Tcons1.SUPEQ,Ne_csti array.t_size,idx_size_expr) in
      let cons = Nc_cons (Tcons1.SUPEQ,Ne_csti array.t_size,expr) in
      Op.size_guard idx_cons (Op.guard_s true cons main)

    (* Calculate the similariy of two groups within one state,
     * this function is used to help calculate whether to do "merge" *)
    let self_rankscore (x: t) (main: Op.t) (l_id: int) (r_id: int) : int =
      let pred_weight = 10 in
      let idx_weight = 1 in
      let sz_weight = 1 in
      let fld_weight = 1 in
      let relation_weight = 3 in
      let result =
        IntMap.fold
          (fun key off wacc->
            let l_dim = Bi_fun.image (l_id,key) x.t_dimensions in
            let r_dim = Bi_fun.image (r_id,key) x.t_dimensions in
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
      let lsz_dim = Bi_fun.image (l_id,g_size) x.t_dimensions in
      let lidx_dim = Bi_fun.image (l_id,g_index) x.t_dimensions in
      let rsz_dim = Bi_fun.image (r_id,g_size) x.t_dimensions in
      let ridx_dim = Bi_fun.image (r_id,g_index) x.t_dimensions in
      let sz_score = sz_weight * (var_compare lsz_dim main rsz_dim main) in
      let idx_score =
        idx_weight * (var_compare lidx_dim main ridx_dim main) in
      let cons = Nc_cons (Tcons1.EQ, Ne_var lidx_dim, Ne_var ridx_dim) in
      let idx_score =
        if Op.is_bot (Op.guard_s true cons main) then 0
        else idx_score in
      let result = result + sz_score + idx_score in
      let result =
        match x.t_predicate with
        | OnePred pt -> result + pred_weight * (Pred.joinrank l_id r_id pt)
        | _ -> result in
      result

    (* Calculate the similarity of each group from two states *)
    let rankscore (lx: t) (lm: Op.t) (rx: t) (rm: Op.t)
        : (int * int * int) list =
      let idx_weight = 1 in
      let sz_weight = 1 in
      let fld_weight = 1 in
      let name_weight = (IntMap.cardinal lx.t_fields) * 10 in
      let fresh_name_weight = 3 in
      let var_weight = 1 in
      IntSet.fold
        (fun lg_id lacc ->
          let lsz_dim = Bi_fun.image (lg_id,g_size) lx.t_dimensions in
          let lidx_dim = Bi_fun.image (lg_id,g_index) lx.t_dimensions in
          IntSet.fold
            (fun rg_id racc ->
              let total =
                match IntSet.mem lg_id rx.t_groups,
                  IntSet.mem rg_id lx.t_groups with
                | true, false -> self_rankscore rx rm lg_id rg_id
                | false, true -> self_rankscore lx lm rg_id lg_id
                | _ ->
                    let result =
                      IntMap.fold
                        (fun key off wacc->
                          let lg_dim =
                            Bi_fun.image (lg_id,key) lx.t_dimensions in
                          let rg_dim =
                            Bi_fun.image (rg_id,key) rx.t_dimensions in
                          let fld_score =
                            fld_weight * (var_compare lg_dim lm rg_dim rm) in
                          wacc + fld_score
                        ) lx.t_fields 0 in
                    let rsz_dim =
                      Bi_fun.image (rg_id,g_size) rx.t_dimensions in
                    let ridx_dim =
                      Bi_fun.image (rg_id,g_index) rx.t_dimensions in
                    let sz_score =
                      sz_weight * (var_compare lsz_dim lm rsz_dim rm) in
                    let idx_score =
                      idx_weight * (var_compare lidx_dim lm ridx_dim rm) in
                    let result = result + sz_score + idx_score in
                    let result =
                      if lg_id = rg_id then result + name_weight
                      else result in
                    let var_score =
                      IntMap.fold
                        (fun v lgs vacc ->
                          if (var_compare v lm v rm) = 2
                              && (IntMap.mem v rx.t_varRes)
                              && (IntSet.mem lg_id lgs) then
                            let rgs = IntMap.find v rx.t_varRes in
                            if (IntSet.mem rg_id rgs) then vacc + var_weight
                            else vacc
                          else vacc
                        ) lx.t_varRes 0 in
                    let freshl = not (IntSet.mem lg_id rx.t_groups) in
                    let freshr = not (IntSet.mem rg_id lx.t_groups) in
                    let result = if freshl && freshr then
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

    (* (\* Split_in_le: *)
    (*  * the split operator used in includesion check, it is special *)
    (*  * since it generates temporary new group/dimension names and *)
    (*  * it need not to be as precise as split in other places. *\) *)
    (* let split_in_le (g_id: int) (ng_id: int) (num: int) *)
    (*     (x: t) (main: Op.t): t * Op.t = *)
    (*   (\* here we use tmp_dim for it is temporary and we do not want *)
    (*    * to let dim_conter increases too fast*\) *)
    (*   let t_index_dim = get_tmp_dim () in *)
    (*   let t_size_dim = get_tmp_dim () in *)
    (*   let dimensions = Bi_fun.add (ng_id,g_size) t_size_dim x.t_dimensions in *)
    (*   let dimensions = Bi_fun.add (ng_id,g_index) t_index_dim dimensions in *)
    (*   let dimensions = *)
    (*     IntMap.fold *)
    (*       (fun key _ acc -> *)
    (*         Bi_fun.add (ng_id,key) (get_tmp_dim ()) acc *)
    (*       ) x.t_fields dimensions in *)
    (*   let ngroups = IntSet.add ng_id x.t_groups in  *)
    (*   let ori_index_dim = Bi_fun.image (g_id,g_index) x.t_dimensions in *)
    (*   let ori_size_dim = Bi_fun.image (g_id,g_size) x.t_dimensions in *)
    (*   let main = Op.expand ori_index_dim t_index_dim main in *)
    (*   let main = Op.add_node t_size_dim false 1 (Some 1) main in *)
    (*   let main = *)
    (*     IntMap.fold *)
    (*       (fun key _ acc -> *)
    (*         let ori_fld_dim = Bi_fun.image (g_id,key) dimensions in *)
    (*         let frsh_fld_dim = Bi_fun.image (ng_id,key) dimensions in *)
    (*         Op.expand ori_fld_dim frsh_fld_dim acc *)
    (*       ) x.t_fields main in *)
    (*   let frsh_agn_expr = Ne_csti num in *)
    (*   let main = Op.update_subs_set t_size_dim frsh_agn_expr main in *)
    (*   let old_agn_expr = *)
    (*     Ne_bin (Texpr1.Sub,Ne_var ori_size_dim, Ne_csti num) in *)
    (*   let main = Op.update_subs_set ori_size_dim old_agn_expr main in *)
    (*   let refreshS elt = *)
    (*     if IntSet.mem g_id elt then IntSet.add ng_id elt *)
    (*     else elt in *)
    (*   let nvarRes = IntMap.map refreshS x.t_varRes in *)
    (*   let nindexRes = IntMap.map refreshS x.t_indexRes in *)
    (*   let nindexRes = *)
    (*     IntMap.fold *)
    (*       (fun key _ acc -> *)
    (*         let ori_fld_dim = Bi_fun.image (g_id, key) dimensions in *)
    (*         if IntMap.mem ori_fld_dim acc then *)
    (*           let tSet = IntMap.find ori_fld_dim acc in *)
    (*           let new_fld_dim = Bi_fun.image (ng_id, key) dimensions in *)
    (*           IntMap.add new_fld_dim tSet acc *)
    (*         else acc *)
    (*       ) x.t_fields nindexRes in *)
    (*   { x with *)
    (*     t_groups = ngroups; *)
    (*     t_indexRes = nindexRes; *)
    (*     t_varRes = nvarRes; *)
    (*     t_dimensions = dimensions; }, main *)

    (* (\* Split operator in materialization: *)
    (*  * it generates permenant fresh group/dimension names, it is also *)
    (*  * more precise than split_in_le *\) *)
    (* let split_in_mt (g_id: int) (ng_id: int) *)
    (*     (var: int) (main: Op.t) (x: t): t * Op.t = *)
    (*   let index_dim = get_new_dim () in *)
    (*   let size_dim = get_new_dim () in *)
    (*   let dimensions = Bi_fun.add (ng_id, g_index) index_dim x.t_dimensions in *)
    (*   let dimensions = Bi_fun.add (ng_id, g_size) size_dim dimensions in *)
    (*   let dimensions = *)
    (*     IntMap.fold *)
    (*       (fun key _ acc -> *)
    (*         Bi_fun.add (ng_id, key) (get_new_dim ()) acc *)
    (*       ) x.t_fields dimensions in *)
    (*   let idx_dim = Bi_fun.image (g_id, g_index) x.t_dimensions in  *)
    (*   let main = Op.update_rem idx_dim (Ne_var var) main in *)
    (*   let ngroups = IntSet.add ng_id x.t_groups in *)
    (*   let ori_size_dim = Bi_fun.image (g_id,g_size) x.t_dimensions in *)
    (*   let idxequal = Nc_cons (Tcons1.EQ,Ne_var  index_dim, Ne_var var) in *)
    (*   let main = Op.add_node index_dim true 1 (Some 1) main in *)
    (*   let main = Op.add_node size_dim  false 1 (Some 1) main in *)
    (*   let main = Op.guard_s true idxequal main in *)
    (*   let frsh_agn_expr = Ne_csti 1 in *)
    (*   let main = Op.update_subs_elt size_dim frsh_agn_expr main in *)
    (*   let main = Op.size_assign index_dim frsh_agn_expr main in *)
    (*   let old_agn_expr = *)
    (*     Ne_bin (Texpr1.Sub,Ne_var ori_size_dim, Ne_csti 1) in *)
    (*   let main = Op.update_subs_elt ori_size_dim old_agn_expr main in *)
    (*   let old_size_cons = *)
    (*     Nc_cons (Tcons1.SUPEQ,Ne_var ori_size_dim,Ne_csti 0) in *)
    (*   let main = Op.guard_s true old_size_cons main in *)
    (*   let main =  *)
    (*     IntMap.fold *)
    (*       (fun key _ acc -> *)
    (*         let ori_fld_dim = Bi_fun.image (g_id,key) dimensions in *)
    (*         let frsh_fld_dim = Bi_fun.image (ng_id,key) dimensions in *)
    (*         let acc = Op.expand ori_fld_dim frsh_fld_dim acc in *)
    (*         Op.scalar_to_single frsh_fld_dim  acc  *)
    (*       ) x.t_fields main in  *)
    (*   (\* can be more precise by comparing the index of new group and each var *\) *)
    (*   let refreshS elt = *)
    (*     if IntSet.mem g_id elt then IntSet.add ng_id elt *)
    (*     else elt in *)
    (*   let nvarRes = IntMap.map refreshS x.t_varRes in *)
    (*   let nindexRes = IntMap.map refreshS x.t_indexRes in *)
    (*   let nindexRes =  *)
    (*     IntMap.fold *)
    (*       (fun key _ acc -> *)
    (*         let ori_fld_dim = Bi_fun.image (g_id,key) dimensions in *)
    (*         if IntMap.mem ori_fld_dim acc then *)
    (*           let tSet = IntMap.find ori_fld_dim acc in *)
    (*           let new_fld_dim = Bi_fun.image (ng_id,key) dimensions in *)
    (*           IntMap.add new_fld_dim tSet acc *)
    (*         else *)
    (*           acc *)
    (*       ) x.t_fields nindexRes in *)
    (*   let nvarRes = IntMap.add var (IntSet.singleton ng_id) nvarRes in *)
    (*   { x with *)
    (*     t_groups = ngroups; *)
    (*     t_indexRes = nindexRes; *)
    (*     t_varRes = nvarRes; *)
    (*     t_dimensions = dimensions; }, main *)


    let split (get_dim: unit -> int ) (g_id: int) (ng_id: int)
        (var: int option) (num: int) (main: Op.t) (x: t): Op.t * t =
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
      let ori_size_dim = Bi_fun.image (g_id,g_size) x.t_dimensions in
      let main = Op.add_node index_dim true 1 (Some 1) main in
      let main = Op.add_node size_dim  false 1 (Some 1) main in
      let main =
        match var with
        | None -> main
        | Some v ->
            let tmain = Op.update_rem ori_index_dim (Ne_var v) main in
            if num = 1 then
              let idxequal = Nc_cons (Tcons1.EQ,Ne_var index_dim, Ne_var v) in
              Op.guard_s true idxequal tmain
            else
              tmain in
      let frsh_agn_expr = Ne_csti num in
      let main = Op.update_subs_elt size_dim frsh_agn_expr main in
      let main = Op.size_assign index_dim frsh_agn_expr main in
      let old_agn_expr =
        Ne_bin (Texpr1.Sub,Ne_var ori_size_dim, Ne_csti num) in
      let main = Op.update_subs_elt ori_size_dim old_agn_expr main in
      let old_size_cons =
        Nc_cons (Tcons1.SUPEQ,Ne_var ori_size_dim,Ne_csti 0) in
      let main = Op.guard_s true old_size_cons main in
      let main =
        IntMap.fold
          (fun key _ acc ->
            let ori_fld_dim = Bi_fun.image (g_id,key) dimensions in
            let frsh_fld_dim = Bi_fun.image (ng_id,key) dimensions in
            let acc = Op.expand ori_fld_dim frsh_fld_dim acc in
            if num = 1 then
              Op.scalar_to_single frsh_fld_dim  acc
            else
              acc
          ) x.t_fields main in
      (* can be more precise by comparing the index of new group and each var *)
      let refreshS elt =
        if IntSet.mem g_id elt then IntSet.add ng_id elt
        else elt in
      let nvarRes = IntMap.map refreshS x.t_varRes in
      let nindexRes = IntMap.map refreshS x.t_indexRes in
      let nindexRes =
        IntMap.fold
          (fun key _ acc ->
            let ori_fld_dim = Bi_fun.image (g_id,key) dimensions in
            if IntMap.mem ori_fld_dim acc then
              let tSet = IntMap.find ori_fld_dim acc in
              let new_fld_dim = Bi_fun.image (ng_id,key) dimensions in
              IntMap.add new_fld_dim tSet acc
            else
              acc
          ) x.t_fields nindexRes in
      let nvarRes =
        match var with
        | None -> nvarRes
        | Some v -> IntMap.add v (IntSet.singleton ng_id) nvarRes in
      main,{ x with
        t_groups = ngroups;
        t_indexRes = nindexRes;
        t_varRes = nvarRes;
        t_dimensions = dimensions; }





     (* Check whether predicates on arrays are satisfied  *)
    let array_check  (x: t) (main: Op.t): bool =
      match x.t_predicate with
      | OnePred pt -> Pred.pred_check x.t_dimensions main pt
      | _ -> true

    (* Operator Merge:
     * Merge two groups into one group, the properties of the new group is the
     * over-approximation of the two old groups*)
    let merge (gl: int) (gr: int) (x: t) (main: Op.t): t * Op.t =
      Log.debug "merge phase gl is %d gr is %d" gl gr;
      (* about prdicate  *)
      let x,main =
        match x.t_predicate with
        | OnePred pt ->
            let tmain,npt = Pred.merge gl gr main pt in
            { x with t_predicate = OnePred npt }, tmain
        | _ -> x,main in
      let merge_dim (key: int) (m: Op.t)=
        let l_fld_dim = Bi_fun.image (gl,key) x.t_dimensions in
        let r_fld_dim = Bi_fun.image (gr,key) x.t_dimensions in
        Op.compact l_fld_dim r_fld_dim m in
      let main =
        IntMap.fold (fun key _ acc -> merge_dim key acc) x.t_fields main in
      let l_sz_dim = Bi_fun.image (gl,g_size) x.t_dimensions in
      let r_sz_dim = Bi_fun.image (gr,g_size) x.t_dimensions in
      let sz_expr = Ne_bin (Texpr1.Add,Ne_var l_sz_dim,Ne_var r_sz_dim) in
      let main = Op.update_subs_elt l_sz_dim sz_expr main in
      (* Format.printf "merge phase 2 is \n %s\n"  *)
      (*   (Op.t_2stri IntMap.empty "" main); *)
      let main = Op.rem_node r_sz_dim main in
      (* Format.printf "merge phase 3 is \n %s\n"  *)
      (*    (Op.t_2stri IntMap.empty "" main); *)
      let main = merge_dim g_index main in
      (* Format.printf "merge phase 4 is \n %s\n"  *)
      (*    (Op.t_2stri IntMap.empty "" main); *)
      let refreshS  elt =
        if IntSet.mem gr elt then
          IntSet.add gl (IntSet.remove gr elt)
        else
          elt in
      let nvarRes = IntMap.map refreshS x.t_varRes in
      let nindexRes = IntMap.map refreshS x.t_indexRes in
      let nindexRes =
        IntMap.fold
          (fun key _ acc ->
            let l_fld_dim = Bi_fun.image (gl,key) x.t_dimensions in
            let r_fld_dim = Bi_fun.image (gr,key) x.t_dimensions in
            if IntMap.mem r_fld_dim nindexRes then
              let r_set = IntMap.find r_fld_dim acc in
              let acc =
                if IntMap.mem l_fld_dim nindexRes then
                  let l_set = IntMap.find l_fld_dim acc in
                  IntMap.add l_fld_dim (IntSet.union l_set r_set) acc
                else
                  IntMap.add l_fld_dim  r_set acc in
              IntMap.remove r_fld_dim acc
            else
              acc
          ) x.t_fields nindexRes in
      let ndimensions =
        IntMap.fold
          (fun key _ acc ->
            Bi_fun.rem_dir (gr,key) acc
          ) x.t_fields x.t_dimensions in
      let ndimensions = Bi_fun.rem_dir (gr,g_size) ndimensions in
      let ndimensions = Bi_fun.rem_dir (gr,g_index) ndimensions in
      let ngroups = IntSet.remove gr x.t_groups in
      let x =
        { x with
          t_groups = ngroups ;
          t_dimensions = ndimensions;
          t_varRes = nvarRes ;
          t_indexRes = nindexRes; } in
      let main = nc_size x main in
      x, main

    (* Operator Create:
     * Create a new group of 0 elements, all its properties are from
     * model (the corresponding group in join algorithm). *)
    let create (fresh: int) (model: int) (main: Op.t) (x: t)
        (model_m: Op.t) (model_x: t): Op.t * t =
      ljc_debug "ljc create is called\n";
      let index_dim = get_new_dim () in
      let size_dim = get_new_dim () in
      let ndimensions = Bi_fun.add (fresh,g_size) size_dim x.t_dimensions in
      let ndimensions = Bi_fun.add (fresh,g_index) index_dim ndimensions in
      let cons_size = Nc_cons (Tcons1.EQ,(Ne_var size_dim),(Ne_csti 0)) in
      let main = Op.add_node size_dim  false 1 (Some 1) main in
      let main = Op.add_node index_dim  true  0 (Some 0) main in
      let main = Op.guard_s true cons_size main in
      let ndimensions,main =
        IntMap.fold
          (fun key _ (tdimensions, tmain) ->
            let ndim = get_new_dim () in
            (* ljc_caution: the constraints from model_m may not be recorded *)
            let tmain = Op.add_node ndim false 0 (Some 0) tmain in
            let odim = Bi_fun.image (model,key) model_x.t_dimensions in
            let tdimensions =
              Bi_fun.add (fresh,key) ndim tdimensions in
            let tmain = cons_copy odim model_m ndim tmain in
            tdimensions,tmain
          ) x.t_fields (ndimensions,main) in
      let ngroups = IntSet.add fresh x.t_groups in
      let nindexRes =
        IntMap.fold
          (fun key off acc ->
            let dim = Bi_fun.image (fresh,key) ndimensions in
            IntMap.add dim IntSet.empty acc
          ) x.t_fields x.t_indexRes in
      let nx = { x with
                 t_groups = ngroups;
                 t_indexRes = nindexRes;
                 t_dimensions = ndimensions; } in
      main, nx

    (* Operator Rename:
     * Give a fresh name to a group. This operator is used to make
     * groups in two states have the same set of names*)
    let rename_group (lold: int) (rold: int) (fresh: int) (lm:Op.t) (lx: t)
        (rm: Op.t) (rx: t): Op.t * t * Op.t * t =
      Log.debug "before rename";
      let lm,lx,rm,rx =
        match lx.t_predicate,rx.t_predicate with
        | OnePred lpt, OnePred rpt ->
          let lm,lpt,rm,rpt = Pred.rename lold rold fresh lm lpt rm rpt in
          lm, { lx with t_predicate = OnePred lpt },
          rm, { rx with t_predicate = OnePred rpt }
        | _ -> lm,lx,rm,rx in
      Log.debug "after ranme";
      let index_dim = get_new_dim () in
      let size_dim = get_new_dim () in
      let update_spcl old fresh sdim idim m x =
        let osize_dim = Bi_fun.image (old,g_size) x.t_dimensions in
        let oindex_dim = Bi_fun.image (old,g_index) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old,g_size) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old,g_index) ndimens in
        let ndimens = Bi_fun.add (fresh,g_size) size_dim ndimens in
        let ndimens = Bi_fun.add (fresh,g_index) index_dim ndimens in
        let nm = Op.rename_var osize_dim sdim m in
        let nm = Op.rename_var oindex_dim idim nm in
        let x = { x with t_dimensions = ndimens } in
        nm,x in
      let lm,lx = update_spcl lold fresh size_dim index_dim lm lx in
      let rm,rx = update_spcl rold fresh size_dim index_dim  rm rx in
      let fldim =
        IntMap.fold (fun key off acc -> IntMap.add key (get_new_dim ()) acc)
          lx.t_fields IntMap.empty in
      let update_fld old fresh fd m x =
        let ndimens,nm,nidxRes =
          IntMap.fold
            (fun key dim (tdimens, tm, tidxRes) ->
              let odim = Bi_fun.image (old,key) tdimens in
              let tdimens = Bi_fun.rem_dir (old,key) tdimens in
              let tdimens = Bi_fun.add (fresh,key) dim tdimens in
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
        nm,x in
      let lm,lx = update_fld lold fresh fldim lm lx in
      let rm,rx = update_fld rold fresh fldim rm rx in
      let re_in_group old fresh gp =
        if IntSet.mem old gp then
          let gp = IntSet.remove old gp in
          IntSet.add fresh gp
        else
          gp in
      let lngroups = re_in_group lold fresh lx.t_groups in
      let rngroups = re_in_group rold fresh rx.t_groups in
      let lnvarRes = IntMap.map (re_in_group lold fresh) lx.t_varRes in
      let rnvarRes = IntMap.map (re_in_group rold fresh) rx.t_varRes in
      let lnidxRes = IntMap.map (re_in_group lold fresh) lx.t_indexRes in
      let rnidxRes = IntMap.map (re_in_group rold fresh) rx.t_indexRes in
      let lx = { lx with
                 t_groups = lngroups ;
                 t_varRes = lnvarRes ;
                 t_indexRes = lnidxRes;} in
      let rx = { rx with
                 t_groups = rngroups ;
                 t_varRes = rnvarRes ;
                 t_indexRes = rnidxRes;} in
      lm,lx,rm,rx

    (* The only difference between rename_group_in_le and rename_group is
     * that is uses temporary dimension names  *)
    let rename_group_in_le (lold: int) (rold: int) (fresh: int) (lm:Op.t)
        (lx: t) (rm: Op.t) (rx: t): Op.t * t * Op.t * t =
      let size_dim = get_tmp_dim () in
      let index_dim = get_tmp_dim () in
      let update_spcl old fresh m x =
        let osize_dim = Bi_fun.image (old,g_size) x.t_dimensions in
        let oindex_dim = Bi_fun.image (old,g_index) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old,g_size) x.t_dimensions in
        let ndimens = Bi_fun.rem_dir (old,g_size) ndimens in
        let ndimens = Bi_fun.add (fresh,g_size) size_dim ndimens in
        let ndimens = Bi_fun.add (fresh,g_index) index_dim ndimens in
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
        let ndimens,nm,nidxRes =
          IntMap.fold
            (fun key dim (tdimens, tm, tidxRes) ->
              let odim = Bi_fun.image (old,key) tdimens in
              let tdimens = Bi_fun.rem_dir (old,key) tdimens in
              let tdimens = Bi_fun.add (fresh,key) dim tdimens in
              let tm = Op.rename_var odim dim tm in
              let tidxRes =
                if IntMap.mem odim tidxRes then
                  let g = IntMap.find odim tidxRes in
                  let tidxRes = IntMap.remove odim tidxRes in
                  IntMap.add dim g tidxRes
                else
                  tidxRes in
              (tdimens, tm, tidxRes)
            ) fd (x.t_dimensions,m,x.t_indexRes) in
        let x = { x with
                  t_dimensions = ndimens;
                  t_indexRes = nidxRes; } in
        nm,x in
      let lm,lx = update_fld lold fresh fldim lm lx in
      let rm,rx = update_fld rold fresh fldim rm rx in
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
      let lx = { lx with
                 t_groups = lngroups ;
                 t_varRes = lnvarRes ;
                 t_indexRes = lnidxRes;} in
      let rx = { rx with
                 t_groups = rngroups ;
                 t_varRes = rnvarRes ;
                 t_indexRes = rnidxRes;} in
      lm, lx, rm, rx

    (* Propatege in relation to numeric part, mainly the index information. *)
    let rlvar_2num (var: int)  (array: t) (main: Op.t): Op.t =
      let groups = IntMap.find var array.t_varRes in
      let group = IntSet.choose groups in
      let nm =
        IntSet.fold
          (fun key m ->
            if IntSet.mem key groups then m
            else
              let dim_index = Bi_fun.image (key,g_index) array.t_dimensions in
              let lwer = Nc_cons (Tcons1.SUP,(Ne_var dim_index),(Ne_var var)) in
              let uper = Nc_cons (Tcons1.SUP,(Ne_var var),(Ne_var dim_index)) in
              let m1 = Op.guard_s true uper m in
              let m2 = Op.guard_s true lwer m in
              (* Format.printf "key is %d, m1 is \n %s\n" key (Op.t_2stri IntMap.empty "" m1 ); *)
              (* Format.printf "key is %d, m2 is \n %s\n" key (Op.t_2stri IntMap.empty "" m2 ); *)
              let m1 = Op.assert_non_empty dim_index m1 in
              let m2 = Op.assert_non_empty dim_index m2 in
              Op.upper_bnd Jjoin m1 m2
          ) array.t_groups main in
      let index_dim = Bi_fun.image (group, g_index) array.t_dimensions in
      Op.assert_non_empty index_dim nm

    (* Derive relation information from numeric part *)
    let num_2rl (main: Op.t)  (var: int) (x: t) : t =
      let lwer = Nc_cons (Tcons1.SUP,(Ne_csti 0),(Ne_var var)) in
      let uper = Nc_cons (Tcons1.SUPEQ,(Ne_var var),(Ne_csti x.t_size))  in
      let domlw = Op.guard_w true uper main in
      let domup = Op.guard_w true lwer main in
      if not (Op.is_bot domlw) || not (Op.is_bot domup) then
        x
      else
        let groups, issole =
          IntSet.fold
            (fun g_id acc ->
              let tg,found = acc in
              if found then
                acc
              else
                let dim_index = Bi_fun.image (g_id,g_index) x.t_dimensions in
                let eq = Nc_cons (Tcons1.EQ,(Ne_var var),(Ne_var dim_index)) in
                let tm = Op.assert_non_empty dim_index main in
                let domeq = Op.guard_w true eq tm in
                if Op.is_bot domeq then
                  acc
                else
                  let up =
                    Nc_cons (Tcons1.SUP,(Ne_var var),(Ne_var dim_index)) in
                  let low =
                    Nc_cons (Tcons1.SUP,(Ne_var dim_index),(Ne_var var)) in
                  let domup = Op.guard_w true up main in
                  let domlow = Op.guard_w true low main in
                  let domneq = (Op.is_bot domup) && (Op.is_bot domlow) in
                  let index = Op.bound_variable dim_index main in
                  let dim_size = Bi_fun.image (g_id,g_size) x.t_dimensions in
                  let size = Op.bound_variable dim_size main in
                  let g1 = IntSet.add g_id tg in
                  let g2 = IntSet.singleton g_id in
                  let tf =
                    match domneq,size.intv_inf,size.intv_sup with
                    | true, Some si, Some ss ->
                        begin
                          match index.intv_inf,index.intv_sup with
                          | Some ii, Some is -> si = (is - ii + 1) && si = ss
                          | _,_ -> false
                        end
                    | _, _, _ -> false in
                  if tf then g2, tf
                  else g1, tf
            ) x.t_groups (IntSet.empty,false) in
        let ogroups =
          try IntMap.find var x.t_varRes
          with Not_found -> x.t_groups in
        (* TODO: More precise inference,
         * e.g. IN cleanup,if parent = 2, and index_1 = 2, then
         * parent \in S_1 *)
        let nvarRes = IntMap.add var (IntSet.inter groups ogroups) x.t_varRes in
        { x with t_varRes = nvarRes }

    (* Maybe it is not needed with new numeric domain *)
    (* Get the index relations after an assignment on summary dimension, *)
    (* now only deal with  expression with non-summary dimensions *)
    let num_2rl_sum (dst_sum: int) (expr: n_expr) (main: Op.t) (array: t): t =
      match expr with
      | Ne_var var ->
          let array = num_2rl main var array in
          if IntMap.mem var array.t_varRes then
            let group = IntMap.find var array.t_varRes in
            let nindexRes = IntMap.add dst_sum group array.t_indexRes in
            { array with t_indexRes = nindexRes }
          else
            array
      | _ ->
          let lwer = Nc_cons (Tcons1.SUP,(Ne_csti 0),(Ne_var dst_sum)) in
          let uper =
            Nc_cons (Tcons1.SUPEQ,(Ne_var dst_sum),(Ne_csti array.t_size)) in
          let domlw = Op.guard_w true uper main in
          let domup = Op.guard_w true lwer main in
          if not (Op.is_bot domlw) || not (Op.is_bot domup) then array
          else
            let groups, _ =
              IntSet.fold
                (fun g_id acc ->
                  let tg,found = acc in
                  if found then
                    acc
                  else
                    let dim = Bi_fun.image (g_id,g_index) array.t_dimensions in
                    let eq =
                      Nc_cons (Tcons1.EQ,(Ne_var dst_sum),(Ne_var dim)) in
                    let tm = Op.assert_non_empty dim  main in
                    let domeq = Op.guard_w true eq tm in
                    if Op.is_bot domeq  then
                      acc
                    else
                      let up =
                        Nc_cons (Tcons1.SUP,(Ne_var dst_sum),(Ne_var dim)) in
                      let low =
                        Nc_cons (Tcons1.SUP,(Ne_var dim),(Ne_var dst_sum)) in
                      (* ljc_caution a problem appears... *)
                      let domup = Op.guard_w true up main in
                      let domlow = Op.guard_w true low main in
                      let domneq = (Op.is_bot domup) && (Op.is_bot domlow) in
                      let index = Op.bound_variable dim main in
                      let size = Op.bound_variable dim main in
                      let g1 = IntSet.add g_id tg in
                      let g2 = IntSet.singleton g_id in
                      let tf =
                        match domneq,size.intv_inf,size.intv_sup with
                        | true, Some si, Some ss ->
                            begin
                              match index.intv_inf,index.intv_sup with
                              | Some ii, Some is ->
                                  si = (is - ii + 1) && si = ss
                              | _,_ -> false
                            end
                        | _, _, _ -> false in
                      if tf then
                        g2,tf
                      else
                        g1,tf
                ) array.t_groups (IntSet.empty,false) in
            (* TODO: More precise inference,
             * e.g. IN cleanup,if parent = 2, and index_1 = 2, then
             * parent \in S_1 *)
            let nindexRes = IntMap.add dst_sum groups array.t_indexRes in
            { array with t_indexRes = nindexRes }


    (** Transfer functions *)

    (* Guard *)
    let guard (typ: bool) (cons: n_cons) (main: Op.t) (x: t): t =
      n_cons_fold (num_2rl main) cons x

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
      let cst,lin =
        match off with
        | Ne_bin (Texpr1.Add,(Ne_csti cst),lin) -> cst,lin
        | lin -> 0,lin in
      let ali,var =
        match lin with
        | Ne_bin (Texpr1.Mul,(Ne_csti ali),(Ne_var var))-> ali,var
        | _ -> Log.fatal_exn "unexpected case in deref linexpr" in
      (* for now we only deals with variables as index  *)
      assert(cst < array.t_align);
      let fld,left =
        IntMap.fold
          (fun key sz acc ->
            let k,left = acc in
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
      let fld,var = resolve array off in
      let array = num_2rl  main var array in
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
          let dim = Bi_fun.image (g_id,fld) narr.t_dimensions in
          (dim, nmain, narr) :: acc
        ) groups []

    (* For a variable, if the groups it belongs to is not determinestic
     * then merge all possible groups;
     * to make the l-value a non-summarizing dimension, split a group
     * which contains only the index varialbe *)
    let materialize (array: t) (off: Offs.t) (main: Op.t): t * Op.t * int =
      let fld,var = resolve array off in
      let array = num_2rl main var array in
      let groups =
        try IntMap.find var array.t_varRes
        with Not_found -> Log.fatal_exn "Out of bound access found\n" in
      let dstgroup = IntSet.choose groups in
      let groups = IntSet.remove dstgroup groups in
      let array,main =
        IntSet.fold
          (fun group acc ->
            let tp_array,tp_main = acc in
            merge dstgroup group tp_array tp_main
          ) groups (array, main) in
      let array,main = rlgroup_2num dstgroup array main in
      let sz_dim = Bi_fun.image (dstgroup,g_size) array.t_dimensions in
      let cons = Nc_cons (Tcons1.EQ,Ne_var sz_dim,Ne_csti 1) in
      let array,main,ngroup =
        if not (Op.sat_s main cons) then
          let ng = get_new_group () in
          let main,array =
            split get_new_dim dstgroup ng (Some var) 1  main array in
          array, main,ng
        else array, main, dstgroup in
      (* start predicate *)
      let npredt,main =
        match array.t_predicate with
        | Uninitialized ->
            begin
              match !hint_array_pred with
              | None ->  NoPred,main
              | Some ap ->
                  if Pred.is_applicable ap then
                    let predt = Pred.initialize ap in
                    let tmain,tpredt =
                      Pred.materialize array.t_dimensions ngroup
                        main predt in
                    OnePred tpredt,tmain
                  else
                    NoPred,main
            end
        | NoPred -> NoPred,main
        | OnePred predt ->
            let tmain,tpredt =
              Pred.materialize array.t_dimensions ngroup main predt in
            OnePred tpredt,tmain in
      let array = { array with t_predicate = npredt } in
      (* end predicate*)
      let dim = Bi_fun.image (ngroup,fld) array.t_dimensions in
      array, main, dim


    let rem_all_predicates (main: Op.t) (x: t): Op.t * t =
      match x.t_predicate with
      | OnePred pt ->
          let nmain,npt = Pred.rem_all_predicates main pt in
          nmain,{x with t_predicate = OnePred npt}
      | _ -> main,x



    (* Special case for split a new group in guard, this function
     * will be eliminated after we have implemented the new materialization
     * scheme *)
    let split_on_guard (iseq: Tcons1.typ) (array: t) (main: Op.t)
       (off: Offs.t) (v2: int): t * Op.t * bool =
      let groups =
        try IntMap.find v2 array.t_varRes with Not_found -> IntSet.empty in
      if IntSet.cardinal groups = 1 then
        let group = IntSet.choose groups in
        let sdim = Bi_fun.image (group,g_size) array.t_dimensions in
        let up = Nc_cons (Tcons1.SUP,Ne_var sdim, Ne_csti 1) in
        let low = Nc_cons (Tcons1.SUP,Ne_csti 1,Ne_var sdim) in
        let upstate = Op.guard_s true up main in
        let lowstate = Op.guard_s true low main in
        if Op.is_bot upstate && Op.is_bot lowstate then
          (* ljc: caution here. no predicate added here *)
          let array, main, dim = materialize array off main in
          match iseq with
          | Tcons1.EQ ->
              let nindexRes = IntMap.add dim groups array.t_indexRes in
              let array = { array with t_indexRes = nindexRes } in
              array, main, true
          | Tcons1.DISEQ ->
              let ngroups = IntMap.find dim array.t_indexRes in
              let ngroups = IntSet.diff ngroups groups in
              let nindexRes = IntMap.add dim ngroups array.t_indexRes in
              let array = { array with t_indexRes = nindexRes } in
              array, main, true
          | _ -> array, main, true
        else
          array, main, false
      else
        array, main, false


    (* Remove the groups that contain 0 element *)
    let cleanup (x: t) (main: Op.t): t * Op.t =
      IntSet.fold
        (fun g_id acc->
          let tx,tmain = acc in
          if Op.is_bot tmain then
            acc
          else
            let idx = Bi_fun.image (g_id, g_index) x.t_dimensions in
            if Op.is_bot (Op.assert_non_empty idx main) then
              let dim = Bi_fun.image (g_id, g_size) tx.t_dimensions in
              let cons = Nc_cons (Tcons1.EQ, Ne_var dim, Ne_csti 0) in
              if not (Op.is_bot (Op.guard_s true cons tmain)) then
                let ngroups = IntSet.remove g_id tx.t_groups in
                let ndimensions,dims =
                  IntMap.fold
                    (fun key _ acc ->
                      let tndim,tdims = acc in
                      let kdim = Bi_fun.image (g_id, key) tndim in
                      let tndim = Bi_fun.rem_dir (g_id, key) tndim in
                      let tdims = IntSet.add kdim tdims in
                      tndim,tdims
                    ) tx.t_fields (tx.t_dimensions,IntSet.empty) in
                let ndimensions = Bi_fun.rem_dir (g_id, g_size) ndimensions in
                let ndimensions = Bi_fun.rem_dir (g_id, g_index) ndimensions in
                let nindexRes =
                  IntSet.fold IntMap.remove dims tx.t_indexRes in
                let nindexRes = IntMap.map (IntSet.remove g_id) nindexRes in
                let nvarRes = IntMap.map (IntSet.remove g_id) tx.t_varRes in
                let nmain = IntSet.fold Op.rem_node dims main in
                let nmain = Op.rem_node dim nmain in
                let nmain = Op.rem_node idx nmain in
                let nx = { tx with
                           t_groups = ngroups;
                           t_dimensions = ndimensions;
                           t_indexRes = nindexRes;
                           t_varRes = nvarRes;} in
                nx,nmain
              else tx, Op.bot
            else acc
        ) x.t_groups (x, main)

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
      let lmap,rmap =
        IntSet.fold
          (fun key acc ->
            let ltmap,rtmap = acc in
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
          ) la.t_groups (lmap,rmap) in
      (* split phase *)
      let size_bound (x: t) (m: Op.t) (g: int): int =
        let dim = Bi_fun.image (g,g_size) x.t_dimensions in
        let bound = Op.bound_variable dim m in
        match bound.intv_inf with
        | None -> Log.fatal_exn "size bound error"
        | Some i -> i in
      let lmap, rmap, la, lm =
        IntMap.fold
          (fun key set acc ->
            let tlmap,trmap,tla,tlm = acc in
            if IntSet.cardinal set > 1 then
              let host =
                if IntSet.mem key set then
                  key
                else
                  IntSet.choose set in
              let tlmap = IntMap.add key (IntSet.singleton host) tlmap in
              let trmap = IntMap.add host (IntSet.singleton key) trmap in
              let set = IntSet.remove key set in
              IntSet.fold
                (fun elt iacc ->
                  let ilmap,irmap,ila,ilm = iacc in
                  let ng_id = get_tmp_dim () in
                  let l_size = size_bound ila ilm key in
                  let r_size = size_bound ra rm elt in
                  let num = if l_size >= r_size then r_size else 0 in
                  let ilm,ila =
                    split get_tmp_dim key ng_id None num  ilm ila in
                  let ilmap =
                    IntMap.add ng_id (IntSet.singleton elt) ilmap in
                  let irmap =
                    IntMap.add elt (IntSet.singleton ng_id) irmap in
                  ilmap,irmap,ila,ilm
                ) set (tlmap,trmap,tla,tlm)
            else
              acc
          ) lmap (lmap, rmap, la, lm) in
      (* create phase*)
      let lmap,rmap,la,lm =
        IntSet.fold
          (fun elt acc ->
            let tlmap,trmap,tla,tlm = acc in
            if IntMap.mem elt trmap then
              acc
            else
              let fresh = get_tmp_dim () in
              let tlm,tla = create fresh elt tlm tla rm ra in
              let trmap = IntMap.add elt (IntSet.singleton fresh) trmap in
              let tlmap = IntMap.add fresh (IntSet.singleton elt) tlmap in
              tlmap,trmap,tla,tlm
          ) ra.t_groups (lmap,rmap,la,lm) in
      (* merge phase*)
      let merge_phase lmap rmap ra rm =
        IntMap.fold
          (fun key set acc ->
            let tlmap,trmap,tra,trm = acc in
            if IntSet.cardinal set > 1 then
              let host = IntSet.choose set in
              let set = IntSet.remove host set in
              let trmap,tra,trm =
                IntSet.fold
                  (fun elt acc ->
                    let irmap, ira,irm = acc in
                    let ira,irm =  merge host elt ira irm in
                    let irmap = IntMap.remove elt irmap in
                    irmap, ira, irm
                  ) set (trmap,tra,trm) in
              let set = IntSet.singleton host in
              let tlmap = IntMap.add key set tlmap in
              tlmap,trmap,tra,trm
            else acc
          ) lmap (lmap, rmap, ra, rm) in
      let rmap, lmap, la, lm = merge_phase rmap lmap la lm in
      (* rename phase *)
      IntMap.fold
        (fun lid rid acc ->
          let lm,la,rm,ra = acc in
          let rid = IntSet.choose rid in
          if lid = rid then acc
          else
            let fresh = get_tmp_dim () in
            rename_group_in_le lid rid fresh lm la rm ra
        ) lmap (lm,la,rm,ra)

    (* Apply operators split,create on two states to make them ready for join*)
    let apply_joinmap (rankscore: (int * int * int) list) (la: t)
       (lm: Op.t) (ra: t) (rm: Op.t):  Op.t * t * Op.t * t=
      Log.debug "join map";
      let lg_num = IntSet.cardinal la.t_groups in
      let rg_num = IntSet.cardinal ra.t_groups in
      let g_num = if lg_num > rg_num then lg_num else rg_num  in
      let threhold = 7 in
      (* Selection of pairs *)
      let cmp a b =
        let a1,a2,a3 = a in
        let b1,b2,b3 = b in
        if a3 > b3 then -1
        else if a3 < b3 then 1
        else 0 in
      let rankscore = List.sort cmp rankscore in
      let rankscore =
        List.fold_left
          (fun acc elt ->
            let al,num = acc in
            let e1,e2,e3 = elt in
            if num < 1 || e3 < threhold then
              acc
            else
              elt::al,(num - 1)
          ) ([],g_num) rankscore in
      let rankscore,num = rankscore in
      (*extract pairs  *)
      let lmap,rmap =
        List.fold_left
          (fun acc elt->
            let ltmap,rtmap = acc in
            let (el,er,e3) = elt in
            let lext = IntMap.mem el ltmap in
            let rext = (IntMap.mem er rtmap) in
            match lext,rext with
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
            | false,false ->
                let ltmap = IntMap.add el (IntSet.singleton er) ltmap in
                let rtmap = IntMap.add er (IntSet.singleton el) rtmap in
                ltmap, rtmap
          ) (IntMap.empty, IntMap.empty) rankscore in
      Log.debug "%s" (ljc_map_2str lmap);
      let lmap,rmap =
        IntSet.fold
          (fun key acc ->
            let ltmap, rtmap = acc in
            if IntMap.mem key ltmap then
              let set = IntMap.find key ltmap in
              if IntSet.cardinal set > 1 then
                IntSet.fold
                  (fun elt iacc ->
                    let lt,rt = iacc in
                    let lset = IntMap.find key lt in
                    if IntSet.cardinal lset > 1 then
                      let rset = IntMap.find elt rt in
                      if IntSet.cardinal rset > 1 then
                        let lset = IntSet.remove elt lset in
                        let rset = IntSet.remove key rset in
                        let lt = IntMap.add key lset lt in
                        let rt = IntMap.add elt rset rt in
                        lt,rt
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
            let tlmap,trmap,tra,trm = acc in
            if IntSet.cardinal set > 1 then
              let host = IntSet.choose set in
              let set = IntSet.remove host set in
              let trmap,tra,trm =
                IntSet.fold
                  (fun elt acc ->
                    let irmap, ira,irm = acc in
                    let ira,irm = merge host elt ira irm in
                    let irmap = IntMap.remove elt irmap in
                    irmap, ira, irm
                  ) set (trmap,tra,trm) in
              let set = IntSet.singleton host in
              let tlmap = IntMap.add key set tlmap in
              tlmap,trmap,tra,trm
            else acc
          ) lmap (lmap,rmap,ra,rm) in
      let lmap,rmap,ra,rm = merge_phase lmap rmap ra rm in
      let rmap,lmap,la,lm = merge_phase rmap lmap la lm in
      (* create phase*)
      let create_phase  lmap rmap la lm ra rm =
        IntSet.fold
          (fun elt acc ->
            let tlmap,trmap,tra,trm = acc in
            if IntMap.mem elt tlmap then acc
            else
              let fresh = get_new_group () in
              let trm,tra = create fresh elt trm tra lm la in
              let tlmap = IntMap.add elt (IntSet.singleton fresh) tlmap in
              let trmap = IntMap.add fresh (IntSet.singleton elt) trmap in
              tlmap,trmap,tra,trm
          ) la.t_groups (lmap,rmap,ra,rm) in
      let lmap,rmap,ra,rm = create_phase lmap rmap la lm ra rm in
      let rmap,lmap,la,lm = create_phase rmap lmap ra rm la lm in
      (* rename phase *)
      IntMap.fold
        (fun lid rid acc ->
          let lm,la,rm,ra = acc in
          let rid = IntSet.choose rid in
          if lid = rid then acc
          else
            let fresh = get_new_group () in
            rename_group lid rid fresh lm la rm ra
        ) lmap (lm, la, rm, ra)

    (* apply operators split,create,merge on two states to make them
     * ready for widen *)
    let apply_widenmap (rankscore: (int * int * int) list) (la: t)
        (lm: Op.t) (ra: t) (rm: Op.t)
        : Op.t * t * Op.t * t =
      (* Selection of pairs *)
      Log.debug "apply widenmap";
      let cmp a b =
        let a1,a2,a3 = a in
        let b1,b2,b3 = b in
        if a3 > b3 then -1
        else if a3 < b3 then 1
        else 0 in
      let rankscore = List.sort cmp rankscore in
      (*extract pairs  *)
      let lmap,rmap =
        List.fold_left
          (fun acc elt ->
            let ltmap,rtmap = acc in
            let (el,er,e3) = elt in
            let lext = IntMap.mem el ltmap in
            let rext = (IntMap.mem er rtmap) in
            match lext,rext with
            | true,true -> acc
            | true,false ->
                let set = IntMap.find el ltmap in
                let set = IntSet.add er set in
                let ltmap = IntMap.add el set ltmap in
                let rtmap = IntMap.add er (IntSet.singleton el) rtmap in
                ltmap, rtmap
            | false,true ->
                let set = IntMap.find er rtmap in
                let set = IntSet.add el set in
                let rtmap = IntMap.add er set rtmap in
                let ltmap = IntMap.add el (IntSet.singleton er) ltmap in
                ltmap, rtmap
            | false,false ->
                let ltmap = IntMap.add el (IntSet.singleton er) ltmap in
                let rtmap = IntMap.add er (IntSet.singleton el) rtmap in
                ltmap, rtmap
          ) (IntMap.empty,IntMap.empty) rankscore in
      (* eliminate the chain case like l1-r1 l2-r1 l2-r2 *)
      let lmap, rmap =
        IntSet.fold
          (fun key acc ->
            let ltmap,rtmap = acc in
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
          ) la.t_groups (lmap,rmap) in
      Log.debug "widen map is\n%s" (ljc_map_2str lmap);
      Log.debug "before merge rm is\n%s" (Op.t_2stri IntMap.empty "" rm);
      (* merge phase*)
      let merge_phase lmap rmap ra  rm =
        IntMap.fold
          (fun key set acc ->
            let tlmap,trmap,tra,trm = acc in
            if IntSet.cardinal set > 1 then
              let host = IntSet.choose set in
              let set = IntSet.remove host set in
              let trmap,tra,trm =
                IntSet.fold
                  (fun elt acc ->
                    let irmap, ira,irm = acc in
                    let ira,irm = merge host elt ira irm in
                    let irmap = IntMap.remove elt irmap in
                    irmap, ira, irm
                  ) set (trmap,tra,trm) in
              let set = IntSet.singleton host in
              let tlmap = IntMap.add key set tlmap in
              tlmap,trmap,tra,trm
            else acc
          ) lmap (lmap,rmap,ra,rm) in
      let lmap,rmap,ra,rm = merge_phase lmap rmap ra rm in
      let rmap,lmap,la,lm = merge_phase rmap lmap la lm in
      (* Format.printf "after merge rm is \n %s\n"  *)
      (*   (Op.t_2stri IntMap.empty "" rm); *)
      (* rename phase *)
      Log.debug "after merge";
      IntMap.fold
        (fun lid rid acc ->
          let lm,la,rm,ra = acc in
          let rid = IntSet.choose rid in
          if lid = rid then
            match la.t_predicate,ra.t_predicate with
            | OnePred lpt,OnePred rpt ->
               let lm,lpt,rm,rpt =  Pred.rename lid rid lid lm lpt rm rpt in
               lm, { la with t_predicate = OnePred lpt },
               rm, { ra with t_predicate = OnePred rpt }
            | _ -> lm,la,rm,ra
          else
           let fresh = get_new_group () in
           rename_group lid rid fresh lm la rm ra
        ) lmap (lm,la,rm,ra)

    (* specific for minix properties *)
    (* let minix_property (x: t) (main: Op.t): t * Op.t = *)
    (*   let ng = get_new_group () in *)
    (*   let ngroups = IntSet.add ng x.t_groups in *)
    (*   let g1_index_dim = get_new_dim () in *)
    (*   let g1_size_dim = get_new_dim () in *)
    (*   let ndimens,nmain = *)
    (*     List.fold_left *)
    (*       (fun ia ie -> *)
    (*         let idims,imain = ia in *)
    (*         let ndim = get_new_dim () in  *)
    (*         let idims = Bi_fun.add (1,ie) ndim idims in *)
    (*         let old_dim = Bi_fun.image (0,ie) idims in *)
    (*         let imain = Op.add_node ndim false 0 None imain in *)
    (*         let imain = Op.scalar_to_exist old_dim imain in *)
    (*         idims,imain *)
    (*       ) (x.t_dimensions, main) [1; 2] in *)
    (*   let ndimens = Bi_fun.add (1,g_size) g1_size_dim ndimens in *)
    (*   let nmain = Op.add_node g1_size_dim false 1 (Some 1) nmain in *)
    (*   let ndimens = Bi_fun.add (1,g_index) g1_index_dim ndimens in *)
    (*   let old_index_dim = Bi_fun.image (0,g_index) ndimens in *)
    (*   let tmain = Op.size_assign old_index_dim (Ne_csti 1) nmain in *)
    (*   let nmain = Op.upper_bnd Jjoin tmain nmain in *)
    (*   let nmain = Op.add_node g1_index_dim true 0 None nmain in *)
    (*   let cons1 = Nc_cons (Tcons1.SUPEQ,Ne_var g1_index_dim,Ne_csti 3) in *)
    (*   let cons2 = Nc_cons (Tcons1.SUPEQ,Ne_csti 23,Ne_var g1_index_dim) in *)
    (*   let nmain = Op.guard_s true cons1 nmain in *)
    (*   let nmain = Op.guard_s true cons2 nmain in *)
    (*   let x = *)
    (*     { x with *)
    (*       t_groups     = ngroups; *)
    (*       t_dimensions = ndimens} in *)
    (*   let userSet = IntSet.singleton 0 in *)
    (*   (\* let nvarRes = IntMap.singleton 11 userSet in *\) *)
    (*   let p_dim = Bi_fun.image (0,2) x.t_dimensions in *)
    (*   let nindexRes = IntMap.singleton p_dim userSet in *)
    (*   { x with *)
    (*     t_varRes   = IntMap.empty; *)
    (*     t_indexRes = nindexRes},nmain *)

    (* (\* specific for spo properties *\) *)
    (* let spo_property (x: t) (main: Op.t): t * Op.t = *)
    (*   let ng = get_new_group () in *)
    (*   let ngroups = IntSet.add ng x.t_groups in *)
    (*   let g1_index_dim = get_new_dim () in *)
    (*   let g1_size_dim = get_new_dim () in *)
    (*   let ndimens,nmain =  *)
    (*     List.fold_left *)
    (*       (fun ia ie -> *)
    (*         let idims,imain = ia in *)
    (*         let ndim = get_new_dim () in *)
    (*         let idims = Bi_fun.add (1,ie) ndim idims in *)
    (*         let imain = Op.add_node ndim false 1 (Some 16) imain in *)
    (*         idims, imain *)
    (*       )  (x.t_dimensions, main) [1;2;3;4] in *)
    (*   let ndimens = Bi_fun.add (1,g_index) g1_index_dim ndimens in *)
    (*   let ndimens = Bi_fun.add (1,g_size) g1_size_dim ndimens in *)
    (*   let nmain = Op.add_node g1_index_dim  true 0 (Some 16) nmain in *)
    (*   let nmain = Op.add_node g1_size_dim  false 1 (Some 1) nmain in *)
    (*   let g1_index_dim = Bi_fun.image (1,g_index) ndimens in    *)
    (*   let g0_index_dim = Bi_fun.image (0,g_index) ndimens in *)
    (*   (\* there is a bug when we make Ne_csti 0 as expression *\) *)
    (*   let tmain = Op.size_assign g0_index_dim (Ne_csti 6) nmain in *)
    (*   let nmain = Op.upper_bnd Jjoin tmain nmain in *)
    (*   let cons1 = Nc_cons (Tcons1.SUPEQ,Ne_var g1_index_dim,Ne_csti 3) in *)
    (*   let cons2 = Nc_cons (Tcons1.SUPEQ,Ne_csti 13,Ne_var g1_index_dim) in *)
    (*   let nmain = Op.guard_s true cons1 nmain in *)
    (*   let nmain = Op.guard_s true cons2 nmain in *)
    (*   let userSet = IntSet.singleton 0 in *)
    (*   let n_dim = Bi_fun.image (0,3) x.t_dimensions in *)
    (*   let nindexRes = IntMap.singleton n_dim userSet in *)
    (*   { x with *)
    (*     t_varRes = IntMap.empty; *)
    (*     t_indexRes = nindexRes ; *)
    (*     t_groups = ngroups ; *)
    (*     t_dimensions = ndimens},nmain *)

    let rem_dims (x: t) (m: Op.t): Op.t =
      Bi_fun.fold_dom (fun _ dim tm -> Op.rem_node dim tm) x.t_dimensions m

    let get_dimension (group: int) (fld: int) (x: t): int =
      Bi_fun.image (group,fld) x.t_dimensions
    let is_dimension_in (dim: int) (x: t): bool =
      Bi_fun.mem_inv dim x.t_dimensions

    let get_group_by_dim (dim: int) (x: t): int =
      let group, _ = Bi_fun.inverse_inj dim x.t_dimensions in
      group
    (* Assign functions inside sub numeric elements. It is used
     * when both "id" and "expr" are non-summary in id:= expr *)
    let assign (id: int) (expr: n_expr) (x: t): t =
      let nvarRes =  IntMap.remove id x.t_varRes in
      let nvarRes =
        match expr with
        | Ne_var var ->
            if IntMap.mem var nvarRes then
              IntMap.add id (IntMap.find var nvarRes) nvarRes
            else nvarRes
        | _ -> nvarRes in
      { x with t_varRes = nvarRes }

    let assign_for_predicate (group: int) (main: Op.t) (x: t) =
      match x.t_predicate with
      | OnePred pt ->
          let nmain,npt = Pred.assign_simple x.t_dimensions group main pt in
          { x with t_predicate = OnePred npt }, nmain
      | _ -> x,main

    (* Propagate the effect of an assigment from the main numeric element
     * to sub-elements, it is used when "id" is non-summary but "expr"
     * contains some summary dimension in id:= expr *)
    let propagate  (id: int) (expr: n_expr) (x: t): t =
      let nvarRes = IntMap.remove id x.t_varRes in
      let nvarRes =
        match expr with
        | Ne_var var ->
            if IntMap.mem var x.t_indexRes then
              IntMap.add id (IntMap.find var x.t_indexRes) nvarRes
            else nvarRes
        | _ -> nvarRes in
      { x with t_varRes = nvarRes }

    (* get a new array content node *)
    let fresh_array_node (id: int) (size: int) (fields: int list)
        (m: Op.t) (* main numeric element  *)
        : t * Op.t =
      let fld_num,fields =
        List.fold_left
          (fun (f_counter,amap) size_of_field ->
            let f_counter = f_counter + 1 in
            let nmap = IntMap.add f_counter size_of_field amap in
            f_counter,nmap
          ) (0, IntMap.empty) fields in
      let align = IntMap.fold (fun _ fld acc -> acc + fld) fields 0 in
      let group_id = get_new_group () in
      let group = IntSet.singleton group_id in
      (* add dimensions to array_node and main numeric element *)
      let dim_index = get_new_dim () in
      let dim_size = get_new_dim () in
      let dimensions =
        Bi_fun.add (group_id,g_index) dim_index Bi_fun.empty_inj in
      let nm = Op.add_node dim_index true size (Some size) m in
      let dimensions =
        Bi_fun.add (group_id,g_size) dim_size dimensions in
      let nm = Op.add_node dim_size false 1 (Some 1) nm in
      let dimensions,nm =
        IntMap.fold
          (fun key _ (td,tm) ->
            let ndim = get_new_dim () in
            (Bi_fun.add (group_id, key) ndim td),
            (Op.add_node ndim false size (Some size) tm)
          ) fields (dimensions,nm) in
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
          t_predicate = Uninitialized} in
      x, nm

    (** Bottom check  *)
    let is_bot (m: Op.t) (x: t): bool =
      IntSet.for_all
        (fun key  ->
          let dim_size = Bi_fun.image (key,g_size) x.t_dimensions in
          let dim_index = Bi_fun.image (key,g_index) x.t_dimensions in
          let equal0 = Nc_cons (Tcons1.EQ, Ne_var dim_size, Ne_csti 0) in
          not (Op.sat_s m equal0)
            && Op.is_bot (Op.assert_non_empty  dim_index m)
        ) x.t_groups
  end
