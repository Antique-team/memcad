(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_ind_utils.ml
 **       data-types for the inductive definitions.
 ** Jiangchao Liu, 2016/03/01 *)

open Data_structures
open Lib
open Graph

open Graph_sig
open Ind_sig
open Set_sig
open Sv_sig
open Array_ind_sig
open List_sig

open Ind_utils
open C_utils
open List_utils

(** Set of inductive definitions *)
let array_ind_defs: array_ind StringMap.t ref = ref StringMap.empty
let array_list_ind_defs: l_def StringMap.t ref = ref StringMap.empty

(** Error report *)
module Log =
  Logger.Make(struct let section = "arr_iu___" and level = Log_level.DEBUG end)


(** Pretty print  *)
let formal_maya_arg_2str: formal_maya_arg -> string = function
  | Fa_par_maya i -> Printf.sprintf "@m%d" i
  | Fa_par_nmaya i -> Printf.sprintf "@n%d" i

let mform_2str: mform -> string = function
  | Ai_Mf_mem (a, m) ->
      Printf.sprintf "%s # %s" (formal_arith_arg_2str a)
        (formal_maya_arg_2str m)
  | Ai_Mf_equal_s (ma0,ma1) ->
      Printf.sprintf "%s = %s" (formal_maya_arg_2str ma0)
        (formal_maya_arg_2str ma1)
  | Ai_Mf_included (ma0,ma1) ->
      Printf.sprintf "%s in %s" (formal_maya_arg_2str ma0)
        (formal_maya_arg_2str ma1)
  | Ai_Mf_cons (op,ma,ae) ->
       Printf.sprintf "%s %s %s" (formal_maya_arg_2str ma)
        (c_binop_2str op) (aexpr_2str ae)
  | Ai_Mf_empty m -> Printf.sprintf "%s == { }" (formal_maya_arg_2str m)
  | Ai_Mf_cardinality (m,v) ->
      Printf.sprintf " |%s|== %d" (formal_maya_arg_2str m) v

let ai_pform_atom_2str: ai_pformatom -> string = function
  | Ai_Pf pf -> pform_atom_2str pf
  | Ai_Pf_maya f -> mform_2str f

let ai_pform_2str: ai_pform -> string =
  gen_list_2str "" ai_pform_atom_2str " & "

let air_kind_2str: air_kind -> string = function
  | Aik_unk -> "unknown"
  | Aik_empi -> "{emp,int}"
  | Aik_true -> " true"

let airule_2str (ar: airule): string =
  let typs =
    IntMap.fold
      (fun i typ acc ->
        Printf.sprintf "%s %s" acc (ntyp_2str typ)
      ) ar.air_typ "" in
  Printf.sprintf "| [%d%s]\n\t- %s\n\t- %s\n"
    ar.air_num typs (hform_2str ar.air_heap) (ai_pform_2str ar.air_pure)

let array_ind_2str (ai: array_ind): string =
  let srules = gen_list_2str "" airule_2str "" ai.ai_rules in
  let buf = Buffer.create 80 in
  Printf.bprintf buf "%s<%d,%d> :=\n%s\n"
    ai.ai_name ai.ai_ppars ai.ai_ipars srules;
  (* Printing the analysis results *)
  List.iteri
    (fun i air ->
      Printf.bprintf buf "  rule %d => %b\n" i air.air_unone
    ) ai.ai_rules;
  Buffer.contents buf


(** Analysis on inductive predicates in arays *)
exception Success
exception Failure


(** Computation of ir_kind fields
 *  i.e., when a rule is either necessary null (emp) or non null (non emp) *)

let check_empty_rule (r: airule): bool =
  try
    List.iter
      (function
        | Ai_Pf (Pf_arith (Af_equal (Ae_var `Fa_this, Ae_cst _)))
        | Ai_Pf (Pf_arith (Af_equal (Ae_cst _, Ae_var `Fa_this))) ->
            raise Success (* it is null *)
        | _ ->
            Log.info "AI: rule is %s " (airule_2str r);
            raise Failure
      ) r.air_pure;
    false
  with
  | Success -> true
  | Failure -> false

let empty_heap_rule_analysis (i: array_ind): array_ind =
  try
    let b =
      List.fold_left
        (fun acc r ->
          if check_empty_rule r then
            if acc then raise Failure (* found a second empty rule *)
            else true (* found one empty rule *)
          else acc
        ) false i.ai_rules in
    { i with ai_mt_rule = b }
  with
  | Failure -> { i with ai_mt_rule = false } (* multiple empty rules found *)

let ind_rules_kind (ind: array_ind): array_ind =
  let f_rule (r: airule): airule =
    let kind =
      try
        (* check whether the pointer is null *)
        let this_is_null = check_empty_rule r in
        (* check whether the heap region is empty *)
        let region_is_emp = r.air_heap = [ ] in
        match this_is_null, region_is_emp, r.air_kind with
        | _, _, Aik_true -> Aik_true
        | true, true, _ -> Aik_empi
        | false, true, _ -> Log.warn "AI: empty region, non null"; Aik_empi
        | _, _, _ -> Aik_unk
      with Failure -> Aik_unk in
    if !Flags.flag_debug_ind_analysis then
      Log.force "Rule kind: %s" (air_kind_2str kind);
    { r with air_kind = kind } in
  { ind with ai_rules = List.map f_rule ind.ai_rules }


(* Initialization from parsing *)
let array_ind_init (al: array_ind list): unit =
  List.iter
    (fun aind ->
      let name = aind.ai_name in
      Log.info "\n AI: ind is \n %s\n" (array_ind_2str aind);
      assert (not (StringMap.mem name !array_ind_defs));
      List.iter
        (fun r ->
          if IntMap.cardinal r.air_typ != r.air_num then
            Log.warn "incorrect rule in %s" aind.ai_name;
        ) aind.ai_rules;
      let aind = empty_heap_rule_analysis aind in
      let aind = ind_rules_kind aind in
      array_ind_defs := StringMap.add name aind !array_ind_defs;
      Log.info "Inductive %s; mt result: %b\n%s"
        aind.ai_name aind.ai_mt_rule (array_ind_2str aind);
    ) al

(** Find array list definitions from inductive definitions *)
let exp_search_array_lists ( ): unit =
  let module M = struct exception Stop of string end in (* local bail out *)
  array_list_ind_defs := StringMap.empty;
  let name_2ldef name =
    try StringMap.find name !array_list_ind_defs
    with Not_found -> raise (M.Stop (Printf.sprintf "%s not found" name)) in
  let aux_rule (iname: string) (aind: array_ind)
      (r: airule) (r_emp: airule): l_def =
    let m_subinds, m_fieldsoff, m_idxoff, m_fieldsrev =
      List.fold_left
        (fun (accsubs, accfo, accio, accfr) -> function
          | Hacell cell ->
              begin
                match cell.ic_dest, Offs.to_int_opt cell.ic_off with
                | `Fa_var_new i, Some o ->
                    ( accsubs, IntMap.add o cell accfo,
                      IntMap.add i o accio, IntMap.add i cell accfr )
                | _, _ -> raise (M.Stop "field")
              end
          | Haind icall ->
              begin
                match icall.ii_maina with
                | `Fa_this -> raise (M.Stop "main field")
                | `Fa_var_new i ->
                    IntMap.add i icall accsubs, accfo, accio, accfr
              end
        ) (IntMap.empty, IntMap.empty, IntMap.empty, IntMap.empty) r.air_heap in
    let idx_2off idx =
      try IntMap.find idx m_idxoff
      with Not_found -> Log.fatal_exn "symvar %d at no offset" idx in
    (* Extracting a single next field, and tail inductive predicate *)
    let onext, callnext, others =
      let self, others =
        IntMap.fold
          (fun i call (self, others) ->
            if String.compare call.ii_ind iname = 0 then
              (idx_2off i, call) :: self, IntMap.remove i others
            else self, others
          ) m_subinds ([ ], m_subinds) in
      match self with
      | [ ] -> raise (M.Stop "no next field")
      | _ :: _ :: _ -> raise (M.Stop "several next fields")
      | [ inext, callnext ] -> inext, callnext, others in
    let nest_calls, nest_call_setpars =
      IntMap.fold
        (fun i ic (c, sp) ->
          (idx_2off i, name_2ldef ic.ii_ind) :: c, ic.ii_args :: sp)
        others ([ ], [ ]) in
    let _subcall_pars =
      List.fold_lefti
        (fun i r -> function
          | `Fa_var_new j ->
              if IntMap.mem j r then
                raise (M.Stop "one new var => several sub-pars")
              else IntMap.add j (Sv_nextpar i) r
          | _ -> r
        ) IntMap.empty callnext.ii_args in
    (* Searching for the size *)
    let size =
      let acc =
        List.fold_left
          (fun acc -> function
            | Ai_Pf (Pf_alloc s) ->
                if acc != None then raise (M.Stop "two sizes"); Some s
            | _ -> acc
          ) None r.air_pure in
      match acc with
      | None -> raise (M.Stop "no size")
      | Some s -> s in
    let emp_csti,emp_mcons =
      List.fold_left
        ( fun (acc_cst,acc_m) node ->
          match node with
          | Ai_Pf (Pf_arith (Af_equal ((Ae_cst aint), (Ae_var `Fa_this))))
          | Ai_Pf (Pf_arith (Af_equal (Ae_var `Fa_this, Ae_cst aint))) ->
              aint, acc_m
          | Ai_Pf_maya a_m -> acc_cst, a_m :: acc_m
          | _ ->  acc_cst, acc_m
          ) (-1,[]) r_emp.air_pure in
    let next_mcons =
      List.fold_left
        ( fun acc node ->
          match node with
          | Ai_Pf_maya am -> am:: acc
          | _ -> acc
         ) [] r.air_pure in
    (* Produce result *)
    { ld_name       = Some aind.ai_name;
      ld_m_offs     = aind.ai_mpars;
      ld_submem     = aind.ai_submem;
      ld_emp_csti   = emp_csti;
      ld_emp_mcons  = emp_mcons;
      ld_next_mcons = next_mcons ;
      ld_nextoff    = onext;
      ld_size       = size;
      ld_onexts     = nest_calls;
      ld_set        = None } in
  let depgraph =
    StringMap.fold
      (fun name aind acc ->
        List.fold_left
          (fun acc rule ->
            List.fold_left
              (fun acc -> function
                | Hacell _ -> acc
                | Haind ic -> StringGraph.edge_add name ic.ii_ind acc
              ) acc rule.air_heap
          ) acc aind.ai_rules
      ) !array_ind_defs StringGraph.empty in
  let components =
    List.filter (fun s -> StringSet.cardinal s <= 1)
      (StringGraph.tarjan depgraph) in
  let ind_candidates =
    List.fold_left (fun acc s -> StringSet.min_elt s :: acc) [ ] components in
  (* Iteration over the inductive definitions candidate to conversion *)
  List.iter
    (fun name ->
      Log.info "looking at inductive definition %s" name;
      let aind =
        try StringMap.find name !array_ind_defs
        with Not_found -> Log.fatal_exn "ind def %s not found" name in
      Log.info "mt_rule %b\n" aind.ai_mt_rule;
      Log.info "length is %d \n" (List.length aind.ai_rules);
      if aind.ai_mt_rule && List.length aind.ai_rules = 2 then
        let rule, emp_rule =
          match aind.ai_rules with
          | [ r0 ; r1 ] ->
              if r0.air_kind = Aik_empi then r1, r0
              else if r1.air_kind = Aik_empi then r0, r1
              else Log.fatal_exn "contradicting rules structure"
          | _ -> Log.fatal_exn "contradicting number of rules" in
        try
          let lc = aux_rule name aind rule emp_rule in
          Log.info "\nDefinition %s converted into:\n%s\n" name
            (l_def_2stri "    " lc);
          array_list_ind_defs := StringMap.add name lc !array_list_ind_defs
        with
        | M.Stop s -> Log.info "%s not an array list like ind def (%s)\n" name s
      else Log.info "%s not array list like ind def (rule #)" name
    ) ind_candidates
