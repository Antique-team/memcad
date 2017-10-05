(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_ppred_utils.ml
 **       signatures of a simplified inductive domain based on lists
 **       (no parameters, no arbitrary inductives)
 ** Jiangchao Liu, 2016/03/01 *)
open Data_structures
open Lib

open Graph_sig
open Ind_sig
open Nd_sig
open Set_sig
open Sv_sig
open Svenv_sig
open Array_ppred_sig
open Array_ind_sig

open Array_ind_utils
open Ind_utils


(** Error report *)
module Log =
  Logger.Make(struct let section = "arr_put" and level = Log_level.DEBUG end)


(** Pretty printing *)
let prtype_2str: prule_type -> string = function
  | PURE_EMPTY -> "PURE EMPTY"
  | PURE_TRUE -> "PURE TURE"
  | PURE_SINGLE -> "PURE SINGLE"

let prule_2str (pr: prule): string =
  Printf.sprintf "rule type is %s \n maya cons is %s \n this cons is %s \n"
    (prtype_2str pr.pr_type) (gen_list_2str "" mform_2str " & " pr.pr_maya_cons)
    (gen_list_2str "" aform_2str " & " pr.pr_n_cons )

let pdef_2stri (i: string) (pdef: p_def): string =
  Printf.sprintf "%s p_def name is %s \n maya offset is %s \n rule is \n %s \n"
    i pdef.p_name
    (gen_list_2str "" Pervasives.string_of_int "; " pdef.p_maya_offs )
    (gen_list_2str "" prule_2str "\n" pdef.p_rules)

let pmem_2stri (i: string) (pm: pmem): string =
  let str_par =
    match pm.pm_mpar with
    | None -> "no this pointer"
    | Some i -> Printf.sprintf "this: %d" i in
  i^(pdef_2stri "" pm.pm_def)^str_par

(* Type of unfold result *)
type pm_unfold_result =
    { pu_pr_type:     prule_type;
      pu_pr_cons:     n_cons list;
      pu_pr_mcons:    mform list;
      pu_pr_maya_off: int list;
      pu_pr_pm:       pmem option; }

(* Transform aform to numeric constraints *)
let tr_aform (mpar: int option) (ipar: int list) (af: aform): n_cons =
  let tr_ae (ae: aexpr): n_expr =
    match ae with
    | Ae_cst i -> Ne_csti i
    | Ae_var av ->
        begin
          match av with
          | `Fa_this ->
              begin
                match mpar with
                | Some m -> Ne_var m
                | None -> Log.fatal_exn "conflict on main parameter"
              end
          | `Fa_par_int i -> Ne_var (List.nth ipar i)
          | _ -> Log.todo_exn "unsupported case in tr_afrom"
        end
    | Ae_plus (_, _) -> Log.fatal_exn "Ae_plus in aexpr" in
  match af with
  | Af_equal (ae1,ae2) -> Nc_cons (Apron.Tcons1.EQ,tr_ae ae1,tr_ae ae2)
  | Af_noteq (ae1,ae2) -> Nc_cons (Apron.Tcons1.DISEQ,tr_ae ae1,tr_ae ae2)
  | Af_sup (ae1,ae2)   -> Nc_cons (Apron.Tcons1.SUP,tr_ae ae1,tr_ae ae2)
  | Af_supeq (ae1,ae2) -> Nc_cons (Apron.Tcons1.SUPEQ,tr_ae ae1,tr_ae ae2)

(* Unfolding *)
let unfold (pm: pmem): pm_unfold_result list =
  List.map
    (fun pr ->
      let pur =
        { pu_pr_pm = None;
          pu_pr_type = PURE_EMPTY;
          pu_pr_cons = List.map (tr_aform pm.pm_mpar pm.pm_ipar) pr.pr_n_cons;
          pu_pr_mcons = pr.pr_maya_cons;
          pu_pr_maya_off = pm.pm_def.p_maya_offs} in
      match pr.pr_type with
      | PURE_TRUE ->
          { pur with
            pu_pr_pm = Some pm;
            pu_pr_type = PURE_TRUE }
      | PURE_EMPTY ->
          { pur with
            pu_pr_pm = None;
            pu_pr_type = PURE_EMPTY }
      | PURE_SINGLE ->
          { pur with
            pu_pr_pm = None;
            pu_pr_type = PURE_SINGLE }
    ) pm.pm_def.p_rules


(* Find pure predicates defs from users' specifications *)
let search_ppred ( ): unit =
  let module M = struct exception Stop of string end in (* local bail out *)
  (* Reinitiliazes the global map of list like inductive definitions *)
  ppred_defs := StringMap.empty;
  Log.info "search ppred\n";
  let aux_ind (iname: string) (ind: array_ind) : p_def =
    Format.printf "now dealing with ind def %s \n" iname;
    let trans_rule (irule: airule) =
      let mcons, acons, is_single =
        List.fold_left
          (fun (mc,ac,tc) node ->
            match node with
            | Ai_Pf_maya (Ai_Mf_cardinality (ma,v)) ->
                assert (v = 1);
                Ai_Mf_cardinality (ma, v) :: mc, ac, PURE_SINGLE
            | Ai_Pf_maya mf ->
                mf :: mc, ac, tc
            | Ai_Pf (Pf_arith af) ->
                mc, af :: ac ,tc
            | _ -> Log.fatal_exn "unexpected pform"
          ) ([],[],PURE_TRUE) irule.air_pure in
      let typ = if irule.air_kind = Aik_true then is_single else PURE_EMPTY in
      { pr_maya_cons = mcons;
        pr_n_cons = acons;
        pr_type = typ } in
    let prules = List.map trans_rule ind.ai_rules in
    let psub =
      match ind.ai_submem with
      | Some isubm -> isubm
      | _ -> Log.fatal_exn "unexpected cases" in
    (* Produce result *)
    { p_name    = ind.ai_name;
      p_submem = psub;
      p_maya_offs  = ind.ai_mpars;
      p_rules = prules;
      p_single_node = List.exists
        (fun node -> node.pr_type = PURE_SINGLE) prules;
      p_ipars = ind.ai_ppars } in
  Printf.printf "searching plain predicates defs\n\n";
  (* Find those inductives with "ture" predicates *)
  let ind_candidates =
    StringMap.filter
      (fun _ aind ->
        Log.info "aind is %s" (array_ind_2str aind);
        List.exists (fun arule -> arule.air_kind = Aik_true ) aind.ai_rules
      ) !Array_ind_utils.array_ind_defs in
  (* Iteration over the inductive definitions candidate to conversion *)
  StringMap.iter
    (fun name aind ->
      let lc = aux_ind name aind in
      Printf.printf "\nDefinition %s converted into plain predicates:\n%s\n\n"
        name (pdef_2stri "    " lc);
      ppred_defs := StringMap.add name lc !ppred_defs
    ) ind_candidates
