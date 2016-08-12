(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_pred_utils.ml
 **       some utils for array predicates
 ** Jiangchao Liu, 2015/11/29 *)
open Data_structures
open Lib
open Array_pred_sig
open Ast_sig
open C_sig

(** Error report *)

module Log =
  Logger.Make(struct let section = "ap_uts__" and level = Log_level.DEBUG end)


(** Array predicates from programs, it is from its string form in 
 * array_pred_sig by binding functions*)

(* hint_array stores predicates to be checked, we call it hint_array since
 * it helps us in re-group strategy *)
let hint_array_pred: apred option ref = ref None
(* assume_array stores predicates assumed  *)
let assume_array_pred: apred option ref = ref None
   
(* these two variables indicate whether array predicates have been
 * transferred from string form to apred form *)
let is_hint_resolved: bool ref = ref false
let is_assume_resolved: bool ref = ref false

(* Map from variable to id, from dom_env *)
let varm: (int * typ) VarMap.t ref = ref VarMap.empty

(* Map from id of varialbe address to id of its store, from dom_mem_low_flat *)
let deref: int IntMap.t ref = ref IntMap.empty


(** Pretty-printing *)
let arop_2str: a_arbop -> string = function
  | Abadd -> "+"
  | Absub -> "-"
  | Abmul -> "*"
  | Abmod -> "%"
let comop_2str: a_combop -> string = function
  | Abne -> "!="
  | Abeq -> "=="
  | Abge -> ">="
  | Abgt -> ">"
  | Able -> "<="
  | Ablt -> "<"
let logop_2str: a_logbop -> string = function
  | Abland -> "&&"
  | Ablor -> "||"
let ident_2str: ident -> string = function
  | Acur -> "$cur"
  | Asucc -> "$succ"
let avar_2str: avar -> string = function
  | Unrv_var av_str -> av_str
  | Rv_var av_id -> Printf.sprintf "%d" av_id
  | Harv_var hvar -> Ast_utils.var_2str hvar
let off_2str: aoff -> string = function
  | Unrv_off ao_str -> ao_str
  | Rv_off ao_id -> Printf.sprintf "%d" ao_id
let rec alval_2str: alval -> string = function
  | Avar av -> avar_2str av
  | Aarray (av,al) ->
      Printf.sprintf "%s[%s].1" (avar_2str av) (alval_2str al)
  | Aarray_strut (av,al,off) ->
      Printf.sprintf "%s[%s].%s" (avar_2str av) (alval_2str al) (off_2str off)
  | Aident ai -> ident_2str ai
let rec aexpr_2str (exp: aexpr): string = 
  match exp with
  | Aelval al -> alval_2str al
  | Aminus ae -> Printf.sprintf "-%s" (aexpr_2str ae)
  | Aebin (op,ae1,ae2) ->
      Printf.sprintf "%s%s%s" (aexpr_2str ae1) (arop_2str op) (aexpr_2str ae2)
  | Aeconst con -> Printf.sprintf "%d" con
let rec acond_2str (cnd: acond) = 
  match cnd with
  | Arith (op,ae1,ae2) ->
      Printf.sprintf "%s%s%s" (aexpr_2str ae1) (comop_2str op) (aexpr_2str ae2)
  | Logic (op, acnd1, acnd2) ->
      Printf.sprintf "%s%s%s" (acond_2str acnd1) (logop_2str op)
        (acond_2str acnd2)
let apred_2str (pred: apred): string = 
  match pred with
  | Nump num -> 
      Printf.sprintf
        "Numpred: var is %s\n assumption is %s \n solution is %s \n"
        (ident_2str num.var) (acond_2str num.assum) (acond_2str num.solution)
  | Comp com ->
      let atom_2str (at: atom_compred) = 
        Printf.sprintf "head is %s,\n succ is %s,\n exitcond is %s\n"
          (aexpr_2str at.head) (aexpr_2str at.succ) (acond_2str at.exitcond) in
      List.fold_left (fun str ato -> str^(atom_2str ato)) "Compred:" com


(** Map functions *)

let rec alval_map (f: avar -> aoff option -> avar * aoff) (lv: alval): alval = 
  match lv with
  | Avar av -> 
      let av, _ = f av None in
      Avar av
  | Aarray (av,al) ->
      let av, off = f av None in
      Aarray_strut (av, alval_map f al, off)
  | Aarray_strut (av,al,off) ->
      let av, off = f av (Some off) in
      Aarray_strut (av, alval_map f al, off)
  | _ -> lv
let rec aexpr_map (f: avar -> aoff option -> avar * aoff) (exp: aexpr): aexpr = 
  match exp with
  | Aelval al -> Aelval (alval_map f al)
  | Aminus ae -> Aminus (aexpr_map f ae)
  | Aebin (op,ae1,ae2) -> Aebin (op, aexpr_map f ae1, aexpr_map f  ae2)
  | _ -> exp
let rec acond_map (f: avar -> aoff option -> avar * aoff) (cnd: acond): acond = 
  match cnd with
  | Arith (op, ae1, ae2) -> Arith (op, aexpr_map f  ae1, aexpr_map f ae2)
  | Logic (op, acnd1, acnd2) -> Logic (op, acond_map f acnd1, acond_map f acnd2)
let apred_map (f: avar -> aoff option -> avar * aoff) (pred: apred): apred =
  match pred with
  | Nump num ->
      Nump { num with
             assum    = acond_map f num.assum;
             solution = acond_map f num.solution }
  | Comp com ->
      let com_map (ato: atom_compred) =
        { head     = aexpr_map f ato.head;
          succ     = aexpr_map f ato.succ;
          exitcond = acond_map f ato.exitcond } in
      Comp (List.map com_map com)

(* Bind a variable (string) with its id (int)  *)
let avar_bind_by_env (varmap: (int * typ) VarMap.t) (der: int IntMap.t)
    (arr: avar) (off: aoff option): avar * aoff = 
  let roff =
    match off with
    | None -> Rv_off 1
    | Some a -> a in
  let ravar = 
    match arr with
    | Harv_var a -> 
        let vid, _ = VarMap.find a varmap in
        Rv_var (IntMap.find vid der)
    | _ -> Log.fatal_exn "variable not parsed before being binded with env" in
  ravar, roff

(* Bind an offset (string) with its ordinal (int)  *)
let off_bind_by_cp (c_p: c_prog) (arr: avar) (off: aoff option): avar * aoff = 
  match arr with
  | Unrv_var ar_str ->
      begin
        let a_v = StringMap.find ar_str c_p.cp_vars in
        match a_v.cv_type with
        | Ctarray (c_t, _) -> 
            begin
              match c_t with
              | Ctint -> Harv_var (C_utils.tr_c_var a_v), Rv_off 1
              | Ctstruct c_agg_def ->
                  begin
                    let offs = 
                      match off with
                      | Some (Unrv_off a) -> a
                      | _ -> Log.fatal_exn "no filed specified" in 
                    match c_agg_def with
                    | Cad_def c_agg -> 
                        let n, f =
                          List.fold_left 
                            (fun (it, flag) field ->
                              if offs = field.caf_name || flag then
                                it, true
                              else
                                it + 1, false
                            ) (1, false) c_agg.cag_fields in
                        if not f then Log.fatal_exn "unrecognized field name";
                        Harv_var (C_utils.tr_c_var a_v), Rv_off n
                    | _ ->
                        Log.fatal_exn "the definition of structure undefined"      
                  end
              | _ -> Log.fatal_exn "array type unexpected"           
            end
        | _ -> Log.fatal_exn "unbounded array name"
      end
  | _ ->
      match off with
      | Some o -> arr,o
      | _ -> Log.fatal_exn "unexpected case"


(* Bind all offsets to their ordianls  *)
let apred_bind_by_cp (c_p: c_prog) (pred: apred ): apred = 
  apred_map (off_bind_by_cp c_p) pred

(* Bind all vars to their ids *)
let apred_bind_by_env (vm: (int * typ) VarMap.t) (def: int IntMap.t)
    (pred: apred): apred = 
  apred_map (avar_bind_by_env vm def) pred
