(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_utils.ml
 **       utilities for the abstract domain
 ** Xavier Rival, 2011/10/17 *)
open Data_structures
open Lib

open Ast_sig
open Dom_sig
open Ind_sig
open Sv_sig
open Svenv_sig
open Graph_sig


(** Error report *)
module Log =
  Logger.Make(struct let section = "d_uts___" and level = Log_level.DEBUG end)


(** Basic pretty-printing *)
let join_kind_2str: join_kind -> string = function
  | Jjoin -> "join"
  | Jwiden -> "widen"
  | Jdweak -> "dweak"


(** Map functions over gen_ind_call *)
let map_gen_ind_indp (f: 'a -> 'b) (ic: 'a gen_ind_intp): 'b gen_ind_intp =
  match ic with
  | Ii_const i -> Ii_const i
  | Ii_lval l -> Ii_lval (f l)
let map_gen_ind_pars (f: 'a -> 'b) (g: setvar -> int)
    (ic: 'a gen_ind_pars): 'b gen_ind_pars =
  { ic_ptr  = List.map f ic.ic_ptr ; 
    ic_int  = List.map (map_gen_ind_indp f) ic.ic_int;
    ic_set  = List.map (fun x -> { x with s_uid = g x }) ic.ic_set }
let map_gen_ind_call (f: 'a -> 'b)  ?(g: setvar -> int = fun x -> -1)
    (ic: 'a gen_ind_call): 'b gen_ind_call =
  { ic_name = ic.ic_name ;
    ic_pars = Option.map (map_gen_ind_pars f g) ic.ic_pars }


(** Emptiness test on gen_ind_call *)
let gen_ind_call_is_empty (ic: 'a gen_ind_call): bool =
  match ic.ic_pars with
  | None -> true
  | Some p -> p.ic_ptr = [ ] && p.ic_int = [ ]


(** Hints for domain operators *)
let extract_hint (ho: hint_be option): hint_ue option =
  Option.map (fun h -> { hue_live = h.hbe_live }) ho


(** Renaming operations *)
(* Pretty printing *)
let renaming_2stri (ind: string): int IntMap.t -> string =
  let sep = "\n"^ind in
  IntMap.t_2str sep string_of_int 
(* Composition of renamings:
 *   - a renaming r is represented by a map M_r such that
 *     r(i) = M_r(i) if i \in M_r
 *     r(i) = i      otherwise
 *   - composition is defined as usual: (r0 o r1)(i) = r0(r1(i))
 *)
let renaming_compose (r0: int IntMap.t) (r1: int IntMap.t): int IntMap.t =
  let add i k r2 =
    if IntMap.mem i r2 then
      begin
        Log.info "combine_renaming: bad renaming:\n r0:\n%s r1:\n%s"
          (renaming_2stri "  " r0) (renaming_2stri "  " r1);
        Log.fatal_exn "combine_renaming: bad renaming"
      end
    else IntMap.add i k r2 in
  let r2 =
    IntMap.fold
      (fun i j r2 ->
        let k = try IntMap.find j r0 with Not_found -> j in
        IntMap.add i k r2
      ) r1 IntMap.empty in
  IntMap.fold add r0 r2


(** Envmod structure *)
let svenv_empty: svenv_mod =
  { svm_add = PMap.empty;
    svm_rem = PSet.empty;
    svm_mod = PSet.empty }
let svenv_is_empty (svm: svenv_mod): bool =
  svm.svm_add = PMap.empty
    && svm.svm_rem = PSet.empty
    && svm.svm_mod = PSet.empty
let svenv_2stri (ind: string) (sv: svenv_mod): string =
  let fmap = PMap.t_2str "" ", " (fun s _ -> string_of_int s) in
  let fset = PSet.t_2str ", " string_of_int in
  Printf.sprintf "%s{ Add: %s\n%s  Rem: %s\n%s  Mod: %s }\n"
    ind (fmap sv.svm_add) ind (fset sv.svm_rem) ind (fset sv.svm_mod)
(* removal of an SV *)
let svenv_rem (i: int) (sv: svenv_mod): svenv_mod =
  assert (not (PMap.mem i sv.svm_add));
  assert (not (PSet.mem i sv.svm_mod));
  { sv with svm_rem = PSet.add i sv.svm_rem }
let svenv_join (sv0: svenv_mod) (sv1: svenv_mod): svenv_mod =
  let sanity_checks = false in (* turn on for debugging *)
  let f_check svc svo =
    PMap.iter
      (fun i _ ->
        if PSet.mem i svo.svm_rem || PSet.mem i svo.svm_mod then
          begin
            Log.info "Incompatible svenvs:\n1:\n%s\n2:\n%s\n"
              (svenv_2stri "  " sv0) (svenv_2stri "  " sv1);
            Log.fatal_exn "svenv_join"
          end;
      ) svc.svm_add in
  (* removed / modified in sv1 should not have been added in sv0 *)
  if sanity_checks then f_check sv1 sv0;
  (* added in sv1 should not have been removed / modified in sv1 *)
  if sanity_checks then f_check sv0 sv1;
  { svm_add = PMap.fold PMap.add sv0.svm_add sv1.svm_add;
    svm_rem = PSet.fold PSet.add sv0.svm_rem sv1.svm_rem;
    svm_mod = PSet.fold PSet.add sv0.svm_mod sv1.svm_mod; }
let svenv_map (f: int -> int) (sv: svenv_mod): svenv_mod = 
  { svm_add = PMap.fold (fun i -> PMap.add (f i)) sv.svm_add PMap.empty;
    svm_rem = PSet.fold (fun i -> PSet.add (f i)) sv.svm_rem PSet.empty;
    svm_mod = PSet.fold (fun i -> PSet.add (f i)) sv.svm_mod PSet.empty; }
(* generic application of modifications in an svenv_mod *)
let svenv_mod_doit
    (fadd: int -> ntyp -> 'a -> 'a)
    (frem: int -> 'a -> 'a)
    (fmod: int -> 'a -> 'a) (svm: svenv_mod) (x: 'a): 'a =
  let x = PMap.fold fadd svm.svm_add x in
  let x = PSet.fold frem svm.svm_rem x in
  PSet.fold fmod svm.svm_mod x

(* Symbolic variable environment updater *)
let sv_upd_2set: sv_upd -> IntSet.t = function
  | Svu_mod (i, s) -> IntSet.add i s
  | Svu_rem         -> IntSet.empty
let sv_upd_2str = function
  | Svu_mod (i, s) -> Printf.sprintf "M: [ %i, { %s } ]" i (IntSet.t_2str "," s)
  | Svu_rem        -> "R"
let svenv_upd_empty: svenv_upd = fun _ -> raise Not_found
let svenv_upd_identity: svenv_upd = fun i -> Svu_mod (i, IntSet.empty)
let svenv_upd_embedding (nm: unit Nd_sig.node_mapping): svenv_upd =
  fun i ->
    try
      let j, s = IntMap.find i nm.Nd_sig.nm_map in
      Svu_mod (j, s)
    with Not_found ->
      if IntSet.mem i nm.Nd_sig.nm_rem then Svu_rem
      else raise Not_found

(*extending the joining graph with its encoding *)
let ext_graph (ei: abs_graph option) (eo: abs_graph option): join_ele =
  { abs_gi = ei;
    abs_go = eo; }

