(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_bdd.ml
 **       Set domain implementation based on BDDs
 ** Huisong Li, Xavier Rival, 2014/8/22 *)
open Bdd
open Lib
open Data_structures
open Svenv_sig

open Set_sig
open Nd_sig


(* Error reporting *)
module Log =
  Logger.Make(struct let section = "s_bdd___" and level = Log_level.DEBUG end)

(** Basic set operations**)

(* making two bdd equal *)
let mk_equal (l: Bdd.t) (r: Bdd.t): Bdd.t =
  mk_and (mk_imp l r) (mk_imp r l)

(* - this function is used for project out a set variable;
 * - we do this by making the set variable as a exist variable;
 * - by seting it as zero or one *)
let mk_exists (i: int) (t: Bdd.t): Bdd.t =
  let v =  mk_var i in
  (* make set var exists *)
  let bdd0 = mk_and (mk_imp v zero) (mk_imp zero v) in
  let bdd1 = mk_and (mk_imp v one) (mk_imp one v) in
  mk_or (mk_and bdd0 t) (mk_and bdd1 t)

type formula_elt =
  | False 
  | True 
  | Sv of int
  | Setv of int  
  | And of formula_elt * formula_elt
  | Or  of formula_elt * formula_elt
type formula = 
  | Imp of formula_elt* formula_elt
  | Iff of formula_elt * formula_elt
  | Not of formula_elt

type bvar =
  | Bsetv of int
  | Bsv of int

(* for variables in Bdd *)
module BvarOrd =
  struct
    type t = bvar
    let compare (v0: bvar) (v1: bvar): int =
      match v0, v1 with
      | Bsetv s1, Bsetv s2 -> s1-s2
      | Bsv s1, Bsv s2 -> s1-s2
      | _ -> 1  
    let t_2str (v: bvar) = 
      match v with
      | Bsetv s -> "Setv"^(string_of_int s)
      | Bsv s -> "Sv"^(string_of_int s)
  end
(* build a t based on formula *)
module BvarMap = MapMake(BvarOrd)

(** Type of abstract values *)

type bdd =
  { b_bdd:    Bdd.t;
    b_key:    Keygen.t;
    b_map:    int BvarMap.t;
  }

type t =
    { t_u:            bdd option;
      (* we keep this set formula, and translate it to real bdd
       * when needed, like rename *)
      t_f:            formula list;
      (* root set variables *)
      t_roots:        IntSet.t; (* set of root set variables *) }

(* bdd_bot *)
let bdd_bot =
  { b_bdd = Bdd.zero;
    b_key = Keygen.empty;
    b_map = BvarMap.empty; }
(* bdd_top *)
let bdd_top =
  { b_bdd = Bdd.one;
    b_key = Keygen.use_key Keygen.empty 0;
    b_map = BvarMap.empty; }

let is_bdd_bot (b: bdd) =
  not (is_sat b.b_bdd)

let bdd_rem (bv: bvar) (t_u: bdd option): bdd option =
  match t_u with 
  | None -> None
  | Some bdd ->
    begin
      try
        let v = BvarMap.find bv bdd.b_map in
        let bdd = { b_bdd = mk_exists v bdd.b_bdd;
                    b_key = Keygen.release_key bdd.b_key v;
                    b_map = BvarMap.remove bv bdd.b_map; } in
        Some bdd
      with Not_found -> t_u
    end

let bdd_add (bv: bvar) (t_u: bdd option): bdd option =
  match t_u with 
  | None -> None
  | Some bdd ->
      if BvarMap.mem bv bdd.b_map then
        t_u
      else
        let _, i = Keygen.gen_key bdd.b_key in
        if i > get_max_var () then set_max_var i;
        let bdd = { bdd with
                    b_key = Keygen.use_key bdd.b_key i;
                    b_map = BvarMap.add bv i bdd.b_map; } in
        Some bdd

let bdd_add_formula (fm: formula) (bd: bdd option): bdd option =
  let rec formua_2bddformula (f:formula_elt) (bdd: bdd): Bdd.formula*bdd =
    match f with
    | False -> Ffalse, bdd
    | True -> Ftrue, bdd
    | Sv sv ->
        begin
          try
            let s = BvarMap.find (Bsv sv) bdd.b_map in
            Fvar s, bdd
          with
          | Not_found ->
              let _, i = Keygen.gen_key bdd.b_key in
              if i > get_max_var () then set_max_var i;
              let bdd = { bdd with
                          b_key = Keygen.use_key bdd.b_key i;
                          b_map = BvarMap.add (Bsv sv) i bdd.b_map; } in
              Fvar i, bdd
        end
    | Setv sv -> 
        begin
          try
            let s = BvarMap.find (Bsetv sv) bdd.b_map in
            Fvar s, bdd
        with
          | Not_found ->
              let _, i = Keygen.gen_key bdd.b_key in
              if i > get_max_var () then set_max_var i;
              let bdd = { bdd with
                          b_key = Keygen.use_key bdd.b_key i;
                          b_map = BvarMap.add (Bsetv sv) i bdd.b_map; } in
              Fvar i, bdd
        end
    | And (fl, fr) ->
        let fl, bdd = formua_2bddformula fl bdd in
        let fr, bdd = formua_2bddformula fr bdd in
        if fl = fr then fl, bdd
        else 
          let sim_f =
            match fl, fr with
            | Ftrue, _ -> fr
            | _, Ftrue -> fl
            | Ffalse, _ -> Ffalse
            | _, Ffalse -> Ffalse
            | _ -> Fand (fl, fr) in
          sim_f, bdd
    | Or (fl, fr) ->
        let fl, bdd = formua_2bddformula fl bdd in
        let fr, bdd = formua_2bddformula fr bdd in
        if fl = fr then fl, bdd
        else
          let sim_f =
            match fl, fr with
            | Ftrue, _ -> Ftrue
            | _, Ftrue -> Ftrue
            | Ffalse, _ -> fr
            | _, Ffalse -> fl
            | _ -> For (fl, fr) in
          sim_f, bdd in
  match bd with
  | None -> None
  | Some bdd_f ->
      begin
        match fm with
        | Imp (fl, fr) ->
            let fl, bdd_f = formua_2bddformula fl bdd_f in
            let fr, bdd_f = formua_2bddformula fr bdd_f in
            Some { bdd_f with
                   b_bdd =mk_and bdd_f.b_bdd (Bdd.build (Fimp (fl, fr))) }
        | Iff (fl, fr) ->
            let fl, bdd_f = formua_2bddformula fl bdd_f in
            let fr, bdd_f = formua_2bddformula fr bdd_f in
            Some { bdd_f with
                   b_bdd =mk_and bdd_f.b_bdd (Bdd.build (Fiff (fl, fr))); }
        | Not fl ->
            let fl, bdd_f = formua_2bddformula fl bdd_f in
            Some { bdd_f with
                   b_bdd =mk_and bdd_f.b_bdd (Bdd.build (Fnot fl)) }
      end

let bdd_imp (b1: bdd) (b2: bdd): bool =
  tautology (mk_imp b1.b_bdd b2.b_bdd)

(* Bottom element (empty context) *)
let bot: t =
  { t_u         = Some bdd_bot;
    t_f         = [ ];
    t_roots     = IntSet.empty; }

(* Top element (empty context) *)
let top: t =
  (* as the bdd require set variable's id start from 1, so we first use 0
   * as a first generated key *)
  { t_u         = Some bdd_top;
    t_f         = [ ];
    t_roots     = IntSet.empty; }

(* Pretty-printing, with indentation *)
let rec formula_elt_2str (s:formula_elt): string = 
  match s with
  | False -> "$F"
  | True  -> "$T"
  | Setv i -> Printf.sprintf "S[%d]" i
  | Sv i -> Printf.sprintf "N[%d]" i
  | And (l, r) ->
      Printf.sprintf "(%s $and %s)" (formula_elt_2str l) (formula_elt_2str r)
  | Or (l, r) ->
      Printf.sprintf "(%s $or %s)" (formula_elt_2str l) (formula_elt_2str r)
let formula_2str (s: formula): string =
  match s with
  | Imp (l, r) ->
      Printf.sprintf "(%s $imp %s)" (formula_elt_2str l) (formula_elt_2str r)
  | Iff (l, r) ->
      Printf.sprintf "(%s $iff %s)" (formula_elt_2str l) (formula_elt_2str r)
  | Not l ->
      Printf.sprintf "($not %s)" (formula_elt_2str l)
let t_2stri (_: string IntMap.t) (ind: string) (t: t): string =
  List.fold_left
    (fun acc f ->
      Printf.sprintf "%s%s%s\n" acc ind (formula_2str f)
    ) "" t.t_f

let formula_rename_bvar (bv: bvar) (felt: formula_elt) (f: formula): formula =
  let rec formula_elt_rename (bv: bvar) (felt: formula_elt) (f: formula_elt)
      :formula_elt =
    match f with
    | False
    | True -> f
    | Sv v -> if (Bsv v = bv) then felt else f
    | Setv setv -> if (Bsetv setv = bv) then felt else f
    | And (l, r) -> And (formula_elt_rename bv felt l,
                         formula_elt_rename bv felt r)
    | Or (l, r) ->  Or (formula_elt_rename bv felt l,
                        formula_elt_rename bv felt r) in
  match f with
  | Imp (l, r) ->
      Imp (formula_elt_rename bv felt l,
           formula_elt_rename bv felt r)
  | Iff (l, r) ->
      Iff (formula_elt_rename bv felt l,
           formula_elt_rename bv felt r)
  | Not l ->
      Not (formula_elt_rename bv felt l)

let replace_formula_bvar (bv: bvar): formula_elt =
  match bv with
  | Bsetv sv -> Setv sv
  | Bsv sv -> Sv sv

let remove_bv_formua (bv: bvar) (f: formula list): formula list =
  let rec check_elt (bv: bvar) (felt: formula_elt): bool =
    match felt with
    | False -> true
    | True -> true
    | Sv sv -> if (Bsv sv) = bv then false else true
    | Setv setv -> if (Bsetv setv) = bv then false else true
    | And (l, r) -> (check_elt bv l) && (check_elt bv r)
    | Or (l, r) -> (check_elt bv l) && (check_elt bv r) in
  let check_formula (bv: bvar) (fora: formula): bool =
    match fora with
    | Imp (l, r) ->
       (check_elt bv l)&&(check_elt bv r)
    | Iff (l, r) ->
       (check_elt bv l)&&(check_elt bv r)
    | Not l ->
      check_elt bv l in
  let formula_list_delete (bv: bvar) (f_l: formula list): formula list =
    List.fold_left
      (fun acc elt ->
        if check_formula bv elt then elt::acc
        else acc
      ) [ ] f_l in
  let formula_list_rename (bv: bvar) (felt: formula_elt) (f_l: formula list)
      : formula list =
    List.fold_left
      (fun acc elt -> (formula_rename_bvar bv felt elt) :: acc) [ ] f_l in
  let check_equal (bv: bvar) (form: formula): formula_elt option =
    let bf = replace_formula_bvar bv in
    match form with
    | Imp (l, r) ->
        begin
          match l, r with
          | _, False -> if l = bf then Some False else None
          | True, _-> if r = bf then Some True else None
          | _ -> None
        end
    | Iff (l, r) ->
        if l = bf then
          if (check_elt bv r) then
            Some r
          else None
        else if r = bf then
          if (check_elt bv l) then
            Some l
          else None
        else None
    | Not l ->
        if l = bf then
          Some False 
        else None in
  let equal_formula =
    List.fold_left
      (fun acc elt ->
        if acc != None then acc
        else
          check_equal bv elt
      ) None f in
  match equal_formula with
  | None -> formula_list_delete bv f
  | Some eq_f ->
      Log.info "equal: %s" (formula_elt_2str eq_f);
      formula_list_rename bv eq_f f

(* For sanity check *)
let check_nodes (s: IntSet.t) (t: t): bool =
  Log.todo_exn "check_nodes"

(** Set variables **)
(* -  adding set variables with a given id *)
let setv_add ?(root: bool = false) ?(kind: set_par_type option = None) 
    ?(name: string option = None) (i: int) (t: t): t =
  { t with
    t_u     = bdd_add (Bsetv i) t.t_u;
    t_roots = if root then IntSet.add i t.t_roots else t.t_roots; }

    
(* - Removing a set variable;
 * - we make the related set variable in bdd exists; *)
let setv_rem (i: int) (t: t): t =
  { t_u     = bdd_rem (Bsetv i) t.t_u;
    t_f     = remove_bv_formua (Bsetv i) t.t_f; 
    t_roots = IntSet.remove i t.t_roots }


(** Management of symbolic variables **)
(* - Adding a symbolic variable; *)
(* => we can drop the int result *)
let sv_add (i: int) (t: t): int * t =
  i,{ t with t_u = bdd_add (Bsv i) t.t_u; }  


let sv_rem (i: int) (t: t): t =
  { t with
    t_u    = bdd_rem (Bsv i) t.t_u;
    t_f    = remove_bv_formua (Bsv i) t.t_f; }
    
(* check if a set var root *)
let setv_is_root (i: int) (t: t): bool =
  IntSet.mem i t.t_roots

(* set variables in set domain *)
let setv_col_root (t: t): IntSet.t =
  t.t_roots


(* simplify formula *)
let simplify_formula (f: formula): formula option=
  let rec simplify_formula_elt (elt: formula_elt): formula_elt =
    match elt with
    | True -> True
    | False -> False
    | Sv i -> Sv i
    | Setv i -> Setv i
    | And (l, r) -> 
        let l, r = simplify_formula_elt l, simplify_formula_elt r in 
        if l = r then l
        else
          begin
            match l, r with
            | True, _ -> r
            | _, True -> l
            | False, _ -> False
            | _, False -> False
            | _ -> And (l, r)
          end
    | Or (l, r) ->
        let l, r = simplify_formula_elt l, simplify_formula_elt r in 
        if l = r then l
        else
          begin
            match l, r with
            | True, _ -> True
            | _, True -> True
            | False, _ -> r
            | _, False -> l
            | _ -> Or (l, r)
          end in
  match f with
  | Imp (l, r) -> 
      let l, r = simplify_formula_elt l, simplify_formula_elt r in 
      if l = r then None
      else
        begin
          match l, r with
          | _, True -> None
          | False, _ -> None
          | _, False -> Some (Not l)
          | _ -> Some (Imp (l, r))
        end
  | Iff (l, r) -> 
      let l, r = simplify_formula_elt l, simplify_formula_elt r in 
      if l = r then None
      else
        begin
          match l, r with
          | False, _ -> Some (Not r)
          | _, False -> Some (Not l)
          | _ -> Some (Iff (l, r))
        end
  | Not l ->
      let l = simplify_formula_elt l in 
      begin
        match l with
        | False -> None
        | _ -> Some (Not l)
      end


(** Set satisfiability *)

(* - Construction of a bdd for a set constraint *
 * - adding the bdd to the current set domain t *)
               
let tr_bdd (s: set_cons) (t: t): t =
  let rec tr_set_expr (e: set_expr) (f: formula list)
      : formula_elt * (formula list)=
    match e with
    | S_var l -> Setv l, f
    | S_node n -> Sv n, f
    | S_uplus (l, r) ->
        let fl, f = tr_set_expr l f in
        let fr, f = tr_set_expr r f in
        Or (fl, fr), (Not (And (fl, fr)))::f
    | S_union (l, r) ->
        let fl, f = tr_set_expr l f in
        let fr, f = tr_set_expr r f in
        Or (fl, fr), f
    | S_empty -> False, f in
  let f_list =
    match s with
    | S_mem (l, r) ->
        let fr, f_list = tr_set_expr r [] in  
        Imp (Sv l, fr)::f_list
    | S_eq (l, r) ->
        let fl, f_list = tr_set_expr l [] in
        let fr, f_list = tr_set_expr r f_list in  
        Iff (fl, fr)::f_list
    | S_subset (l, r) ->
        let fl, f_list = tr_set_expr l [] in
        let fr, f_list = tr_set_expr r f_list in  
        Imp (fl, fr)::f_list in
  let u =
    match t.t_u with
    | None -> None
    | Some t_u -> 
        List.fold_left (fun acc elt -> bdd_add_formula elt acc) t.t_u f_list in
  { t with
    t_f = List.rev_append f_list t.t_f;
    t_u = u }


(** Set condition test *)
let set_guard (s: set_cons) (t: t): t =
  Log.info "BDD:set_guard: %s" (Set_utils.set_cons_2str s);
  tr_bdd s t

let rebuild_t_u (fl: formula list) (bdd: bdd): bdd =
  let acc =
    List.fold_left (fun acc elt -> bdd_add_formula elt acc) (Some bdd) fl in
  match acc with
  | None -> Log.fatal_exn "rebuild_t_u return None"
  | Some bdd -> bdd
 
(** Set satisfiability *)
let set_sat (s: set_cons) (t: t): bool =
  Log.info "BDD:set_sat: %s" (Set_utils.set_cons_2str s);
  let t_u = 
    match t.t_u with
    | None -> rebuild_t_u t.t_f bdd_top
    | Some t_u -> t_u in
  let t1 = tr_bdd s { t with
                      t_u = Some { t_u with
                                   b_bdd = Bdd.one } } in
  match t1.t_u with
  | Some t1_u -> bdd_imp t_u t1_u
  | None -> Log.fatal_exn "set_sat t1_u is None"

let is_bot (t: t): bool =
  match t.t_u with
  | None ->
      let bdd = rebuild_t_u t.t_f bdd_top in
      is_bdd_bot bdd
  | Some t_u -> is_bdd_bot t_u

(* Comparison: check t1 imply t2 *)
let is_le (t1: t) (t2: t): bool =
  match t1.t_u, t2.t_u with
  | None, None ->
      let bdd_1 = rebuild_t_u t1.t_f bdd_top in
      let bdd_2 = rebuild_t_u t1.t_f { bdd_1 with b_bdd = Bdd.one } in
      bdd_imp bdd_1 bdd_2
  | Some t1_u, None ->
      bdd_imp t1_u  (rebuild_t_u t2.t_f {t1_u with b_bdd = Bdd.one})
  | None, Some t2_u ->
      bdd_imp (rebuild_t_u t1.t_f {t2_u with b_bdd = Bdd.one}) t2_u
  | Some t1_u, Some t2_u -> bdd_imp t1_u t2_u 

let simplify_formula_list (fl: formula list): formula list =
  List.fold_left
    (fun acc elt -> 
      match  simplify_formula elt with
      | None -> acc
      | Some foru -> foru::acc
    ) [ ] fl


(* collect sv *)
(* this need be improved later *)
let collect_sv (fm: formula list): IntSet.t =
  let rec formula_elt (fe: formula_elt) (set_sv: IntSet.t): IntSet.t =
    match fe with
    | False 
    | True -> set_sv
    | Sv sv -> IntSet.add sv set_sv
    | Setv _ -> set_sv 
    | And (fl, fr) -> formula_elt fr (formula_elt fl set_sv)
    | Or (fl, fr) -> formula_elt fr (formula_elt fl set_sv) in
  let formula (f: formula): IntSet.t =
    match f with
    | Imp (fl, fr) ->
        formula_elt fr (formula_elt fl IntSet.empty)
    | Iff (fl, fr) ->
        formula_elt fr (formula_elt fl IntSet.empty)
    | Not fl -> formula_elt fl IntSet.empty in
  List.fold_left (fun acc elt -> IntSet.union acc (formula elt)) IntSet.empty fm

(* - Upper bound: serves as join  *
 * - t.t_u    = t1.t_u or t2.t_u; *
 * - t.t_f    = t1.t_f or t2.t_f; *)
let upper_bnd (t1: t) (t2: t): t =
  let t1_f = simplify_formula_list t1.t_f in
  let t2_f = simplify_formula_list t2.t_f in
  Log.info "uper_before_t1: %s" 
    (List.fold_left (fun acc elt -> (formula_2str elt)^"^"^acc) "" t1_f);
  Log.info "uper_before_t2: %s" 
    (List.fold_left (fun acc elt -> (formula_2str elt)^"^"^acc) "" t2_f);
  let t1_sv, t2_sv = collect_sv t1_f, collect_sv t2_f in 
  let t1_vs_diff = IntSet.diff t1_sv t2_sv in
  let t2_vs_diff = IntSet.diff t2_sv t1_sv in
  let t1_f =
    IntSet.fold
      (fun elt acc -> remove_bv_formua (Bsv elt) acc) t1_vs_diff t1_f in
  let t2_f =
    IntSet.fold
      (fun elt acc -> remove_bv_formua (Bsv elt) acc) t2_vs_diff t2_f in
  Log.info "uper_t1: %s" 
    (List.fold_left (fun acc elt -> (formula_2str elt)^"^"^acc)
       "" t1_f);
  Log.info "uper_t2: %s" 
    (List.fold_left (fun acc elt -> (formula_2str elt)^"^"^acc)
       "" t2_f);
  let t1_bdd = rebuild_t_u t1_f bdd_top in
  let t2_bdd = rebuild_t_u t2_f {t1_bdd with b_bdd = Bdd.one} in
  if bdd_imp t1_bdd t2_bdd then 
    { t2 with
      t_f = t2_f;
      t_u = Some t2_bdd; }
  else if bdd_imp t2_bdd t1_bdd then
    { t1 with
      t_f = t1_f;
      t_u = Some t1_bdd; }
  else
    { t_f = [ ];
      t_u = Some { t2_bdd with b_bdd = mk_or t1_bdd.b_bdd t2_bdd.b_bdd; };
      t_roots = IntSet.inter t1.t_roots t2.t_roots }

(* Weak bound: serves as widening *)
let weak_bnd (t1: t) (t2: t): t =
  upper_bnd t1 t2
 
(* - Forget (if the meaning of the sv changes)
 * - HS: I think here it is same to sv_rem *)
let forget (i: int) (t: t): t =
  Log.todo_exn "forget"

(* this need be improved later *)
let collect_unmapped_setv (fm: formula list) (sm: setv_mapping): IntSet.t =
  let renamed_setv =
    IntMap.fold (fun key _ acc -> IntSet.add key acc) sm.sm_map IntSet.empty in
  let rec formula_elt (fe: formula_elt) (umap_setv: IntSet.t): IntSet.t =
    match fe with
    | False 
    | True 
    | Sv _ -> umap_setv
    | Setv sv -> 
        if IntSet.mem sv renamed_setv then umap_setv
        else IntSet.add sv umap_setv
    | And (fl, fr) ->
        formula_elt fr (formula_elt fl umap_setv)
    | Or (fl, fr) ->
        formula_elt fr (formula_elt fl umap_setv) in
  let formula (f: formula): IntSet.t =
    match f with
    | Imp (fl, fr) ->
        formula_elt fr (formula_elt fl IntSet.empty)
    | Iff (fl, fr) ->
        formula_elt fr (formula_elt fl IntSet.empty)
    | Not fl -> formula_elt fl IntSet.empty in
  List.fold_left
    (fun acc elt -> IntSet.union acc (formula elt)) IntSet.empty fm
  
let delete_unmapped_setv (t: t) (sm: setv_mapping): t =
  let un_mapped_setv = collect_unmapped_setv t.t_f sm in
  IntSet.fold
    (fun elt acc -> setv_rem elt acc) un_mapped_setv { t with t_u = None }
  
let delete_unmapped_sv (t: t) (nm: (int * Offs.t) node_mapping): t =
  IntSet.fold (fun elt acc -> sv_rem elt acc) nm.nm_rem {t with t_u = None}
  
 
(** Renaming (e.g., post join) *)

(* rename symbolic variables and set variables together *)
let symvars_srename
    (om: (Offs.t * int) Offs.OffMap.t)
    (nm: (int * Offs.t) node_mapping)
    (sm: setv_mapping option) 
    (t1: t): t =
  let sm =
    match sm with
    | None -> Log.fatal_exn "no-setvmapping"
    | Some x -> x in
  (*clean t1*)
  let t1_f = simplify_formula_list t1.t_f in
  let t1_clean = delete_unmapped_sv { t1 with t_u = None; t_f = t1_f } nm in
  let t1_clean = delete_unmapped_setv t1_clean sm in
  (* create the initial renamed t *)
  let t2 =
    IntMap.fold
      (fun key (elt, selt) acc ->
        let is_root = IntSet.mem key t1.t_roots in
        let acc = setv_add ~root:is_root elt acc in
        IntSet.fold
          (fun se acc ->
            let acc = setv_add ~root:is_root se acc in
            { acc with t_f = Iff (Setv se, Setv elt)::acc.t_f; }
          ) selt acc
      ) sm.sm_map { t_u = None; t_f = [ ]; t_roots = IntSet.empty }  in
  (* - rename function, m is the Map used in rename *
   * - collect set variables cannot be renamed at the same time*)
  let formula_rename (f: formula): formula =
    let rec formula_elt_rename  (felt: formula_elt): formula_elt =
      match felt with
      | False -> False
      | True -> True
      | Setv s ->
          begin
            try
              let elt, _ = IntMap.find s sm.sm_map in
              Setv elt
            with Not_found ->
              Log.fatal_exn "srename setv not found"
          end
      | Sv i ->
          begin
            try
              let elt, _ = IntMap.find i  nm.nm_map in
              Sv elt
            with Not_found ->
              Log.fatal_exn "srename sv not found"
          end
      | And (l, r) ->
          let  fl = formula_elt_rename l in
          let  fr = formula_elt_rename r in
          And (fl, fr)
      | Or (l, r) ->
          let fl = formula_elt_rename l in
          let fr= formula_elt_rename r in
          Or (fl, fr) in
    match f with
    | Imp (l, r) ->
        let fl = formula_elt_rename l in
        let fr = formula_elt_rename r in
        Imp (fl, fr)
    | Iff (l, r) ->
        let fl = formula_elt_rename l in
        let fr = formula_elt_rename r in
        Iff (fl, fr)
    | Not l ->
        let fl = formula_elt_rename l in 
        Not fl in
  (* do the rename *)
  let rename_f =
    List.fold_left
      (fun acc elt -> (formula_rename elt)::acc) [ ] t1_clean.t_f in
   { t2 with
     t_f = List.rev_append t2.t_f rename_f;
     t_u = None; }
  
let sve_sync_top_down (svm: svenv_mod) (x: t): t =
  let x = PSet.fold sv_rem svm.svm_rem x in
  PSet.fold sv_rem svm.svm_mod x

(* Removes all symbolic vars and set vars that are not 
 * in a given set *)
let symvars_filter (s: IntSet.t) (setv: IntSet.t) (t: t): t = 
  t
