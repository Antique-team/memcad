(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_utils.ml
 **       utilities for set domain
 ** Huisong Li, 2014/09/25 *)
open Data_structures
open Lib
open Set_sig
open List_sig

module Log =
  Logger.Make(struct let section = "s_uts___" and level = Log_level.DEBUG end)

(** Print function *)

(* Pretty-printing *)
let rec set_expr_2str (e: set_expr): string =
  match e with
  | S_var i -> Printf.sprintf "S[%d]" i
  | S_node i -> Printf.sprintf "N[%d]" i
  | S_uplus (i, j) ->
      Printf.sprintf "%s [U+] %s" (set_expr_2str i) (set_expr_2str j)
  | S_union (i, j) ->
      Printf.sprintf "%s [U] %s" (set_expr_2str i) (set_expr_2str j)
  | S_empty -> Printf.sprintf "$emp"   
let rec set_cons_2str (s: set_cons): string =
  match s with
  | S_mem (i, j) ->
      Printf.sprintf "N[%d] $in %s" i (set_expr_2str j)
  | S_eq (i, j) ->
      Printf.sprintf "%s = %s" (set_expr_2str i) (set_expr_2str j)
  | S_subset (i, j) ->
      Printf.sprintf "%s <= %s" (set_expr_2str i) (set_expr_2str j)
let set_par_type_2str (t: set_par_type): string =
  let f b x s = if b then StringSet.add x s else s in
  let s = f t.st_mono "Mono" (f t.st_const "Const" StringSet.empty) in
  let s = f t.st_add "Add" (f t.st_head "Head" s) in
  Printf.sprintf "[%s]" (StringSet.t_2str ";" s)


(** Mapping functions *)

(* Empty mapping *)
let setv_mapping_empty: setv_mapping =
  { sm_map    = IntMap.empty;
    sm_rem    = IntSet.empty; }

(* Addition of a new node *)
let add_to_mapping (i: int) (j: int) (m: setv_mapping): setv_mapping =
  let map =
    try
      let k, s = IntMap.find i m.sm_map in
      IntMap.add i (k, IntSet.add j s) m.sm_map ;
    with
    | Not_found -> IntMap.add i (j, IntSet.empty) m.sm_map in
  { sm_map = map ;
    sm_rem = IntSet.remove i m.sm_rem }

(* Pretty-printing *)
let setv_mapping_2str (m: setv_mapping): string =
  let smap =
    IntMap.fold
      (fun i (j, s) acc ->
        let ts = IntSet.fold (Printf.sprintf "%d;%s") s "" in
        Printf.sprintf "        %d -> %d;%s\n%s" i j ts acc 
      ) m.sm_map "" in
  let srem = intset_2str m.sm_rem in
  Printf.sprintf "   [[Setvar Mapping:\n%s     Removed: %s]]\n" smap srem

(* Extraction of mappings *)
let extract_mappings  (sr: (int*int) IntMap.t)
    : setv_mapping * setv_mapping * IntSet.t  =
  IntMap.fold
    (fun i (il, ir) (accl, accr, seti) ->
      add_to_mapping il i accl, add_to_mapping ir i accr,
      IntSet.add i seti
    ) sr (setv_mapping_empty, setv_mapping_empty, IntSet.empty)
    
(* Map translation *)
let rec s_cons_map (f: int -> int) (g: int -> int) (s: set_cons) =
  match s with
  | S_mem (n, sr) -> S_mem (f n, s_expr_map f g sr)
  | S_eq (sl, sr) -> S_eq (s_expr_map f g sl, s_expr_map f g sr)
  | S_subset (sl, sr) -> S_subset (s_expr_map f g sl, s_expr_map f g sr)
and s_expr_map (f: int -> int) (g: int -> int) (e: set_expr) =
  match e with
  | S_var si -> S_var (g si)
  | S_node n -> S_node (f n)
  | S_uplus (sl, sr) -> S_uplus (s_expr_map f g sl, s_expr_map f g sr)
  | S_union (sl, sr) -> S_union (s_expr_map f g sl, s_expr_map f g sr)
  | S_empty -> S_empty


(** Transformers over set_expr and set_cons *)
(*  Take a function for setv to set_expr, and substitute everywhere *)
let gen_transformer f =
  let rec aux_expr e =
    match e with
    | S_var i -> f i
    | S_node _ | S_empty -> e
    | S_union (e0, e1) ->
        begin
          match aux_expr e0, aux_expr e1 with
          | S_empty, S_empty -> S_empty
          | S_empty, ee | ee, S_empty -> ee
          | ee0, ee1 -> S_union (ee0, ee1)
        end
    | S_uplus (e0, e1) ->
        begin
          match aux_expr e0, aux_expr e1 with
          | S_empty, S_empty -> S_empty
          | S_empty, ee | ee, S_empty -> ee
          | ee0, ee1 -> S_uplus (ee0, ee1)
        end in
  let aux_cons = function
    | S_mem (i, e0) -> S_mem (i, aux_expr e0)
    | S_eq (e0, e1) -> S_eq (aux_expr e0, aux_expr e1)
    | S_subset (e0, e1) -> S_subset (aux_expr e0, aux_expr e1) in
  aux_expr, aux_cons
let transform_expr (f: int -> set_expr): set_expr -> set_expr =
  fst (gen_transformer f)
let transform_cons (f: int -> set_expr): set_cons -> set_cons =
  snd (gen_transformer f)

(** Set of setv that appear *)
let set_expr_setvs, set_cons_setvs =
  let rec aux_expr s = function
    | S_var i -> IntSet.add i s
    | S_node _ | S_empty -> s
    | S_uplus (e0, e1) | S_union (e0, e1) -> aux_expr (aux_expr s e1) e0 in
  let aux_cons s = function
    | S_mem (_, e0) -> aux_expr s e0
    | S_eq (e0, e1) | S_subset (e0, e1) -> aux_expr (aux_expr s e1) e0 in
  aux_expr IntSet.empty, aux_cons IntSet.empty

(** Pruning some SETVs from a list of set constraints *)
(* This function should return an equivalent set of constraints, where
 * some SETVs are removed (it is used for is_le) *)
let set_cons_prune_setvs (torem: IntSet.t) (lc: set_cons list): set_cons list =
  let loc_debug = false in
  (* Phase 0. inspect all the variables used *)
  if loc_debug then
    List.iter (fun c -> Log.info "Prune,Ph-0: %s" (set_cons_2str c)) lc;
  (* Phase 1. search for sets equal to empty *)
  let lc =
    let lc, emptys =
      List.fold_left
        (fun (acc_remain, acc_emp) c ->
          if loc_debug then Log.info "Prune,Ph-1: %s" (set_cons_2str c);
          match c with
          | S_eq (S_var i, S_empty) | S_eq (S_empty, S_var i) ->
              if IntSet.mem i torem then
                acc_remain, IntSet.add i acc_emp
              else c :: acc_remain, acc_emp
          | _ -> c :: acc_remain, acc_emp
        ) ([ ], IntSet.empty) lc in
    let aux_setv i =
      try if IntSet.mem i emptys then S_empty else S_var i
      with Not_found -> S_var i in
    List.map (transform_cons aux_setv) lc in
  (* Phase 2. make a table of equalities, among SETVs to remove and try to
   * rename each class into one element that is not to remove *)
  let lc =
    let uf_add i uf = if Union_find.mem i uf then uf else Union_find.add i uf in
    let uf = (* equalities turned into a union_find *)
      List.fold_left
        (fun uf c ->
          if loc_debug then Log.info "Prune,Ph-2: %s" (set_cons_2str c);
          match c with
          | S_eq (S_var i, S_var j) ->
              let uf = uf_add i (uf_add j uf) in
              let ii, uf = Union_find.find i uf in
              let jj, uf = Union_find.find j uf in
              Union_find.union ii jj uf
          | _ -> uf
        ) Union_find.empty lc in
    let renamer, _ =
      IntSet.fold
        (fun i ((binding, tobind) as acc) ->
          if IntSet.mem i tobind && Union_find.mem i uf then
            let i, _ = Union_find.find i uf in
            let cli = Union_find.find_class i uf in
            let cli_k = List.filter (fun i -> not (IntSet.mem i torem)) cli in
            match cli_k with
            | [ ] -> (* no representant... no renaming *)
                binding, IntSet.remove i tobind
            | rep :: _ -> (* renaming *)
                let cli_r = List.filter (fun i -> IntSet.mem i torem) cli in
                List.fold_left
                  (fun (binding, tobind) ii ->
                    IntMap.add ii rep binding, IntSet.remove ii tobind
                  ) acc cli_r
          else acc (* no equalities or already done, nothing to do *)
        ) torem (IntMap.empty, torem) in
    (* Resolving all equalities that can be resolved *)
    let aux_setv i =
      try S_var (IntMap.find i renamer) with Not_found -> S_var i in
    let lc = List.map (transform_cons aux_setv) lc in
    (* Filtering out constraints of the form Si = Si *)
    let filter = function
      | S_eq (S_var i, S_var j) -> i != j
      | _ -> true in
    List.filter filter lc in
  (* Phase 3. Resolving equalities of the form S_i = ... where S_i should
   * disappear. As of now, this will crash if there are several such
   * equalities for a given S_i. *)
  let lc =
    let lc, map =
      List.fold_left
        (fun (acc_lc, acc_map) c ->
          if loc_debug then Log.info "Prune,Ph-3: %s" (set_cons_2str c);
          match c with
          | S_eq (S_var i, ex) | S_eq (ex, S_var i) ->
              if IntSet.mem i torem then acc_lc, IntMap.add i ex acc_map
              else c :: acc_lc, acc_map
          | _ -> c :: acc_lc, acc_map
        ) ([ ], IntMap.empty) lc in
    let aux_setv i = try IntMap.find i map with Not_found -> S_var i in
    List.map (transform_cons aux_setv) lc in
  lc

(* generate set constraints that should be proved equal from left side
 * that is, when a set variable \sete is mapped to many set
 * variables {\sete' \setf', ...}, choose one mapped set variable
 * (like \sete') and add equality constraints on
 * all the mapped set variables *)
let gen_eq_setctr (cur_si: setv_embedding): set_expr IntMap.t * set_cons list =
  IntMap.fold
    (fun id st (acc_m, acc_s) ->
      try
        let e = IntSet.choose st in
        IntMap.add id (S_var e) acc_m,
        IntSet.fold (fun ele acc -> S_eq (S_var e, S_var ele) :: acc)
          (IntSet.remove e st) acc_s
      with
        Not_found -> Log.fatal_exn "setvar embeddind has empty setimg"
    ) cur_si.n_img (IntMap.empty, [])

(* replace instantiated set variables from a set expression *)
let rec replace_sexpr (sr: set_expr) (inst: set_expr IntMap.t)
    (nmap: int IntMap.t): set_expr =
  try
    match sr with
    | S_var sid -> IntMap.find sid inst
    | S_node nid -> S_node (IntMap.find nid nmap)
    | S_uplus (sl, sr) ->
        S_uplus (replace_sexpr sl inst nmap, replace_sexpr sr inst nmap)
    | S_union (sl, sr) ->
        S_union (replace_sexpr sl inst nmap, replace_sexpr sr inst nmap)
    | S_empty -> S_empty
  with Not_found -> Log.fatal_exn "setvar not instantiated"

(* replace instantiated set variables from set constraints *)
let replace_cons (setctr: set_cons list)
    (inst: set_expr IntMap.t) (nmap: int IntMap.t)
    : set_cons list =
  try
    List.fold_left
      (fun acc ele ->
        let r_ele =
          match ele with
          | S_mem (nid, sr) ->
              S_mem (IntMap.find nid nmap, replace_sexpr sr inst nmap)
          | S_eq (sl, sr) ->
              S_eq (replace_sexpr sl inst nmap, replace_sexpr sr inst nmap)
          | S_subset (sl, sr) ->
              S_subset (replace_sexpr sl inst nmap,replace_sexpr sr inst nmap)
        in r_ele :: acc
      ) [] setctr
  with Not_found -> Log.fatal_exn "setvar/var not instantiated"

(* XR -> HS:
 *  - from the comment below, the meaning of the output is not totally clear
 *  - if this function is specific to is_le, maybe change its name to
 *    is_le_instantiate ?
 *)
(* is_le: instantiate set variables from equality set constraints
 * on the right side *)
let rec instantiate (setctr: set_cons list)
    (inst: set_expr IntMap.t) (nmap: int IntMap.t)
    : set_expr IntMap.t * set_cons list =
  let a_inst i se inst ctr =
    if IntMap.mem i inst then inst, (S_eq (S_var i, se))::ctr
    else
      let setv = set_expr_setvs se in
      if IntSet.for_all (fun i -> IntMap.mem i inst) setv then
        IntMap.add i (replace_sexpr se inst nmap) inst, ctr
      else inst, (S_eq (S_var i, se)):: ctr in
  let inst, r_setctr =
    List.fold_left
      (fun (inst, ctr) con ->
        match con with
        | S_mem _ -> inst, con :: ctr
        | S_subset _ -> inst, con :: ctr
        | S_eq (S_var i, S_var j) ->
            if IntMap.mem i inst then a_inst j (S_var i) inst ctr
            else a_inst i (S_var j) inst ctr
        | S_eq (S_var i, sr) -> a_inst i sr inst ctr
        | S_eq (sl, S_var j) -> a_inst j sl inst ctr
        | S_eq (sl, sr) -> inst, con :: ctr
      ) (inst, [ ]) setctr in
  if List.length r_setctr = List.length setctr then inst, r_setctr
  else instantiate r_setctr inst nmap


(* check if there is non instantiated set variables,
 * if there is non instantiated set variables, compute the minimal
 * set of non-instantiated set variables, that needs to instantiated
 * to fresh set variables *)
let check_non_inst (setctr: set_cons list) (inst: set_expr IntMap.t)
    : IntSet.t =
  let f_add i setv map =
    try  IntMap.add i (IntSet.union setv (IntMap.find i map)) map
    with Not_found -> IntMap.add i setv map in
  (* compute the dependence of non instantiated set variables *)
  let a_dep i inst se map =
    if IntMap.mem i inst then map
    else
      let setv = set_expr_setvs se in
      f_add i setv map in
  let dep =
    List.fold_left
      (fun acc con ->
        match con with
        | S_mem _ -> acc
        | S_subset _ -> acc
        | S_eq (S_var i, S_var j) ->
            if IntMap.mem j inst then a_dep i inst (S_var j) acc
            else a_dep j inst (S_var i) acc
        | S_eq (S_var i, sr) -> a_dep i inst sr acc
        | S_eq (sl, S_var j) -> a_dep j inst sl acc
        | S_eq (sl, sr) -> acc
      ) IntMap.empty setctr in
  let sc_inst, de_inst =
    IntMap.fold
      (fun k set (accl, accr) ->
         IntSet.add k accl, IntSet.union set accr)
      dep (IntSet.empty, IntSet.empty) in
  let de_inst = IntSet.diff de_inst sc_inst in
  let de_inst =
    IntSet.diff de_inst
      (IntMap.fold (fun k _ acc -> IntSet.add k acc) inst IntSet.empty) in
  if !Flags.flag_debug_is_le_shape then
    Log.force "Non-Instantiation set variables:\n%s"
      (IntSet.t_2str ";" de_inst);
  de_inst

(* liner uplus or union set variables from set expression *)
let rec linear_svars (se: set_expr) (is_disjoin: bool) =
  let f sl sr =
    match linear_svars sl is_disjoin,
          linear_svars sr is_disjoin with
    | Some (ssl, snl), Some (ssr, snr) ->
        assert (IntSet.inter ssl ssr = IntSet.empty);
        assert (IntSet.inter snl snr = IntSet.empty);
        Some (IntSet.union ssl  ssr, IntSet.union snl snr)
    | _, _ -> None in
  match se with
  | S_var s -> Some (IntSet.singleton s, IntSet.empty)
  | S_node n -> Some (IntSet.empty, IntSet.singleton n)
  | S_uplus (sl, sr) -> if is_disjoin then f sl sl else None
  | S_union (sl, sr) -> if is_disjoin then None else f sl sr
  | S_empty -> Some (IntSet.empty, IntSet.empty)

(* make uplus or union set expression *)
let make_sexp (setv: IntSet.t) (sv: IntSet.t) (is_disjoin: bool)
    : set_expr =
  let op =
    if is_disjoin then fun a b -> S_uplus (a, b)
    else fun a b -> S_union (a, b) in
  let f_setv setv se =
    IntSet.fold (fun ele acc -> op (S_var ele) acc) setv se in
  let f_sv sv se =
    IntSet.fold (fun ele acc -> op (S_node ele) acc) sv se in
  if not (IntSet.is_empty setv) then
    let min = IntSet.min_elt setv in
    f_sv sv (f_setv (IntSet.remove min setv) (S_var min))
  else if not (IntSet.is_empty sv) then
    let min = IntSet.min_elt sv in
    f_sv (IntSet.remove min sv) (S_node min)
  else S_empty


(** Functions on set var injections (for is_le) *)
module Semb =
  struct
    let empty: setv_embedding =
      { n_img = IntMap.empty ;
        n_pre = IntMap.empty }
    (* To string, compact version *)
    let ne_2str (ni: setv_embedding): string =
      IntMap.t_2str "\n" (IntSet.t_2str ",")  ni.n_img
    (* To string, long version *)
    let ne_full_2stri (ind: string) (inj: setv_embedding): string =
      IntMap.fold
        (fun i j acc ->
          Printf.sprintf "%s%s%d => %s\n" acc ind i (IntSet.t_2str "," j) 
        ) inj.n_img ""
    (* Tests membership *)
    let mem (i: int) (ni: setv_embedding): bool =
      IntMap.mem i ni.n_img
    (* Find an element in the mapping *)
    let find (i: int) (ni: setv_embedding): IntSet.t =
      IntMap.find i ni.n_img
    (* Add an element to the mapping *)
    let add (i: int) (j: int) (ni: setv_embedding): setv_embedding =
      let j_set = try IntMap.find i ni.n_img with Not_found -> IntSet.empty in
      let i_set = try IntMap.find j ni.n_pre with Not_found -> IntSet.empty in 
      { n_img = IntMap.add i (IntSet.add j j_set) ni.n_img ;
        n_pre = IntMap.add j (IntSet.add i i_set) ni.n_pre; }
    (* Initialization *)
    let init (m: setv_emb): setv_embedding =
      Aa_maps.fold add m empty
    (* Extraction of siblings information *)
    let siblings (ni: setv_embedding): IntSet.t IntMap.t =
      IntMap.fold
        (fun j pre acc ->
          if IntSet.cardinal pre > 1 then IntMap.add j pre acc
          else acc
        ) ni.n_pre IntMap.empty
  end
