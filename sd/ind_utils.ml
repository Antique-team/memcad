(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ind_utils.ml
 **       basic operations on inductive definitions
 ** Xavier Rival, 2011/06/30 *)
open Data_structures
open Lib

open Graph_sig
open Ind_sig
open Set_sig
open Sv_sig

(** Error report *)
module Log =
  Logger.Make(struct let section = "i_uts___" and level = Log_level.DEBUG end)

(** To string *)
(* Node types *)
let ntyp_2str (nt: ntyp): string =
  match nt with
  | Ntaddr -> "addr"
  | Ntraw  -> "raw"
  | Ntint  -> "int"
  | Ntset  -> "set"
let ntyp_2str_short (nt: ntyp): string =
  match nt with
  | Ntaddr -> "a"
  | Ntraw  -> "r"
  | Ntint  -> "i"
  | Ntset  -> "s"
let set_op_2str (op: set_op):string =
  match op with
  | Uplus -> "+"
  | Union -> "U"
let wk_typ_2str (t: wk_typ): string =
  match t with
  | `Eq -> "="
  | `Non -> "non"
  | `Leq -> "<="
  | `Geq -> ">="
  | `Add -> "+"
  | `SAdd op -> set_op_2str op
let ptr_wk_typ_2str (t: ptr_wk_typ): string =
  wk_typ_2str (t :> wk_typ)
let int_wk_typ_2str (t: int_wk_typ): string =
  wk_typ_2str (t :> wk_typ)
let set_wk_typ_2str (t: set_wk_typ): string =
  wk_typ_2str (t :> wk_typ)
let pars_wk_typ_2str (t: pars_wk_typ): string =
  Printf.sprintf " ptr_pars:%s\n int_pars:%s\n set_pars: %s\n"
    (IntMap.t_2str " | " ptr_wk_typ_2str t.ptr_typ)
    (IntMap.t_2str " | " int_wk_typ_2str t.int_typ)
    (IntMap.t_2str " | " set_wk_typ_2str t.set_typ)
(* Parameters *)
let formal_arg_2str: formal_arg -> string = function
  | `Fa_this      -> "this"
  | `Fa_var_new i -> Printf.sprintf "$%d" i
  | `Fa_par_ptr i -> Printf.sprintf "@p%d" i
  | `Fa_par_int i -> Printf.sprintf "@i%d" i
  | `Fa_par_set i -> Printf.sprintf "@s%d" i
let formal_main_arg_2str (fa: formal_main_arg): string =
  formal_arg_2str (fa :> formal_arg)
let formal_ptr_arg_2str (fa: formal_ptr_arg): string =
  formal_arg_2str (fa :> formal_arg)
let formal_int_arg_2str (fa: formal_int_arg): string =
  formal_arg_2str (fa :> formal_arg)
let formal_set_arg_2str (fa: formal_set_arg): string =
  formal_arg_2str (fa :> formal_arg)
let formal_arith_arg_2str (fa: formal_arith_arg): string =
  formal_arg_2str (fa :> formal_arg)
let formal_ptr_args_2str = gen_list_2str "" formal_ptr_arg_2str ", "
let formal_int_args_2str = gen_list_2str "" formal_int_arg_2str ", "
let formal_set_args_2str = gen_list_2str "" formal_set_arg_2str ", "
let indcall_2str (i: indcall): string =
  if i.ii_argp != [ ] || i.ii_argi != [ ] || i.ii_args != [ ] then
    Printf.sprintf "%s.%s(%s|%s|%s)" (formal_main_arg_2str i.ii_maina) i.ii_ind
      (formal_ptr_args_2str i.ii_argp) (formal_int_args_2str i.ii_argi)
      (formal_set_args_2str i.ii_args)
  else Printf.sprintf "%s.%s()" (formal_main_arg_2str i.ii_maina) i.ii_ind

(* Heap formulas *)
let cell_2str (c: cell): string =
  let arrow =
    if c.ic_size = 4 then "|->"
    else Printf.sprintf "|-%d->" c.ic_size in
  let off =
    match Offs.to_int_opt c.ic_off with
    | None -> "?"
    | Some d -> string_of_int d in
  Printf.sprintf "this->%s %s %s" off arrow
    (formal_arith_arg_2str c.ic_dest)
let heapatom_2str: heapatom -> string = function
  | Hacell c -> cell_2str c
  | Haind  i -> indcall_2str i
let hform_2str: hform -> string = gen_list_2str "emp" heapatom_2str " * "

(* Pure formulas *)
let sexpr_2str: sexpr -> string = function
  | Se_var s -> formal_set_arg_2str s
  | Se_uplus (s, x) ->
      Printf.sprintf "%s + { %s }"
        (gen_list_2str " " formal_set_arg_2str "+" s) (formal_arith_arg_2str x)
  | Se_union (s, x) ->
      Printf.sprintf "%s u { %s }"
        (gen_list_2str " " formal_set_arg_2str "u" s) (formal_arith_arg_2str x)
let rec aexpr_2str: aexpr -> string = function
  | Ae_cst c -> Printf.sprintf "%d" c
  | Ae_var x -> formal_arith_arg_2str x
  | Ae_plus (e0, e1) ->
      Printf.sprintf "%s + %s" (aexpr_2str e0) (aexpr_2str e1)
let sform_2str: sform -> string = function
  | Sf_mem (x, s) ->
      Printf.sprintf "%s # %s" (formal_arith_arg_2str x) (formal_set_arg_2str s)
  | Sf_equal (x, s) ->
      Printf.sprintf "%s == %s" (formal_set_arg_2str x) (sexpr_2str s)
  | Sf_empty x ->
      Printf.sprintf "%s == { }" (formal_set_arg_2str x)
let aform_2str: aform -> string = function
  | Af_equal (e0, e1) ->
      Printf.sprintf "%s = %s" (aexpr_2str e0) (aexpr_2str e1)
  | Af_noteq (e0, e1) ->
      Printf.sprintf "%s != %s" (aexpr_2str e0) (aexpr_2str e1)
  | Af_sup (e0, e1) ->
      Printf.sprintf "%s > %s" (aexpr_2str e0) (aexpr_2str e1)
  | Af_supeq (e0, e1) ->
      Printf.sprintf "%s => %s" (aexpr_2str e0) (aexpr_2str e1)
let pathexpr_2str pexpr =
  match pexpr with
  | Pe_epsilon -> "~"
  | Pe_seg flds ->
      Printf.sprintf "(%s)^*" (gen_list_2str "" Offs.t_2str "+" flds)
  | Pe_single flds ->
      Printf.sprintf "(%s)" (gen_list_2str "" Offs.t_2str "+" flds)
let path_2str p =
  let (sc, pt, dt) = p in
  Printf.sprintf "(%s, %s, %s)" (formal_ptr_arg_2str sc)
    (pathexpr_2str pt) (formal_ptr_arg_2str dt)
let pform_atom_2str: pformatom -> string = function
  | Pf_alloc sz -> Printf.sprintf "alloc( this, %d )" sz
  | Pf_set f -> sform_2str f
  | Pf_arith f -> aform_2str f
  | Pf_path f -> path_2str f
let pform_2str: pform -> string = gen_list_2str "" pform_atom_2str " & "

(* Rules *)
let ir_kind_2str: ir_kind -> string = function
  | Ik_unk -> "unknown"
  | Ik_empz -> "{emp,0}"
  | Ik_range (r0, r1) -> Printf.sprintf "[%d...%d[" r0 r1
let irule_2str (r: irule): string =
  let typs =
    IntMap.fold
      (fun i typ acc ->
        Printf.sprintf "%s %s" acc (ntyp_2str typ)
      ) r.ir_typ "" in
  Printf.sprintf "| [%d%s]\n\t- %s\n\t- %s\n"
    r.ir_num typs (hform_2str r.ir_heap) (pform_2str r.ir_pure)

(* Inductive definitions *)
let ind_2str (i: ind): string =
  let srules = gen_list_2str "" irule_2str "" i.i_rules in
  let buf = Buffer.create 80 in
  Printf.bprintf buf "%s<%d,%d> :=\n%s\n"
    i.i_name i.i_ppars i.i_ipars srules;
  (* Printing the analysis results *)
  List.iteri
    (fun i ir ->
      Printf.bprintf buf "  rule %d, ptr: {%s}, int: {%s}, set: {%s} => %b\n" i
        (IntSet.t_2str ", " ir.ir_uptr) (IntSet.t_2str ", " ir.ir_uint)
        (IntSet.t_2str ", " ir.ir_uset) ir.ir_unone
    ) i.i_rules;
  Printf.bprintf buf "  %s\n"
    (gen_list_2str "" path_2str ";" i.i_ppath);
  Printf.bprintf buf "%s\n"
    (gen_list_2str ""
       (fun (a, b, c) ->
         Printf.sprintf "%s, => (%s, %s)" (aform_2str a)
           (gen_list_2str "" aform_2str ";" b)
           (gen_list_2str "" sform_2str ";" c)
       ) "\n" i.i_rules_cons);
  Printf.bprintf buf "All-rules:\n%sEmp_rule:\n%s\n"
    (pars_wk_typ_2str i.i_pars_wktyp)
    (pars_wk_typ_2str i.i_emp_pars_wktyp);
  Buffer.contents buf

(* shorter version of ind_2str *)
let rules_to_string (i: ind): string =
  let srules = gen_list_2str "" irule_2str "" i.i_rules in
  Printf.sprintf "%s<%d,%d> :=\n%s"
    (if i.i_name <> "" && String.get i.i_name 0 = '%' then
       (* names introduced by the C frontend (they start with '%')
        * are not valid ind. def. names *)
       String.pop i.i_name
     else i.i_name)
    i.i_ppars
    i.i_ipars
    srules

(* save rules to a file *)
let rules_to_file (out_file: string) (il: ind list): unit =
  with_out_file out_file
    (fun out ->
      List.iter
        (fun i ->
          let rules_str = rules_to_string i in
          Printf.fprintf out "%s.\n" rules_str
        ) il;
    )


(** Visitor *)
let visitor (fp: 'a -> int -> 'a) (fi: 'a -> int -> 'a) (fs: 'a -> int -> 'a)
    : ('a -> hform -> 'a) * ('a -> pform -> 'a) =
  let do_formal_arg a = function
    | `Fa_this | `Fa_var_new _ -> a
    | `Fa_par_ptr i -> fp a i
    | `Fa_par_int i -> fi a i
    | `Fa_par_set i -> fs a i in
  let do_indcall a ic =
    let a = do_formal_arg a ic.ii_maina in
    let a = List.fold_left do_formal_arg a ic.ii_argp in
    let a = List.fold_left do_formal_arg a ic.ii_argi in
    List.fold_left do_formal_arg a ic.ii_args in
  let do_heapatom a = function
    | Hacell c -> do_formal_arg a c.ic_dest
    | Haind ic -> do_indcall a ic in
  let do_hform (a: 'a) (h: hform): 'a = List.fold_left do_heapatom a h in
  let do_sexpr a = function
    | Se_var v -> do_formal_arg a v
    | Se_uplus (v0, v1) ->
        do_formal_arg (List.fold_left do_formal_arg a v0) v1
    | Se_union (v0, v1) ->
        do_formal_arg (List.fold_left do_formal_arg a v0) v1 in
  let rec do_aexpr a = function
    | Ae_cst _ -> a
    | Ae_var v -> do_formal_arg a v
    | Ae_plus (ae0, ae1) -> do_aexpr (do_aexpr a ae0) ae1 in
  let do_sform a = function
    | Sf_mem (v0, v1) -> do_formal_arg (do_formal_arg a v0) v1
    | Sf_equal (v0, as1) -> do_sexpr (do_formal_arg a v0) as1
    | Sf_empty v -> do_formal_arg a v in
  let do_aform a = function
    | Af_equal (ae0, ae1)
    | Af_noteq (ae0, ae1)
    | Af_supeq (ae0, ae1)
    | Af_sup (ae0, ae1) -> do_aexpr (do_aexpr a ae0) ae1 in
  let do_pathform a (sc, _, dt) =
    do_formal_arg (do_formal_arg a sc) dt in
  let do_pformatom a = function
    | Pf_alloc _ -> a
    | Pf_set   f -> do_sform a f
    | Pf_arith f -> do_aform a f
    | Pf_path p  -> do_pathform a p in
  let do_pform (a: 'a) (p: pform): 'a = List.fold_left do_pformatom a p in
  do_hform, do_pform
let visitor_hform fp fi fs = fst (visitor fp fi fs)
let visitor_pform fp fi fs = snd (visitor fp fi fs)


(** Equality test *)
let compare (i0: ind) (i1: ind): int =
  if i0 == i1 then 0
  else
    (* if it failed, it would mean an inductive is improperly copied all over
     * the place, which we normally avoid (a given inductive is represented
     * by the same OCaml object all the time *)
    let c = String.compare i0.i_name i1.i_name in
    assert (c != 0);
    c


(** Operations on tags *)
let ntyp_merge (nt0: ntyp) (nt1: ntyp): ntyp =
  if nt0 = nt1 then nt0
  else
    begin
      Log.info "Merging distict SV types: %s %s"
        (ntyp_2str nt0) (ntyp_2str nt1);
      Ntraw
    end


(** Utilities for inductive definitions analyses *)
let iter_heap (f: 'a -> heapatom -> 'a) (i: ind) (x: 'a): 'a =
  List.fold_left
    (fun acc r ->
      List.fold_left f acc r.ir_heap
    ) x i.i_rules



(** Inductive parameters use analysis:
 *  For each rule, we compute the set of parameters that are NOT used,
 *  so as to allow for parameters weakening later in join *)
let indpar_use_analysis (ind: ind): ind =
  (* compute the set of parameters of all sorts *)
  let rec f i acc = if i < 0 then acc else f (i - 1) (IntSet.add i acc) in
  let g i = f (i-1) IntSet.empty in
  let pars = g ind.i_ppars, g ind.i_ipars, g ind.i_spars in
  (* compute the information for each rule *)
  let f_ptr (sp, si, ss) i = IntSet.remove i sp, si, ss
  and f_int (sp, si, ss) i = sp, IntSet.remove i si, ss
  and f_set (sp, si, ss) i = sp, si, IntSet.remove i ss in
  let do_hform, do_pform = visitor f_ptr f_int f_set in
  let rules =
    List.map
      (fun ir ->
        let sp, si, ss = do_hform (do_pform pars ir.ir_pure) ir.ir_heap in
        let bn = IntSet.cardinal sp = ind.i_ppars
            && IntSet.cardinal si = ind.i_ipars
            && IntSet.cardinal ss = ind.i_spars in
        { ir with
          ir_uptr  = sp;
          ir_uint  = si;
          ir_uset  = ss;
          ir_unone = bn }
      ) ind.i_rules in
  { ind with i_rules = rules }
(* Functions to query the result of this analysis *)
let par_may_use_rules_gen (fkind: ir_kind -> bool)
    (par: formal_aux_arg) (ind: ind): bool =
  try
    List.iter
      (fun ir ->
        if fkind ir.ir_kind then
          match par with
          | `Fa_par_ptr i -> if IntSet.mem i ir.ir_uptr then raise True
          | `Fa_par_int i -> if IntSet.mem i ir.ir_uint then raise True
          | `Fa_par_set i -> if IntSet.mem i ir.ir_uset then raise True
      ) ind.i_rules;
    false
  with True -> true
let kind_all_empty = function
  | Ik_empz | Ik_unk -> true
  | Ik_range (_,_) -> false
let kind_all_non_empty = function
  | Ik_unk | Ik_range (_,_) -> true
  | Ik_empz -> false
let par_may_use_rules_emp: formal_aux_arg -> ind -> bool =
  par_may_use_rules_gen kind_all_empty
let par_may_use_rules_notemp: formal_aux_arg -> ind -> bool =
  par_may_use_rules_gen kind_all_non_empty
let no_par_use_rules_gen (fkind: ir_kind -> bool) (ind: ind): bool =
  try
    List.iter
      (fun ir ->
        if fkind ir.ir_kind && not ir.ir_unone then raise False
      ) ind.i_rules;
    true
  with False -> false
let no_par_use_rules_emp: ind -> bool =
  no_par_use_rules_gen kind_all_empty
let no_par_use_rules_notemp: ind -> bool =
  no_par_use_rules_gen kind_all_non_empty



(** Nodes analysis: populates the map of types
 *  - either checks the types are coherent if the map is already full;
 *  - or populates map ir_typ with "Ntraw" record (no type assumption) *)
let indnodes_analysis (i: ind): ind =
  let nrules =
    List.map
      (fun ir ->
        if ir.ir_num = 0 then
          begin
            assert (ir.ir_typ = IntMap.empty);
            ir
          end
        else if ir.ir_typ = IntMap.empty then
          (* we make up a map of type "raw" *)
          let rec aux i acc =
            if i < 0 then acc
            else aux (i-1) (IntMap.add i Ntraw acc) in
          { ir with ir_typ = aux ir.ir_num IntMap.empty }
        else
          (* we need to check that the indexes in the map correspond *)
          begin
            assert (IntMap.cardinal ir.ir_typ = ir.ir_num);
            IntMap.iter
              (fun ix _ ->
                assert (0 <= ix && ix < ir.ir_num)
              ) ir.ir_typ;
            ir
          end
      ) i.i_rules in
  { i with i_rules = nrules }


(** Inductive "direction", that is paths traversed from one ind call to
 *  the next one:
 *  This analysis is very incomplete
 *  it considers only paths of the form this.f->$i * $i.ind(...) *)
let inddir_analysis (ind: ind): ind =
  let dirs, self_dirs =
    List.fold_left
      (fun ((dirs, self_dirs) as acc1) r ->
        let m =
          List.fold_left
            (fun acc2 -> function
              | Haind _ -> acc2
              | Hacell c ->
                  match c.ic_dest with
                  | `Fa_var_new i -> IntMap.add i c.ic_off acc2
                  | _ -> acc2
            ) IntMap.empty r.ir_heap in
        List.fold_left
          (fun acc3 -> function
            | Hacell _ -> acc3
            | Haind ic ->
                match ic.ii_maina with
                | `Fa_this -> acc3
                | `Fa_var_new i ->
                    try
                      let o = IntMap.find i m in
                      let dirs' = Offs.OffSet.add o (fst acc3) in
                      (* self_dirs are more restrictive than dirs *)
                      let self_dirs' =
                        if ic.ii_ind = ind.i_name then
                          Offs.OffSet.add o (snd acc3)
                        else snd acc3 in
                      dirs', self_dirs'
                    with Not_found -> acc3
          ) acc1 r.ir_heap
      ) (Offs.OffSet.empty, Offs.OffSet.empty) ind.i_rules in
  if !Flags.flag_debug_ind_analysis then
    begin
      Log.force "Inductive %s ind directions: { %s }"
        ind.i_name (Offs.OffSet.t_2str ", " dirs);
      Log.force "Inductive %s self ind directions: { %s }"
        ind.i_name (Offs.OffSet.t_2str ", " self_dirs)
    end;
  { ind with i_dirs = dirs; i_may_self_dirs = self_dirs }


(** Inductive definition parameters analysis
 *  This analysis aims at inferring whether parameters of inductive
 *  definitions may be constant or additive, which helps algorithms
 *  (non local unfolding, join...) *)
let pars_rec_top =
  { pr_ptr_const  = IntMap.empty;
    pr_int        = IntMap.empty;
    pr_set        = IntMap.empty }
let par_rec_2str (p: par_rec): string =
  match p.pr_const, p.pr_add with
  | true , _     -> "constant"
  | false, true  -> "additive"
  | false, false -> "?????"
let pars_rec_2str (p: pars_rec): string =
  let s =
    IntMap.fold
      (fun i b acc ->
        Printf.sprintf "%s - ptr @%d: %s\n" acc i
          (if b then "constant" else "????")
      ) p.pr_ptr_const "" in
  let f kind =
    IntMap.fold
      (fun i r acc ->
        Printf.sprintf "%s - %s @%d: %s\n" acc kind i (par_rec_2str r)) in
  f "int" p.pr_int s
(* Parameters analysis *)
let indpars_analysis (ind: ind): ind =
  let flag_debug = !Flags.flag_debug_ind_analysis in
  if flag_debug then
    Log.force "Parameters analysis of inductive definition %s" ind.i_name;
  let make_map x i =
    let rec aux acc i =
      if i < 0 then acc
      else aux (IntMap.add i x acc) (i-1) in
    aux IntMap.empty (i-1) in
  let pr_empty =
    { pr_const = true ;
      pr_add   = true } in
  let t_empty =
    { st_const = true ;
      st_add   = true ;
      st_head  = true ;
      st_mono  = true ; } in
  let res =
    { pr_ptr_const = make_map true ind.i_ppars ;
      pr_int       = make_map pr_empty ind.i_ipars ;
      pr_set       = make_map t_empty ind.i_spars } in
  (* Algo for pr_set:
   *  - start from most precise assignment
   *  - for each rule, make the list of calls to the same inductive
   *  - build abstract constraints for each rule
   *    => equalities
   *    => linear sums with this (linearization of equalities; fails if not lin)
   *  - intersection
   *)
  let do_rule (acc: pars_rec) (r: irule): pars_rec =
    Log.info "do_rule:\n%s" (irule_2str r);
    let rec_calls =
      List.fold_left
        (fun acc -> function
          | Hacell _ -> acc
          | Haind c ->
              if String.compare c.ii_ind ind.i_name = 0 then c.ii_args :: acc
              else acc
        ) [ ] r.ir_heap in
    (* linearization of set expressions, will help to extend this analysis *)
    let rec linearize (f: sform)
        : formal_set_arg * formal_set_arg list * formal_arith_arg list =
      match f with
      | Sf_empty sl -> sl, [ ], [ ]
      | Sf_equal (sl, Se_var sr) -> sl, [ sr ], [ ]
      | Sf_equal (sl, Se_uplus (sr, u)) -> sl, sr, [ u ]
      | Sf_equal (sl, Se_union (sr, u)) -> sl, sr, [ u ]
      | Sf_mem _ -> Log.fatal_exn "non linearizable" in
    (* set variables known to be empty, and known set relations *)
    let emp, rel, vpars, vnews =
      List.fold_left
        (fun (emp, rel, vpars, vnews) -> function
          | Pf_alloc _ | Pf_arith _ | Pf_set (Sf_mem _) | Pf_path _ ->
              emp, rel, vpars, vnews
          | Pf_set f ->
              let dst, ls, ln = linearize f in
              let vpars, vnews =
                let f (vp, vn) = function
                  | `Fa_par_set i -> IntSet.add i vp, vn
                  | `Fa_var_new i -> vp, IntSet.add i vn in
                List.fold_left f (f (vpars, vnews) dst) ls in
              match dst, ls, ln with
              | `Fa_par_set i, [ ], [ ] ->
                  IntSet.add i emp, rel, IntSet.add i vpars, vnews
              | `Fa_par_set i, ls, ln ->
                  assert (not (IntMap.mem i rel)); (* otherwise, overwrite *)
                  emp, IntMap.add i (ls, ln) rel, vpars, vnews
              | _, _, _ -> emp, rel, vpars, vnews
        ) (IntSet.empty, IntMap.empty, IntSet.empty, IntSet.empty) r.ir_pure in
    let uf =
      IntMap.fold
        (fun i x uf ->
          match x with
          | [ s ], [ ] ->
              let c0, uf = Union_find.find (`Fa_par_set i) uf in
              let c1, uf = Union_find.find s uf in
              Union_find.union c0 c1 uf
          | _, _ -> uf
        ) rel Union_find.empty in
    (* flatten list to set; aborts if `Fa_par_set present *)
    let flatten l =
      List.fold_left
        (fun acc -> function
          | `Fa_par_set j -> raise Stop
          | `Fa_var_new j -> IntSet.add j acc
        ) IntSet.empty l in
    (* treat the arguments of the sub-calls *)
    let rec aux i ((accc, acch, acca, accm) as acc) subs totspars =
      if i = totspars then acc
      else
        let sub0  = List.map List.hd subs
        and subso = List.map List.tl subs in
        let pre_is_mono = (* never used anywhere else than mem *)
          try
            List.iter
              (function
                | `Fa_par_set i -> if IntSet.mem i vpars then raise Stop
                | `Fa_var_new i -> if IntSet.mem i vnews then raise Stop
              ) sub0;
            true
          with Stop -> false in
        let acc =
          if sub0 = [ ] then (* no recrusive call *)
            let accm = if pre_is_mono then IntSet.add i accm else accm in
            if IntSet.mem i emp then (* const, head, add *)
              IntSet.add i accc, IntSet.add i acch, IntSet.add i acca, accm
            else (* const, add *)
              IntSet.add i accc, acch, IntSet.add i acca, accm
          else
            let is_const = (* if sub call params always provably equal *)
              try
                List.iter
                  (fun x ->
                    if x = `Fa_par_set i then ( )
                    else
                      let c, uf = Union_find.find (`Fa_par_set i) uf in
                      if c != fst (Union_find.find x uf) then raise Stop
                  ) sub0;
                true
              with Stop | Not_found -> false in
            let is_mono = (* if const, and never used anywhere else than mem *)
              is_const && pre_is_mono in
            Log.info "is_mono: %b" is_mono;
            let is_head, is_add =
              try
                let ls, ln = IntMap.find i rel in
                (* check if add *)
                let is_add =
                  try
                    let a = flatten sub0 in
                    let b = flatten ls in
                    IntSet.equal a b
                  with Stop -> false in
                (* head if add + ln = [ This ] *)
                let is_head = is_add && ln = [ `Fa_this ] in
                is_head, is_add
              with Not_found -> false, false in
            let f b acc = if b then IntSet.add i acc else acc in
            f is_const accc, f is_head acch, f is_add acca, f is_mono accm in
        aux (i+1) acc subso totspars in
    let argsc, argsh, argsa, argsm =
      aux 0 (IntSet.empty,IntSet.empty,IntSet.empty,IntSet.empty)
        rec_calls ind.i_spars in
    (* compute the intersection *)
    let nset =
      IntMap.mapi
        (fun i t ->
          Log.info "is_mono: %b%b" t.st_mono (IntSet.mem i argsm);
          { st_const = t.st_const && IntSet.mem i argsc;
            st_head  = t.st_head  && IntSet.mem i argsh;
            st_add   = t.st_add   && IntSet.mem i argsa;
            st_mono  = t.st_mono  && IntSet.mem i argsm; }
        ) acc.pr_set in
    { acc with pr_set = nset } in
  let res = List.fold_left do_rule res ind.i_rules in
  (* functions to treat pointer, integer and set parameters *)
  let do_ptr_pars (acc: pars_rec) (lp: formal_ptr_args): pars_rec =
    let discard_info i acc =
      assert (IntMap.mem i acc.pr_ptr_const);
      { acc with pr_ptr_const = IntMap.add i false acc.pr_ptr_const } in
    let _, acc =
      List.fold_left
        (fun (i, acc) (arg: formal_ptr_arg) ->
          match arg with
          | `Fa_this ->
              i + 1, discard_info i acc
          | `Fa_var_new _ -> Log.todo_exn "ipa: ptr, new"
          | `Fa_par_ptr k ->
              if k = i then (* info about the ith parameter is preserved *)
                i + 1, acc
              else (* parameter maybe not constant, info must be removed *)
                i + 1, discard_info i acc
        ) (0, acc) lp in
    acc in
  let pr_discard (i: int) (m: par_rec IntMap.t): par_rec IntMap.t =
    assert (IntMap.mem i m);
    let no_info = { pr_const = false;
                    pr_add   = false } in
    IntMap.add i no_info m in
  let pr_discard_cst (i: int) (m: par_rec IntMap.t): par_rec IntMap.t =
    assert (IntMap.mem i m);
    let old_info = IntMap.find i m in
    let new_info = { old_info with
                     pr_const = false } in
    IntMap.add i new_info m in
  let do_int_pars (linrels: int IntMap.t) (acc: pars_rec)
      (li: formal_int_args): pars_rec =
    let discard i acc =
      { acc with pr_int = pr_discard i acc.pr_int } in
    let discard_cst i acc =
      { acc with pr_int = pr_discard_cst i acc.pr_int } in
    let _, acc =
      List.fold_left
        (fun (i, acc) (arg: formal_int_arg) ->
          match arg with
          | `Fa_par_int k ->
              if k = i then (* info about the ith parameter is preserved *)
                i + 1, acc
              else (* parameter maybe not constant, info must be removed *)
                i + 1, discard i acc
          | `Fa_var_new n ->
              try
                let k = IntMap.find n linrels in
                if k = i then (* parameter may be additive *)
                  i + 1, discard_cst i acc
                else (* parameter maybe not constant, info must be removed *)
                  i + 1, discard i acc
              with
              | Not_found -> i + 1, discard i acc
        ) (0, acc) li in
    acc in
  (* iteration over the set of all rules *)
  let res =
    List.fold_left
      (fun acc ir ->
        (* computation of the set of local variables that are in a linear
         * relation together with an integer parameter *)
        let m_linrel =
          List.fold_left
            (fun rels -> function
               | Pf_alloc _ | Pf_set _ | Pf_arith (Af_noteq _)
               | Pf_path _ | Pf_arith (Af_sup _)
               | Pf_arith (Af_supeq _)-> rels
              | Pf_arith (Af_equal (ae0, ae1)) ->
                  match ae0, ae1 with
                  | Ae_var (`Fa_var_new n),
                    Ae_plus (Ae_var (`Fa_par_int m), Ae_cst _)
                  | Ae_var (`Fa_par_int m),
                    Ae_plus (Ae_var (`Fa_var_new n), Ae_cst _)
                  | Ae_plus (Ae_var (`Fa_var_new n), Ae_cst _),
                    Ae_var (`Fa_par_int m)
                  | Ae_plus (Ae_var (`Fa_par_int m), Ae_cst _),
                    Ae_var (`Fa_var_new n) ->
                      IntMap.add n m rels
                  | _, _ -> rels
            ) IntMap.empty ir.ir_pure in
        (* computation of what is preserved under that rule, based on the
         * recursive calls that can be found *)
        List.fold_left
          (fun acc -> function
            | Hacell _ -> acc
            | Haind ic ->
                if String.compare ic.ii_ind ind.i_name = 0 then
                  begin
                    assert (List.length ic.ii_argi = ind.i_ipars);
                    assert (List.length ic.ii_argp = ind.i_ppars);
                    assert (List.length ic.ii_args = ind.i_spars);
                    let acc = do_ptr_pars acc ic.ii_argp in
                    let acc = do_int_pars m_linrel acc ic.ii_argi in
                    acc
                  end
                else acc (* other inductive called, ignore *)
          ) acc ir.ir_heap
      ) res ind.i_rules in
  if flag_debug then
    begin
      Log.force "%s" (pars_rec_2str res);
      IntMap.iter
        (fun i st ->
          Log.force "%s: %d :::===> %s" ind.i_name i
            (Set_utils.set_par_type_2str st)
        ) res.pr_set
    end;
  { ind with i_pkind = res }


(** Computation of the inductives that have ONE rule corresponding to:
 *  - an empty region;
 *  - and a null pointer.
 *  This information can be used in order to speed up materialization. *)
exception Success
exception Failure
let empty_heap_rule_analysis (i: ind): ind =
  (* checks whether a rule has the above property *)
  let check_rule (r: irule): bool =
    try
      if r.ir_heap = [ ] then
        begin
          List.iter
            (function
              | Pf_arith (Af_equal (Ae_var `Fa_this, Ae_cst 0))
              | Pf_arith (Af_equal (Ae_cst 0, Ae_var `Fa_this)) ->
                  raise Success
              | _ -> raise Failure
            ) r.ir_pure;
          false
        end
      else false
    with
    | Success -> true
    | Failure -> false in
  try
    let b =
      List.fold_left
        (fun acc r ->
          if check_rule r then
            if acc then raise Failure (* found a second empty rule *)
            else true (* found one empty rule *)
          else acc
        ) false i.i_rules in
    { i with i_mt_rule = b }
  with
  | Failure -> { i with i_mt_rule = false } (* multiple empty rules found *)


(** Computation of the inductives that have ONE rule corresponding to:
 *  - an empty region;
 *  - and an integer parameter.
 *  This information can be used in order to speed up materialization. *)
exception Found_iparam of int
let empty_heap_iparam_rule_analysis (i: ind): ind =
  (* checks whether a rule has the above property *)
  let check_rule (r: irule): int option =
    try
      if r.ir_heap = [ ] then
        begin
          List.iter
            (function
              | Pf_arith (Af_equal (Ae_var `Fa_this, Ae_var (`Fa_par_ptr x)))
              | Pf_arith (Af_equal (Ae_var (`Fa_par_ptr x), Ae_var `Fa_this)) ->
                  raise (Found_iparam x)
              | _ -> raise Failure
            ) r.ir_pure;
          None
        end
      else None
    with
    | Found_iparam ip -> Some ip
    | Failure -> None in
  let b =
    List.fold_left
      (fun acc r ->
         match check_rule r with
         | Some ip ->
             begin
               match acc with
               | Some _ -> raise Failure (* found a second empty rule *)
               | None -> Some ip (* found one empty rule *)
             end
         | None -> acc
      ) None i.i_rules in
  match b with
  | Some ip -> { i with i_emp_ipar = ip }
  | None -> i (* no such or multiple empty rules found *)


(** Computation of parameters which may denote prev pointers.
 *  This information is important for backward unfolding. *)
let bwdpar_analysis (i: ind): ind =
  (* search for parameters which are candidate prev pointers *)
  let allpars =
    let rec aux k =
      if k < 0 then IntSet.empty else IntSet.add k (aux (k-1)) in
    aux (i.i_ppars - 1) in
  let prev_pars =
    let f_doit (acc: IntSet.t): heapatom -> IntSet.t = function
      | Hacell _ -> acc
      | Haind ic ->
          let _, m =
            List.fold_left
              (fun (i, acc) -> function
                | `Fa_this -> i+1, acc
                | _ -> i+1, IntSet.remove i acc
              ) (0, acc) ic.ii_argp in
          m in
    iter_heap f_doit i allpars in
  if !Flags.flag_debug_ind_analysis then
    Log.force "Prev pointers: %s" (intset_2str prev_pars);
  (* collect all possibly pointer fields *)
  let allfields =
    let f_doit (acc: Offs.OffSet.t): heapatom -> Offs.OffSet.t = function
      | Haind _ -> acc
      | Hacell c ->
          if c.ic_size = Flags.abi_ptr_size then Offs.OffSet.add c.ic_off acc
          else acc in
    iter_heap f_doit i Offs.OffSet.empty in
  (* check which fields are prev fields *)
  let prev_fields =
    let f_doit (acc: Offs.OffSet.t): heapatom -> Offs.OffSet.t = function
      | Haind _ -> acc
      | Hacell c ->
          if Offs.OffSet.mem c.ic_off acc then
            match c.ic_dest with
            | `Fa_par_ptr i ->
                if IntSet.mem i prev_pars then acc
                else Offs.OffSet.remove c.ic_off acc
            | _ -> Offs.OffSet.remove c.ic_off acc
          else acc in
    iter_heap f_doit i allfields in
  if !Flags.flag_debug_ind_analysis then
    Log.force "Prev fields: %s" (Offs.OffSet.t_2str "," prev_fields);
  (* search fields which are always equal to a prev pointer parameter *)
  { i with
    i_pr_pars = prev_pars ;
    i_pr_offs = prev_fields }


(** Computation of rules that are useful for segments:
 *  only rules that have at least one recursive call need be considered
 *  for segments *)
let ind_calc_segrules (i: ind): ind =
  let l =
    List.filter
      (fun r ->
        List.fold_left
          (fun acc -> function
            | Hacell _ -> acc
            | Haind _ -> true
          ) false r.ir_heap
      ) i.i_rules in
  (* checks whether the root of a non empty segment may not be the null value;
   * if that is the case, the reduction below becomes available:
   *    [ a.i()====>b.i'() /\ a=0 ]   =>   [ a=b; empty segment ]   *)
  let rnull =
    (* compute whether a rule satisfies (P) the reduction above is ok *)
    let f_rule r =
      (* if there is a (non empty) field from this, the rule satisfies P *)
      let b0 =
        List.fold_left
          (fun acc -> function
            | Hacell c -> acc || c.ic_size > 0
            | _ -> acc
          ) false r.ir_heap in
      (* if there is a predicate this not be null, the rule satisfies P *)
      let b1 =
        List.fold_left
          (fun acc -> function
            | Pf_arith (Af_noteq (Ae_var `Fa_this, Ae_cst 0))
            | Pf_arith (Af_noteq (Ae_cst 0, Ae_var `Fa_this)) -> true
            | _ -> acc
          ) false r.ir_pure in
      b0 || b1 in
    List.fold_left (fun acc r -> acc && f_rule r) true l in
  (* debug and result *)
  if !Flags.flag_debug_ind_analysis then
    Log.force "Found %d segment rules in %s; reduction property: %b"
      (List.length l) i.i_name rnull;
  { i with
    i_srules = l;
    i_reds0  = rnull }


(** Computation of fields that are equal to parameters *)
let ind_field_pars (ind: ind): ind =
  (* types: ptrs -> offset (the least one) *)
  let join x0 x1 =
    match x0, x1 with
    | None, x | x, None -> x
    | Some y0, Some y1 ->
        let m =
          IntMap.fold
            (fun i j0 acc ->
              try
                if IntMap.find i y1 = j0 then IntMap.add i j0 acc
                else acc
              with Not_found -> acc
            ) y0 IntMap.empty in
        Some m in
  let f_rule (r: irule): int IntMap.t =
    List.fold_left
      (fun acc -> function
        | Haind _ -> acc
        | Hacell c ->
            (* if offset is integer, and points to ptr, add to map *)
            match Offs.to_int_opt c.ic_off, c.ic_dest with
            | Some i, `Fa_par_ptr j -> IntMap.add j i acc
            | _, _ -> acc
      ) IntMap.empty r.ir_heap in
  let result =
    List.fold_left
      (fun acc r ->
        if r.ir_heap = [ ] then acc
        else join acc (Some (f_rule r))
      ) None ind.i_rules in
  let f_pars =
    match result with
    | None -> IntMap.empty
    | Some m -> m in
  if !Flags.flag_debug_ind_analysis && f_pars != IntMap.empty then
    Log.force "Field parameters %s: {{ %s }}" ind.i_name
      (IntMap.t_2str ", " string_of_int f_pars);
  { ind with i_fl_pars = f_pars }


(** Computation of ir_kind fields
 *  i.e., when a rule is either necessary null (emp) or non null (non emp) *)
let ind_rules_kind (ind: ind): ind =
  let f_rule (r: irule): irule =
    let kind =
      try
        (* check whether the pointer is null *)
        let this_is_null =
          try
            List.iter
              (function
                | Pf_arith (Af_equal (Ae_var `Fa_this, Ae_cst 0))
                | Pf_arith (Af_equal (Ae_cst 0, Ae_var `Fa_this)) ->
                    raise Success (* it is null *)
                | _ -> raise Failure
              ) r.ir_pure;
            false
          with
          | Success -> true
          | Failure -> false in
        (* check whether the heap region is empty *)
        let region_is_emp = r.ir_heap = [ ] in
        (* compute the range *)
        let range =
          List.fold_left
            (fun acc -> function
              | Haind ic -> acc
              | Hacell c ->
                  match Offs.to_int_opt c.ic_off with
                  | None -> raise Failure
                  | Some o ->
                      let rec aux k acc =
                        if o > k then acc else aux (k-1) (IntSet.add k acc) in
                      aux (o+c.ic_size-1) acc
            ) IntSet.empty r.ir_heap in
        (* gather all the info, and produce a valid kind *)
        match this_is_null, region_is_emp, range with
        | true, true, _ -> Ik_empz
        | false, true, _ -> Log.warn "empty region, non null"; Ik_empz
        | false, false, s ->
            if s = IntSet.empty then
              Log.fatal_exn "rule kind: non null rull, empty range"
            else Ik_range (IntSet.min_elt s, 1 + IntSet.max_elt s)
        | _, _, _ -> Log.fatal_exn "undetermined rule kind"
      with Failure -> Ik_unk in
    if !Flags.flag_debug_ind_analysis then
      Log.force "Rule kind: %s" (ir_kind_2str kind);
    { r with ir_kind = kind } in
  { ind with i_rules = List.map f_rule ind.i_rules }


(** Computation of rules_cons, a constraint of a rule
 *  that differ from all the other rules
 *  i.e., when this = 0 and this != 0 *)
let ind_rules_cons (ind: ind): ind =
  let weak_arith_arg = function
    | `Fa_this | `Fa_par_int _ | `Fa_par_ptr _ -> true
    | `Fa_var_new i -> false in
  let weak_set_arg = function
    | `Fa_par_set _ -> true
    | `Fa_var_new i -> false in
  let rec weak_aexpr = function
    | Ae_cst i -> true
    | Ae_var fa -> weak_arith_arg fa
    | Ae_plus (la, ra) -> weak_aexpr la && weak_aexpr ra in
  let weak_sexpr = function
    | Se_var sa -> if weak_set_arg sa then Some (Se_var sa, true) else None
    | Se_uplus (lsa, fa) ->
        if weak_arith_arg fa then
          Some (Se_uplus (lsa, fa), (List.for_all  weak_set_arg lsa))
        else None
    | Se_union (lsa, fa) ->
        if weak_arith_arg fa then
          Some (Se_union (lsa, fa), (List.for_all  weak_set_arg lsa))
        else None in
  let weak_aform = function
    | Af_equal (le, re)
    | Af_noteq (le, re)
    | Af_sup (le, re)
    | Af_supeq (le, re) -> weak_aexpr le && weak_aexpr re in
  let weak_sform sf =
    match sf with
    | Sf_mem (fa, sa) ->
        if weak_arith_arg fa && weak_set_arg sa then Some sf else None
    | Sf_empty sa ->
        if weak_set_arg sa then Some sf else None
    | Sf_equal (sa, se) ->
        if weak_set_arg sa then
          match weak_sexpr se with
          | None -> None
          | Some (se, true) -> Some (Sf_equal (sa, se))
          | Some (se, false) ->
              match se with
              | Se_union (_, fa) -> Some (Sf_mem (fa, sa))
              | Se_uplus (_, fa) -> Some (Sf_mem (fa, sa))
              | _ -> None
      else None in
  let f_rule (r: irule) =
    try
      let cons1 =
        List.find
          (function
            | Pf_arith (Af_equal (Ae_var `Fa_this, _))
            | Pf_arith (Af_equal (_, Ae_var `Fa_this))
            | Pf_arith (Af_noteq (_, Ae_var `Fa_this))
            | Pf_arith (Af_noteq (Ae_var `Fa_this, _)) -> true
            | _ -> false
          ) r.ir_pure in
      let cons =
        match cons1 with
        | Pf_arith (Af_equal (Ae_var `Fa_this, le)) ->
            Af_equal (Ae_var `Fa_this, le)
        | Pf_arith (Af_equal (re, Ae_var `Fa_this)) ->
            Af_equal (Ae_var `Fa_this, re)
        | Pf_arith (Af_noteq (re, Ae_var `Fa_this)) ->
            Af_noteq (Ae_var `Fa_this, re)
        | Pf_arith (Af_noteq (Ae_var `Fa_this, le)) ->
            Af_noteq (Ae_var `Fa_this, le)
        | _ -> Log.fatal_exn "ind_rules_cons: cons is not arith" in
      let cons_o =
        List.fold_left
          (fun (acca, accs) p ->
            match p with
            | Pf_set sf ->
                begin
                  match weak_sform sf with
                  | None -> acca, accs
                  | Some f -> acca, f :: accs
                end
            | Pf_arith pf ->
                if weak_aform pf && p <> cons1 then
                  pf :: acca, accs else acca, accs
            | _ -> acca, accs
          ) ([], []) r.ir_pure in
      Some (cons, cons_o)
    with Not_found -> None in
  let is_conflict cons_l cons_r =
    match cons_l, cons_r with
    | Af_equal (Ae_var `Fa_this, Ae_cst i),
      Af_equal (Ae_var `Fa_this, Ae_cst j) ->
        i<>j
    | Af_equal (Ae_var `Fa_this, le), Af_noteq (Ae_var `Fa_this, re) ->
        le = re
    | Af_noteq (Ae_var `Fa_this, le), Af_equal (Ae_var `Fa_this, re) ->
        le = re
    | Af_noteq (Ae_var `Fa_this, le), Af_noteq (Ae_var `Fa_this, re) ->
        false
    | _, _ -> false in
  let rec check_conflict rules_cons =
    match rules_cons with
    | [ ] -> true
    | (cons_h, _, _) :: tl ->
        if List.for_all (fun (cons_t, _, _) -> is_conflict cons_h cons_t) tl
        then
          check_conflict tl
        else false in
  let i_rule_cons, i_rules, b =
    List.fold_left
      (fun (acc, accr, b) r ->
        match f_rule r with
        | None -> acc, r :: accr, false
        | Some (af, (afl, sfl)) ->
            (af, afl, sfl) :: acc,
            { r with ir_cons = Some af } :: accr, b
      ) ([],[],true) ind.i_rules in
  if b && check_conflict i_rule_cons then
    { ind with
      i_rules = i_rules;
      i_rules_cons = i_rule_cons; }
  else ind

(** Computation of the guard condition of the empty rule,
 *  e.g.  this = null
 *  or    this = e *)
let emp_rule_cons (ind: ind): aform option =
  try
    let emp_rule = List.filter (fun r -> r.ir_kind = Ik_empz) ind.i_rules in
    if List.length emp_rule <> 1 then None
    else
      let emp_rule = List.hd emp_rule in
      emp_rule.ir_cons
  with Not_found -> None


(** Computation of weakening types for integer/set parameters *)

(* Collects all the occurrences of the i-th int of set parameters
 * as "new local names" (fails otherwise), from all the sub inductive calls *)
let linear_ic (fa: formal_arg) (hf: hform) (name: string): IntSet.t =
  let f_i_par (fa: formal_arg) (ic: indcall): int =
    match fa with
    | `Fa_par_int i ->
        begin
          match List.nth ic.ii_argi i with
          | `Fa_var_new n -> n
          | _ ->  raise Failure
        end
    | `Fa_par_set i ->
        begin
          match  List.nth ic.ii_args i with
          | `Fa_var_new n -> n
          | _ ->  raise Failure
        end
    | _ -> Log.fatal_exn "linear: improper arg" in
  List.fold_left
    (fun acc h ->
      match h with
      | Haind ic ->
          if ic.ii_ind = name then
            let n = f_i_par fa ic in
            if IntSet.mem n acc then raise Failure
            else IntSet.add n acc
          else acc
      | Hacell c -> acc
    ) IntSet.empty hf

(* Collect equality constraints over a set or integer parameters *)
let linear_cons (fa: formal_arg) (pure: pform): pformatom =
  let f (fa: formal_arg) (pf: pformatom): pformatom option =
    match fa, pf with
    | `Fa_par_int i, Pf_arith (Af_equal (al, ar)) ->
        if al = Ae_var (`Fa_par_int i) then
          Some (Pf_arith (Af_equal (al, ar)))
        else if ar = Ae_var (`Fa_par_int i) then
          Some (Pf_arith (Af_equal (ar, al)))
        else None
    | `Fa_par_set i, Pf_set (Sf_equal (al, ar)) ->
        if al = `Fa_par_set i then
          Some (Pf_set (Sf_equal (al, ar)))
        else if ar = Se_var (`Fa_par_set i) then
          Some (Pf_set (Sf_equal (`Fa_par_set i,  Se_var al)))
        else None
    | `Fa_par_set i, Pf_set (Sf_empty fa) ->
        if fa = `Fa_par_set i then Some (Pf_set (Sf_empty fa))
        else None
    | _ -> None in
  let fil_pure =
    List.fold_left
      (fun acc ele ->
        match f fa ele with
        | None -> acc
        | Some pf -> pf :: acc
      ) [] pure in
  if List.length fil_pure <> 1 then raise Failure
  else List.hd fil_pure

(* Check whether the i-th set parameter commutes with uplus or additive
 * with union *)
let wk_sadd_pform (i: int) (op: set_op) (hf: hform) (pure: pform)
    (name: string): bool =
  try
    let all_args = linear_ic (`Fa_par_set i) hf name in
    let pf = linear_cons (`Fa_par_set i) pure in
    let lin_lfs lfs set =
      List.fold_left
        (fun acc ele ->
          match ele with
          | `Fa_var_new i -> IntSet.add i acc
          | _ -> raise Failure
        ) set lfs in
    let f_sexpr ae acc =
      match ae with
      | Se_var (`Fa_var_new i) -> IntSet.add i acc
      | Se_uplus (al, ar) ->
          if op = Uplus then lin_lfs al acc else raise Failure
      | Se_union (al, ar) ->
          if op = Union then lin_lfs al acc else raise Failure
      | _ -> raise Failure in
    let f_sform sf =
      match sf with
      | Pf_set (Sf_equal (fs, se)) -> f_sexpr se IntSet.empty
      | Pf_set (Sf_empty fs) -> IntSet.empty
      | _ -> IntSet.empty in
    IntSet.subset all_args (f_sform pf)
  with
  | Failure -> false
  | Not_found -> false

(* Check whether the i-th int parameter is additive *)
let wk_add_pform (i: int) (hf: hform) (pure: pform) (name: string): bool =
  try
    let all_args = linear_ic (`Fa_par_int i) hf name in
    let pf = linear_cons (`Fa_par_int i) pure in
    let rec f_aexpr ae acc =
      match ae with
      | Ae_var (`Fa_var_new i) -> IntSet.add i acc
      | Ae_cst _ -> acc
      | Ae_plus (al, ar) -> f_aexpr ar (f_aexpr al acc)
      | _ -> raise Failure in
    let f_aform = function
      | Pf_arith (Af_equal (fs, se)) -> f_aexpr se IntSet.empty
      | _ -> IntSet.empty in
    IntSet.subset all_args (f_aform pf)
  with
  | Failure | Not_found -> false

(* check whether the i-th pointer parameter is eq or none
 * or check whether the i-th int parameter is eq, leq, geq or none
 * or check whether the i-th set parameter is  eq or none
 * (none means no such constraints for weakening) *)
let  wk_pform (i: formal_arg) (tp: wk_typ) (pure: pform) (heap: hform)
    (indname: string): bool =
  let do_formal_arg (i: formal_arg) (fa: formal_arg): bool =
    fa <> i in
  let do_formal_arith_arg (i: formal_arg) (fa: formal_arith_arg): bool =
    do_formal_arg i (fa :> formal_arg) in
  let do_formal_set_arg (i: formal_arg) (fa: formal_set_arg): bool =
    do_formal_arg i (fa :> formal_arg) in
  let rec do_aexpr (i: formal_arg) (ae: aexpr): bool =
    match ae with
    | Ae_cst _ -> true
    | Ae_var v -> do_formal_arith_arg i v
    | Ae_plus (ae0, ae1) -> do_aexpr i ae0 && do_aexpr i ae1 in
  let do_sexpr (i: formal_arg) (se: sexpr): bool=
    match se with
    | Se_var sa -> do_formal_set_arg i sa
    | Se_uplus (ls, ar) | Se_union (ls, ar) ->
        do_formal_arith_arg i ar && List.for_all (do_formal_set_arg i) ls in
  let do_aform (i: formal_arg) (af: aform): bool =
    match af with
    | Af_equal (al, ar)
    | Af_noteq (al, ar) -> (do_aexpr i al)&& (do_aexpr i ar)
    | Af_sup (al, ar)  | Af_supeq (al, ar)->
        begin
          match al, ar, tp with
          | Ae_var ag, _, `Leq ->
              (ag :> formal_arg) = i || do_aexpr i al && do_aexpr i ar
          | _, Ae_var ag, `Geq ->
              (ag :> formal_arg) = i || do_aexpr i al && do_aexpr i ar
          | _, _, _ -> do_aexpr i al && do_aexpr i ar
        end in
  let do_sform (i: formal_arg) (sf: sform): bool =
    match sf with
    | Sf_mem (ar, sr) ->
        do_formal_arith_arg i ar && do_formal_set_arg i sr
    | Sf_equal (sa, se) -> do_sexpr i se && do_formal_set_arg i sa
    | Sf_empty sa -> do_formal_set_arg i sa in
  let do_pformatom (i: formal_arg) (pf: pformatom): bool =
    match pf with
    | Pf_set sf -> do_sform i sf
    | Pf_arith af -> do_aform i af
    | _ -> true in
  let do_ic (fa: formal_arg) (hf: hform) (name: string): bool =
    let f_i_par (fa: formal_arg) (ic: indcall): bool =
      match fa with
      | `Fa_par_int i -> (List.nth ic.ii_argi i :> formal_arg) <> fa
      | `Fa_par_set i -> (List.nth ic.ii_args i :> formal_arg) <> fa
      | `Fa_par_ptr i -> (List.nth ic.ii_argp i :> formal_arg) <> fa
      | _ ->  Log.fatal_exn "do_ic: improper arg" in
    List.for_all
      (function
        | Haind ic -> if ic.ii_ind = name then f_i_par i ic else true
        | Hacell c -> true
      ) hf in
  List.for_all
    (fun p ->
      match tp with
      | `Eq -> true
      | _ -> do_pformatom i p && do_ic i heap indname
    ) pure

(* Compute weakening types for all the parameters of an inductive definition *)
let ind_rules_pars_wktyp (ind: ind): ind =
  let lptr_typs = [ `Eq; `Non ] in
  let lint_typs = [ `Eq; `Leq; `Geq; `Non ] in
  let lset_typs = [ `Eq; `Non ] in
  let emp_rules = List.filter (fun r -> r.ir_kind = Ik_empz) ind.i_rules in
  (* Compute weakening types (eq, non) for all the pointer parameters *
   * Compute weakening types (eq, leq, geq, non) for all the int parameters *
   * Compute weakening types (eq, non) for all the set parameters *)
  let rec f_wktyp (i: int) (f: int -> formal_arg)
      (ls: [< Ind_sig.wk_typ ] list) (m: [< Ind_sig.wk_typ ] IntMap.t)
      (rs: irule list): [< Ind_sig.wk_typ ] IntMap.t =
    if i < 0 then m
    else
      let fi = f i in
      let res =
        List.fold_left
          (fun acc t ->
            let t1 = (t :> wk_typ) in
            if List.for_all
                (fun r -> wk_pform fi t1 r.ir_pure r.ir_heap ind.i_name) rs then
              IntMap.add i t acc
            else acc
          ) m ls in
      f_wktyp (i-1) f ls res rs in
  (* Compute weakening types add for all the int parameters *)
  let f_wktyp_int_add (is: IntSet.t) (m: int_wk_typ IntMap.t)
      (rs: irule list): int_wk_typ IntMap.t =
    IntSet.fold
      (fun i acc ->
        if List.for_all
            (fun r -> wk_add_pform i r.ir_heap r.ir_pure ind.i_name) rs then
          IntMap.add i `Add m
        else m
      ) is m in
  (* Compute weakening types add (uplus, union) for all the set parameters *)
  let f_wktyp_set_add (is: IntSet.t) (m: set_wk_typ IntMap.t)
      (rs: irule list): set_wk_typ IntMap.t =
    IntSet.fold
      (fun i acc ->
        let f op =
          List.for_all
            (fun r -> wk_sadd_pform i op r.ir_heap r.ir_pure ind.i_name) rs in
        if f Uplus then IntMap.add i (`SAdd Uplus) m
        else if f Union then IntMap.add i (`SAdd Union) m
        else m
      ) is m in
  let init_wktyp (ind: ind)  (rs: irule list)=
    let f_ptr = fun i -> `Fa_par_ptr i in
    let f_int = fun i -> `Fa_par_int i in
    let f_set = fun i -> `Fa_par_set i in
    { ptr_typ = f_wktyp (ind.i_ppars-1) f_ptr lptr_typs IntMap.empty rs;
      int_typ = f_wktyp (ind.i_ipars-1) f_int lint_typs IntMap.empty rs;
      set_typ = f_wktyp (ind.i_spars-1) f_set lset_typs IntMap.empty rs; } in
  let pars_wktyp = init_wktyp ind ind.i_rules in
  let eq_index =
    IntMap.fold (fun i m acc -> if m = `Eq then IntSet.add i acc else acc)
      pars_wktyp.int_typ IntSet.empty in
  let seq_index =
    IntMap.fold (fun i m acc -> if m = `Eq then IntSet.add i acc else acc)
      pars_wktyp.set_typ IntSet.empty in
  (* only do additive type computing for "eq" type int and set parameters*)
  let pars_wktyp =
    { pars_wktyp with
      int_typ = f_wktyp_int_add eq_index pars_wktyp.int_typ ind.i_rules;
      set_typ = f_wktyp_set_add seq_index pars_wktyp.set_typ ind.i_rules } in
  (* if the inductive definition has emp rule, then, compute parameters type
   * only for empty rule *)
  let emp_pars_wktyp =
    if emp_rules = [ ] then pars_wktyp
    else init_wktyp ind emp_rules in
  let ind =
    { ind with
      i_pars_wktyp     = pars_wktyp;
      i_emp_pars_wktyp = emp_pars_wktyp} in
  ind


(** Checks whether an inductive definition resembles a list inductive def
 ** (this is used in order to feed data into the list domain) *)
let ind_list_check (ind: ind): ind =
  try
    (* there should be exactly two rules, and one should be empty *)
    if not ind.i_mt_rule then raise Failure;
    if List.length ind.i_rules != 2 then raise Failure;
    (* the non empty rule should define non ambiguous next offset and size *)
    let onext, osize =
      List.fold_left
        (fun ((on, os) as acc) r ->
          match r.ir_kind with
          | Ik_empz -> acc
          | Ik_range (omin, omax) ->
              (* - check the size of the block *)
              let nsize =
                match os with
                | None -> Some (omax - omin)
                | Some i -> if omax - omin = i then os else raise Failure in
              (* - compute the list of inductive calls; should be one
               *   and the map from new symbolic variables into offsets from
               *   this *)
              let indcalls, i_2off =
                List.fold_left
                  (fun (accl, accm) -> function
                    | Haind ic -> ic :: accl, accm
                    | Hacell ic ->
                        match Offs.to_int_opt ic.ic_off, ic.ic_dest with
                        | Some o, `Fa_var_new v -> accl, IntMap.add o v accm
                        | _, _ -> accl, accm
                  ) ([ ], IntMap.empty) r.ir_heap in
              (* - localization of a *single* next field *)
              begin
                match indcalls with
                | [ ] | _ :: _ :: _ -> raise Failure
                | [ icall ] ->
                    if String.compare icall.ii_ind ind.i_name = 0
                        && icall.ii_argp = [] && icall.ii_argi = []
                        && icall.ii_args = [] then
                      match icall.ii_maina with
                      | `Fa_var_new v ->
                          let nxt =
                            try IntMap.find v i_2off
                            with Not_found -> raise Failure in
                          if on = None || on = Some nxt then Some nxt, nsize
                          else raise Failure
                      | _ -> raise Failure
                    else raise Failure
              end
          | Ik_unk -> raise Failure
        ) (None, None) ind.i_rules in
    match onext, osize with
    | Some nxt, Some sz ->
        Log.info "Inductive %s identified as list(%d,%d)"
          ind.i_name nxt sz;
        { ind with i_list = Some (nxt, sz) }
    | None, _ | _, None -> raise Failure
  with Failure -> { ind with i_list = None }


(** Computation of access paths between pointer parameters *)
let ptr_path_computation (ind: ind): ind =
  try
    (* there should be exactly two rules, and one should be empty *)
    if not ind.i_mt_rule then raise Failure;
    if List.length ind.i_rules != 2 then raise Failure;
    (* empty rule and next rule *)
    let erule, nrule =
      List.find (fun r -> r.ir_kind = Ik_empz) ind.i_rules,
      List.find (fun r -> r.ir_kind <> Ik_empz) ind.i_rules in
    let rc_ptr =
      List.fold_left
        (fun acc ele ->
          match ele with
          | Haind ic ->
              if ic.ii_ind = ind.i_name && acc = None then
                Some ic.ii_argp
              else raise Failure;
          | _ -> acc
        ) None nrule.ir_heap in
    (* rename path predicate in empty rule *)
    let init_paths =
      List.fold_left
        (fun acc ele ->
          match ele with
          | Pf_path (`Fa_par_ptr i, Pe_epsilon, `Fa_par_ptr j) ->
              (List.nth (BatOption.get rc_ptr) i,
               List.nth (BatOption.get rc_ptr) j) :: acc
          | _ -> acc
        ) [] erule.ir_pure in
    (* replace new var by the euqual ptr from empty rule *)
    let replace_new sc =
      match sc with
      | `Fa_var_new i ->
          let fst, snd =
            List.find (fun (fst, snd) -> fst = sc || snd = sc) init_paths in
          if fst = sc then snd else fst
      | _ -> sc in
    let infer_paths =
      List.fold_left
        (fun acc ele ->
          match ele with
          | Pf_path (`Fa_var_new i , Pe_single ofs, dt) ->
              (replace_new (`Fa_var_new i), Pe_seg ofs, dt) :: acc
          | _ -> acc
        ) [] nrule.ir_pure in
    { ind with i_ppath = infer_paths }
  with
  | Failure -> ind
  | Not_found -> ind
  | Invalid_argument _ -> ind

(* Collect SETVs in rules *)
let ind_setvar_compute (ind: ind): ind =
  let do_rule r =
    List.fold_left
      (fun (accs, accn) h ->
        match h with
        | Hacell _ -> accs, accn
        | Haind ic ->
          List.fold_left
            (fun acc a->
               match a with
               | `Fa_var_new i -> IntSet.add i acc
               | `Fa_par_set _ -> acc
            ) accs ic.ii_args,
          List.fold_left
            (fun acc a->
               match a with
               | `Fa_var_new i -> IntSet.add i acc
               | `Fa_par_int _ -> acc
            ) accn ic.ii_argi
      ) (IntSet.empty, IntSet.empty) r.ir_heap in
  let irules =
    List.map
      (fun ele -> let svars, nvars = do_rule ele in
        { ele with ir_snum = svars;
                   ir_nnum = nvars })
      ind.i_rules in
  let isrules =
    List.map
      (fun ele -> let svars, nvars = do_rule ele in
        { ele with ir_snum = svars;
                   ir_nnum = nvars })
      ind.i_srules in
  { ind with
    i_rules  = irules;
    i_srules = isrules; }


(** Set of inductive definitions *)
let ind_defs: ind StringMap.t ref = ref StringMap.empty
let ind_bind: string StringMap.t ref = ref StringMap.empty
let ind_prec: string list ref = ref [ ]

(* Initialization from parsing *)
let ind_init (l: p_iline list): unit =
  List.iter
    (function
      | Piind ind ->
          let name = ind.i_name in
          assert (not (StringMap.mem name !ind_defs));
          Log.info "";
          (* verification of the rules (temporary, to fix other issues) *)
          List.iter
            (fun r ->
              if IntMap.cardinal r.ir_typ != r.ir_num then
                Log.warn "incorrect rule in %s" ind.i_name;
            ) ind.i_rules;
          (* compute the parameters used by each rule *)
          let ind = indpar_use_analysis ind in
          (* make the proper node associations, hint generations *)
          let ind = inddir_analysis (indnodes_analysis ind) in
          (* flag whether there is an "empty heap + null ptr" rule *)
          let ind = empty_heap_rule_analysis ind in
          (* flag whether there is an "empty heap + int param" rule *)
          let ind = empty_heap_iparam_rule_analysis ind in
          (* flag parameters that may denote prev pointers *)
          let ind = bwdpar_analysis ind in
          (* FOR XAR: flag parameters MUST denote prev pointers *)
          let ind =
            let n = Offs.OffSet.union ind.i_may_self_dirs ind.i_pr_offs in
            { ind with i_may_self_dirs = n } in
          (* flag some rules as "full inductive edges only"
           * (should not be used at all for segments) *)
          let ind = ind_calc_segrules ind in
          (* analyze fields corresponding to pointer parameters *)
          let ind = ind_field_pars ind in
          (* computing rules kinds *)
          let ind = ind_rules_kind ind in
          (* check whether it resembles a list inductive definition *)
          let ind = ind_list_check ind in
          (* computing new set variables in each rule *)
          let ind = ind_setvar_compute ind in
          (* comoute i_rules_cons *)
          let ind = ind_rules_cons ind in
          (* analyze behavior of parameters *)
          let ind = ind_rules_pars_wktyp ind in
          let ind =
            if !Flags.flag_indpars_analysis then indpars_analysis ind
            else ind in
          let ind =  ptr_path_computation ind in
          ind_defs := StringMap.add name ind !ind_defs;
          Log.info "Inductive %s; mt result: %b\n%s"
            ind.i_name ind.i_mt_rule (ind_2str ind);
      | Pibind (tname, iname) ->
          assert (not (StringMap.mem tname !ind_bind));
          ind_bind := StringMap.add tname iname !ind_bind
      | Piprec l ->
          assert (!ind_prec = [ ]);
          ind_prec := l
    ) l

(* Extraction of an inductive *)
let ind_find (indname: string): ind =
  try StringMap.find indname !ind_defs
  with Not_found ->
    Log.fatal_exn "inductive %s not_found; map size: %d"
      indname (StringMap.cardinal !ind_defs)

(* Retrieve an inductive name from type *)
let indname_find (tname: string): string =
  try StringMap.find tname !ind_bind
  with Not_found -> Log.fatal_exn "type %s: no inductive found" tname
