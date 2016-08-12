(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_ind_infer.ml
 **       inference of inductive definitions from C type definitions
 ** Xavier Rival, 2013/01/05 *)
open Data_structures
open Lib
open Offs

open C_sig
open Ind_sig
open Sv_sig

open C_utils


(** Error report *)
module Log =
  Logger.Make(struct let section = "i_inf___" and level = Log_level.DEBUG end)

(* Local debug flag *)
let local_debug = false


(** Utilities for the generation of fields *)
(* A local flattening function
 *  the first parameter stands for lengths, and should be the same over
 *  all elements of the structure *)
let flatten_list_rulesl (l: (int * irule list) list): int * irule list =
  match l with
  | [ ] -> Log.fatal_exn "empty list arises in do_fields"
  | [ b0, r0 ] -> b0, r0
  | (b0, r0) :: l0 ->
      List.fold_left
        (fun (ba, la) (bc, lc) ->
          if bc = ba then ba, lc @ la
          else Log.fatal_exn "incoherent field lengths %d %d" bc ba
        ) (b0, r0) l0
let flatten_list_rulesr (l: (int * irule) list): int * irule list =
  flatten_list_rulesl (List.map (fun (b, r) -> b, [ r ]) l)
(* Addition of a cell to a rule *)
let add_cellv (typ, off, sz) (rule: irule): irule * int =
  let new_var = rule.ir_num in
  let cell = Hacell { ic_off  = Offs.of_int off;
                      ic_size = sz;
                      ic_dest = `Fa_var_new new_var } in
  { rule with
    ir_num  = new_var + 1 ;
    ir_typ  = IntMap.add new_var typ rule.ir_typ;
    ir_heap = cell :: rule.ir_heap }, new_var
let add_cell (typ, off, sz) (rule: irule): irule =
  fst (add_cellv (typ, off, sz) rule)
(* Padding addition, if needed, to complete a structure to a point *)
let add_padding (target: int) ((base, rule): int * irule): int * irule =
  if base = target then target, rule
  else target, add_cell (Ntraw, base, target - base) rule

(** Generation of fields *)
(* Collection functions *)
let rec do_fields ((base, rule): int * irule)
    (fields: c_agg_field list): int * irule list =
  List.fold_left
    (fun (base, rules) fld ->
      flatten_list_rulesl (List.map (fun r -> do_field (base, r) fld) rules)
    ) (base, [ rule ]) fields
and do_field ((base, rule): int * irule) (fld: c_agg_field)
    : int * irule list =
  let t = fld.caf_typ and off = fld.caf_off in
  Log.info "field %s @%d" fld.caf_name off;
  let size = c_type_sizeof t in
  (* add padding if needed *)
  let base, rule = add_padding off (base, rule) in
  (* treat corresponding type *)
  match t with
  | Ctchar -> off + size, [ add_cell (Ntint, off, 1) rule ]
  | Ctint  -> off + size, [ add_cell (Ntint, off, 4) rule ]
  | Ctptr (Some tu) ->
      let nbase = off + size in
      let rule, var = add_cellv (Ntaddr, off, Flags.abi_ptr_size) rule in
      let rule =
        match tu with
        | Ctnamed n ->
            let hatom = Haind { ii_maina = `Fa_var_new var;
                                ii_ind   = n.cnt_name;
                                ii_argp  = [ ];
                                ii_argi  = [ ];
                                ii_args  = [ ] } in
            { rule with ir_heap = hatom :: rule.ir_heap }
        | _ -> rule in
      nbase, [ rule ]
  | Ctunion (Cad_def u) ->
      (* recomputation of the offsets inside the union *)
      let fields =
        List.map (fun fld -> { fld with caf_off = off }) u.cag_fields in
      (* recursive treatment *)
      let l =
        List.map
          (fun field ->
            let b, l = do_field (base, rule) field in
            let l =
              List.map (fun r -> add_padding (off + u.cag_size) (b, r)) l in
            flatten_list_rulesr l
          ) fields in
      flatten_list_rulesl l
  | Ctstruct (Cad_def s) ->
      (* recomputation of the offsets inside the structure *)
      let fields =
        List.map
          (fun fld -> { fld with caf_off = fld.caf_off + off }) s.cag_fields in
      (* recursive treatment *)
      do_fields (base, rule) fields
  | _ -> Log.todo_exn "other type in do_field: %s" (c_type_2str t)
let extract_fields (s: c_aggregate): irule list =
  let size = s.cag_size
  and nonnull = Af_noteq (Ae_var `Fa_this, Ae_cst 0) in
  let n, rl =
    do_fields (0, { ir_num   = 0;
                    ir_typ   = IntMap.empty;
                    ir_heap  = [];
                    ir_pure  = [ Pf_alloc size; Pf_arith nonnull ];
                    ir_kind  = Ik_range (0, size);
                    ir_uptr  = IntSet.empty;
                    ir_uint  = IntSet.empty;
                    ir_uset  = IntSet.empty;
                    ir_unone = true } ) s.cag_fields in
  Log.info "final: %d-%d" n size;
  assert (n = size);
  List.flatten
    (List.map (fun x -> [ { x with ir_heap = List.rev x.ir_heap } ]) rl)

(** Inference function *)
(* Reads all typedefs, and try to propose inductive definitions for
 * them, assuming:
 *   - all inductives have a "0" case, with empty memory
 *   - all inductives have no parameter
 *   - all inductives correspond to list, trees and the like
 *)
let compute_inductives (p: c_prog): ind list =
  let l = ref [ ] in
  StringMap.iter
    (fun n t ->
      (* Try to build an inductive for structures *)
      if local_debug then Log.info "examining type %s: " n;
      match t with
      | Ctint | Ctchar | Ctvoid | Ctarray _ | Ctstring _ ->
          if local_debug then Log.info "base type or array"
      | Ctptr _ -> (* later: chain ? *)
          if local_debug then Log.info "ptr type"
      | Ctnamed _ -> (* later: chain ? *)
          if local_debug then Log.info "named type"
      | Ctstruct (Cad_def s) ->
          (* walk through fields *)
          if local_debug then
            Log.info "struct [%d,%d]" s.cag_size s.cag_align;
          let rules = extract_fields s in
          (* Creates a (constant) rule 0, assuming structures may be empty *)
          let rule0 =
            let null = Af_equal (Ae_var `Fa_this, Ae_cst 0) in
            { ir_num   = 0;
              ir_typ   = IntMap.empty;
              ir_heap  = [];
              ir_pure  = [ Pf_arith null ];
              ir_kind  = Ik_empz;
              ir_uptr  = IntSet.empty;
              ir_uint  = IntSet.empty;
              ir_uset  = IntSet.empty;
              ir_unone = true } in
          (* compute rules for the body of the structure:
           *  - if there are union fields, one rule per combination
           *  - otherwise only one rule for the body of the union;
           *  - always add a rule for the empty case (null pointer) *)
          let ind =
            (* not fully elaborated inductive, will be used only for pp *)
            { i_name    = n;
              i_ppars   = 0;
              i_ipars   = 0;
              i_spars   = 0;
              i_rules   = rule0 :: (List.rev rules);
              i_srules  = [];
              i_mt_rule = true;
              i_emp_ipar = -1;
              i_reds0   = true;
              i_dirs    = OffSet.empty;
              i_may_self_dirs = OffSet.empty;
              i_pr_pars = IntSet.empty;
              i_fl_pars = IntMap.empty;
              i_pr_offs = OffSet.empty;
              i_list    = None;
              i_pkind   = Ind_utils.pars_rec_top; } in
          l := ind :: !l
      | Ctstruct (Cad_named _) ->
          if local_debug then Log.info "named struct"
      | Ctunion _ ->
          if local_debug then Log.info "union type"
    ) p.cp_types;
  !l

(** Compatibility checking *)
exception Incompat of string
(* checks whether an inductive definition is compatible with a type
 * according to the types of the fields *)
let test_compat_ind (t: c_type) (i: ind): bool =
  let rec extract_named = function
    | Ctnamed tn -> extract_named tn.cnt_type
    | t -> t in
  let rec extract_ptr = function
    | Ctptr (Some tp) -> tp
    | _ -> raise (Incompat "not a pointer type") in
  let rec aux_fields ((base,typs): int * (ntyp * int) IntMap.t)
      (fields: c_agg_field list): int * (ntyp * int) IntMap.t =
    List.fold_left aux_field (base, typs) fields
  and aux_field ((base,typs): int * (ntyp * int) IntMap.t)
      (field: c_agg_field): int * (ntyp * int) IntMap.t =
    let treat_base (nt: ntyp): int * (ntyp * int) IntMap.t =
      let it, isz =
        try IntMap.find base typs
        with Not_found ->
          raise (Incompat (Printf.sprintf "no field in inductive (%d)" base)) in
      let typs = IntMap.remove base typs in
      if it != nt then raise (Incompat "inconsistent types");
      if isz != field.caf_size then raise (Incompat "inconsistent sizes");
      base + isz, typs in
    let rec f_typ tp =
      match tp with
      | Ctint -> treat_base Ntint
      | Ctptr _ -> treat_base Ntaddr
      | Ctnamed tn -> f_typ tn.cnt_type
      | Ctunion tu ->
          (* unions are hard to handle:
           *  we need to check that for each rule there exists a union field
           *  that matches, so we should branch here, which the return type
           *  of aux_field currently does not allow *)
          Log.todo_exn "test_compat_ind: union"
      | Ctstruct (Cad_def ts) -> aux_fields (base, typs) ts.cag_fields
      | _ -> Log.todo_exn "test_compat_ind: visit" in
    f_typ field.caf_typ in
  try
    let aggr =
      match extract_named (extract_ptr (extract_named t)) with
      | Ctstruct (Cad_def st) -> st.cag_fields
      | _ -> raise (Incompat "not an aggregate") in
    (* check whether all the rules are compatible *)
    List.iter
      (fun rule ->
        (* consider only non empty rules
         *  (since we are considering pointer types, empty rules normally
         *   correspond to the null pointer) *)
        if rule.ir_kind != Ik_empz then
          (* extract the layout of the block that is described in the rule
           * body and discard the underlying pointers *)
          let fields =
            List.fold_left
              (fun acc -> function
                | Hacell c ->
                    let n =
                      match Offs.to_int_opt c.ic_off with
                      | None -> Log.fatal_exn "test_compat_ind: symbolic offset"
                      | Some i -> i in
                    let t =
                      match c.ic_dest with
                      | `Fa_this
                      | `Fa_par_ptr _ -> Ntaddr (* pointer *)
                      | `Fa_par_int _ -> Ntint (* int *)
                      | `Fa_var_new i -> IntMap.find i rule.ir_typ in
                    IntMap.add n (t, c.ic_size) acc
                | Haind _ -> acc
              ) IntMap.empty rule.ir_heap in
          let _, m = aux_fields (0, fields) aggr in
          if m != IntMap.empty then raise (Incompat "not all fields visited")
      ) i.i_rules;
    true
  with
  | Incompat s -> false
