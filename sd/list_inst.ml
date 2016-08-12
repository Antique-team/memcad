(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_inst.ml
 **       Instantiation of set parameters for the list domain join
 ** Xavier Rival, 2015/07/16 *)
open Data_structures
open Lib

open Inst_sig
open List_sig
open Set_sig

open Inst_utils
open Set_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "l_ins___" and level = Log_level.DEBUG end)


(** Initialization of instantiation *)
let l_call_empty (lc: l_call) (inst: setv_inst): setv_inst =
  let args = 
    match lc.lc_def.ld_set with
    | None -> [ ]
    | Some e -> e.s_params in
  try
    List.fold_left2
      (fun inst l kind ->
        let inst = Inst_utils.add_setv l inst in
        (* If a parameter is "monotone", then we can fix it to be anything,
         * it will always work for the empty segment *)
        if kind.st_add || kind.st_head then
          setv_inst_bind l S_empty inst
        else if kind.st_mono then
          setv_inst_nobind l inst
        else Log.todo_exn "unhandled kind"
      ) inst lc.lc_args args
  with Not_found -> Log.fatal_exn "l_call_empty: set parameters not match"


(** Handling unresolved set constraints from is_le *)
let do_setconses
    (findkind: int -> set_par_type option) (* Extraction of SETV types *)
    (lc_comp: l_call)            (* Call used for the comparison *)
    (lc_out:  l_call)            (* Call produced in the output *)
    (svmap:   int IntMap.t)      (* Is_le mapping for symbolic variables *)
    (setvmap: IntSet.t IntMap.t) (* Is_le mapping for set parameters *)
    (sc: set_cons list)          (* Constraints to process *)
    (inst: setv_inst)            (* Previous instantiation *)
    : setv_inst =
  let loc_debug = false in
  if loc_debug then
    Log.info "do_setconses: status before:\n%s"
      (setv_inst_2stri "  " inst);
  let sv_rename i = IntMap.find_err "sv renaming" i svmap in
  let setv_rename i =
    try IntSet.min_elt (IntMap.find i setvmap)
    with Not_found -> Log.fatal_exn "setv renaming" in
  let inst =
    List.fold_left (fun acc i -> Inst_utils.add_setv i acc)
      inst lc_out.lc_args in
  (* set indexes that are generated *)
  let call_vars =
    List.fold_left2 (fun acc iw io -> IntMap.add iw io acc)
      IntMap.empty lc_comp.lc_args lc_out.lc_args in
  let setv_output i = IntMap.find_err "do_setconses:mapping" i call_vars in
  (* index the set indexes that are not mapped *)
  let set_unmapped =
    let rec aux_set_expr s = function
      | S_empty -> s
      | S_var i -> if IntMap.mem i setvmap then s else IntSet.add i s
      | S_node _ -> s
      | S_uplus (e0, e1) | S_union (e0, e1) ->
          aux_set_expr (aux_set_expr s e0) e1 in
    let aux_set_cons s = function
      | S_eq (e0, e1) | S_subset (e0, e1) ->
          aux_set_expr (aux_set_expr s e0) e1
      | S_mem (_, e0) -> aux_set_expr s e0 in
    List.fold_left aux_set_cons IntSet.empty sc in
  (* Inspection functions *)
  let setv_is_unmapped (i: int): bool = IntSet.mem i set_unmapped in
  let setv_is_mapped (i: int): bool = not (setv_is_unmapped i) in
  let setv_is_call (i: int): bool = IntMap.mem i call_vars in
  let inspect_setv (i: int): bool * bool =
    let is_call = setv_is_call i in
    let is_unmapped = setv_is_unmapped i in
    if loc_debug then
      Log.info "    %d: %s-%s" i
        (if is_call then "parameter:t" else "generated:f")
        (if is_unmapped then "unmapped:t" else "mapped:f");
    is_call, is_unmapped in
  let rec inspect_set_expr = function
    | S_empty | S_node _ -> ( )
    | S_var i -> ignore (inspect_setv i)
    | S_uplus (e0, e1) | S_union (e0, e1) ->
        inspect_set_expr e0; inspect_set_expr e1 in
  let inspect_set_cons = function
    | S_mem (_, e0) -> inspect_set_expr e0
    | S_eq (e0, e1) -> inspect_set_expr e0; inspect_set_expr e1
    | S_subset (_, e0) -> inspect_set_expr e0 in
  (* Adding constraints over a setv *)
  let add_ctr i c acc =
    if loc_debug then Log.info "    +cons on %d" i;
    if IntMap.mem i acc then Log.fatal_exn "already a constraint on %d" i
    else IntMap.add i c acc in
  (* First, we process the constraints in several phases *)
  (* Phase 0. Inspect all the variables used and print constraints *)
  if loc_debug then
    begin
      List.iter
        (fun c -> Log.info "Do_setconses,Ph-0: %s" (set_cons_2str c)) sc;
      List.iter (fun c -> ignore (inspect_set_cons c)) sc;
    end;
  (* Phase 1. Search for sets equal to empty, and simplify them away *)
  let remain, ctrs =
    List.fold_left
      (fun (acc_remain, acc_ctr) c ->
        if loc_debug then
          Log.info "Do_setconses,Phase-1: %s" (set_cons_2str c);
        match c with
        | S_eq (S_var i, S_empty) | S_eq (S_empty, S_var i) ->
            if inspect_setv i = (false, true) then
              acc_remain, add_ctr i `Is_empty acc_ctr
            else c :: acc_remain, acc_ctr
        | _ -> c :: acc_remain, acc_ctr
      ) ([ ], IntMap.empty) sc in
  let remain =
    let aux_setv i =
      try if IntMap.find i ctrs = `Is_empty then S_empty else S_var i
      with Not_found -> S_var i in
    List.map (transform_cons aux_setv) remain in
  (* Phase 2. Search the singletons and make a table of equalities
   *          among SetVs
   *  - simplify singletons
   *  - simplify and put aside constraints all variables of which are
   *    resolved *)
  let remain, equalities, proofs =
    let remain, ctrs, uf, eqcl =
      (* computes a union find to describe equalities, and a set of equality
       *  classes *)
      List.fold_left
        (fun (acc_remain, acc_ctr, uf, eqcl) c ->
          if loc_debug then
            Log.info "Do_setconses,Phase-2: %s" (set_cons_2str c);
          match c with
          | S_eq (S_var i, S_node j) | S_eq (S_node j, S_var i) ->
              if inspect_setv i = (false, true) (* generated, unmapped *) then
                acc_remain, add_ctr i (`Is_singleton j) acc_ctr, uf, eqcl
              else c :: acc_remain, acc_ctr, uf, eqcl
          | S_eq (S_var i, S_var j) ->
              let uf = if Union_find.mem i uf then uf else Union_find.add i uf in
              let uf = if Union_find.mem j uf then uf else Union_find.add j uf in
              let ii, uf = Union_find.find i uf in
              let jj, uf = Union_find.find j uf in
              let uf = Union_find.union ii jj uf in
              acc_remain, acc_ctr, uf, IntSet.add ii (IntSet.remove jj eqcl)
          | _ -> c :: acc_remain, acc_ctr, uf, eqcl
        ) ([ ], ctrs, Union_find.empty, IntSet.empty) remain in
    let renamer, equalities, proofs =
      (* for each equality class, decide to which SetV to rename it,
       * rename free SetVs and extend proof obligations for non free SetVs *)
      IntSet.fold
        (fun ii (accr, acce, accp) ->
          let cii = Union_find.find_class ii uf in
          let rename_class_to cpar =
            List.fold_left
              (fun accr v -> if v = cpar then accr else IntMap.add v cpar accr)
              accr cii in
          let call = List.filter setv_is_call cii in
          let mapped = List.filter setv_is_mapped cii in
          (* TODO:
           *  - when a mapping exists: USE IT to resolve variable
           *  - when no mapping exists: resolve equalities (done)
           *  - when several mapping exist: we need to prove it no ? *)
          let tgt_name =
            match call with
            | [ ] -> Log.fatal_exn "do_setconses: no setv from call"
            | [ cpar ] -> cpar
            | _ -> Log.todo_exn "do_setconses rename equalities, several choices" in
          let f_list l =
            let s = List.fold_left (fun a x -> IntSet.add x a) IntSet.empty l in
            intset_2str s in
          if loc_debug then
            begin
              Log.info "class of %d: %s => %d\n - mapped:%s\n - call: %s"
                ii (f_list cii) tgt_name (f_list mapped) (f_list call);
              List.iter
                (fun x -> Log.info "  map: %d=>%d" x (setv_rename x))
                mapped;
            end;
          let acce =
            match mapped with
            | [ ] -> acce
            | x :: _ -> IntMap.add tgt_name (setv_rename x) acce in
          let proofs =
            let rec aux l =
              match l with
              | [ ] | [ _ ] -> [ ]
              | a :: (b :: c as d) ->
                  S_eq (S_var (setv_rename a), S_var (setv_rename b)) :: aux d in
            aux mapped in
          rename_class_to tgt_name, acce, proofs @ accp
        ) eqcl (IntMap.empty, IntMap.empty, [ ]) in
    let aux_setv i =
      try
        match IntMap.find i ctrs with
        | `Is_singleton k -> S_node k
        | _ -> S_var i
      with Not_found -> S_var (IntMap.find_val i i renamer) in
    List.map (transform_cons aux_setv) remain, equalities, proofs in
  (* Phase 3. Search for membership constraints, that can guide instantiation *)
  (*          and collect equalities of the form SetV=expr, where expr is not
   *          empty, a singleton, or a SetV, and then simplify them *)
  let remain, ctrs =
    let remain, ctrs, defs =
      List.fold_left
        (fun (acc_remain, acc_ctr, acc_defs) c ->
          if loc_debug then
            Log.info "Do_setconses,Phase-3: %s" (set_cons_2str c);
          match c with
          | S_eq (S_var i, e) ->
              if setv_is_call i then c :: acc_remain, acc_ctr, acc_defs
              else
                let b =
                  IntSet.fold (fun i a -> a && setv_is_mapped i)
                    (set_expr_setvs e) true in
                if b then acc_remain, acc_ctr, IntMap.add i e acc_defs
                else c :: acc_remain, acc_ctr, acc_defs
          | S_mem (i, S_var j) ->
              if setv_is_call j then
                acc_remain, add_ctr j (`Has_elt i) acc_ctr, acc_defs
              else
                begin
                  Log.warn "dropping complex, unhandled membership constraint";
                  acc_remain, acc_ctr, acc_defs
                end
          | _ -> Log.todo_exn "unhandled set constraint (0)"
        ) ([ ], ctrs, IntMap.empty) remain in
    let aux_setv i = IntMap.find_val (S_var i) i defs in
    List.map (transform_cons aux_setv) remain, ctrs in
  (* Now, build the result from the accumulated constraints *)
  (* - check empty *)
  let is_empty i = try IntMap.find i ctrs = `Is_empty with Not_found -> false in
  (* 1. simplify linear equalities with an empty member *)
  let res =
    List.fold_left
      (fun acc c ->
        if loc_debug then
          Log.info "Do_setconses,Phase-res-1: %s" (set_cons_2str c);
        match c with
        | S_eq (S_var i, S_uplus (S_node j, S_var k))
        | S_eq (S_var i, S_uplus (S_var k, S_node j)) ->
            if is_empty k then
              Log.todo_exn "untransformed, empty"
            else if setv_is_unmapped i && setv_is_call i && setv_is_mapped k then
              setv_inst_bind (setv_output i)
                (S_uplus (S_node (sv_rename j), S_var (setv_rename k))) acc
            else (* still left to do *)
              begin
                Log.warn "may be unmapped: %d, dropping" i;
                acc
              end
        | S_eq (S_var i, S_uplus (S_var j, S_var k)) ->
            if setv_is_unmapped i && setv_is_call i
                && setv_is_mapped j && setv_is_mapped k then
              setv_inst_bind (setv_output i)
                (S_uplus (S_var (setv_rename j), S_var (setv_rename k))) acc
            else
              begin
                Log.warn "ernaming issue";
                acc
              end
        | S_eq (S_var i, S_node j) ->
            if setv_is_call i then
              setv_inst_bind (setv_output i) (S_node (sv_rename j)) acc
            else (* to a renaming on i *)
              Log.todo_exn "rename i"
        | S_eq (S_var i, e) ->
            if setv_is_call i then
              let e =
                try s_expr_map sv_rename setv_rename e
                with Not_found -> Log.fatal_exn "renaming failed" in
              setv_inst_bind (setv_output i) e acc
            else Log.fatal_exn "renaming unbound"
        | _ ->
            Log.todo_exn "unhandled set constraint (2)"
      ) { inst with setvi_prove = proofs @ inst.setvi_prove } remain in
  (* 2. when the only constraints about a set S are of the form x \in S,
   *    let S = { x } *)
  let res =
    IntMap.fold
      (fun i ctr acc ->
        match ctr with
        | `Is_empty -> acc
        | `Is_renamed j ->
            if loc_debug then Log.info "Adding renamed: %d, %d" i j;
            Log.todo_exn "do_sc:3"
        | `Is_singleton _ -> acc
        | `Has_elt j -> (* means x is only specified as having x as element *)
            setv_inst_guess (setv_output i) (sv_rename j) acc
      ) ctrs res in
  (* 3. when an equality x => y has been found as well as x contains z,
   *    keep x => y, and move property "x contains z" in the to check pile *)
  let res =
    IntMap.fold
      (fun i j acc ->
        let outi = setv_output i in
        if loc_debug then
          Log.info "Mapping %d [%d] to %d" i outi j;
        if IntMap.mem outi acc.setvi_guess then
          let c = IntMap.find_err "inst-0" outi acc.setvi_guess in
          let cons = (S_mem (c, S_var j)) in
          setv_inst_bind outi (S_var j)
            { acc with
              setvi_guess = IntMap.remove outi acc.setvi_guess;
              setvi_prove = cons :: acc.setvi_prove }
        else setv_inst_bind outi (S_var j) acc
      ) equalities res in
  (* 4. mark any other setv related to this call as unbound *)
  let inst =
    IntMap.fold
      (fun i j acc ->
        if loc_debug then
          Log.info "No spec on %d:%d" i j;
        if setv_inst_free j acc then
          { acc with setvi_none = IntSet.add j acc.setvi_none }
        else acc
      ) call_vars res in
  (* Parameters that are mapped in is_le can be immediately added to the
   * instantiation (no resolution needed) *)
  let inst =
    IntMap.fold
      (fun i s acc ->
        if loc_debug then
          Log.info "considering: %d [%b]" i (setv_is_call i);
        if setv_is_call i then
          begin
            let j = IntMap.find_err "inst-1" i call_vars in
            if loc_debug then
              Log.info "parameter mapped : %d => %s" j (intset_2str s);
            if IntSet.mem j acc.setvi_none then
              begin
                if IntSet.cardinal s > 1 then Log.fatal_exn "mapping";
                setv_inst_over_bind j (S_var (IntSet.min_elt s)) acc
              end
            else acc
          end
        else acc
      ) setvmap inst in
  if loc_debug then
    Log.info "processed ctrs:\n%s" (setv_inst_2stri "  " inst);
  inst
