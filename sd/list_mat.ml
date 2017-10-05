(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_mat.ml
 **       materialization support for the list abstract domain
 ** Xavier Rival, 2014/03/02 *)
open Lib
open Data_structures

open Graph_sig
open Ind_sig
open List_sig
open Nd_sig
open Set_sig
open Sv_sig

open List_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "l_mat___" and level = Log_level.DEBUG end)

let debug_module = true

(** Unfolding primitive *)
let unfold (i: int) (only_non_emp: bool) (lm: lmem): unfold_result list =
  (* Computation of the set of setv to remove *)
  let setv_to_remove (lc: l_call) (lm: lmem): IntSet.t =
    List.fold_left
      (fun acc i ->
        if setv_is_root lm i then acc
        else IntSet.add i acc
      ) IntSet.empty lc.lc_args in
  (* Creation of a single points-to edge at origin point *)
  let create_pt (nt: ntyp) (off: int) (size: int) (x: lmem): int * lmem =
    let j, x = sv_add_fresh nt x in
    let bn = i, Bounds.of_int off in
    let pe = { pe_size = Offs.size_of_int size;
               pe_dest = j, Offs.zero } in
    j, pt_edge_block_append ~nochk:true bn pe x in
  (* Add the pointer edges and prepare for the inductive edges *)
  (*  returns:
   *   - mapping of offsets to svs
   *   - list of new calls
   *   - new memory state
   *   - setv kinds *)
  let create_ld_block (actual: sid list) (ld: l_def) (lm: lmem)
      : int IntMap.t * (int * l_call) list * lmem * set_par_type IntMap.t =
    (* Create real set argument for l_call *)
    (*  returns:
     *   - reversed list of arguments
     *   - new memory state
     *   - setv kinds *)
    let gen_real_setpar (lm: lmem) (ds: seti option)
        (nsetvs: set_par_type IntMap.t)
        : (sid list) * lmem * set_par_type IntMap.t =
      match ds with
      | None -> [ ], lm, nsetvs
      | Some sel ->
          let params, lm, nsetvs, _ =
            List.fold_left
              (fun (acc, lm, nsetvs, i) skind ->
                let setv, lm = setv_add_fresh false (Some skind) lm in
                if debug_module then
                  Log.debug "freshly generated var: %d" setv;
                setv :: acc, lm, IntMap.add setv skind nsetvs, i + 1
              ) ([ ], lm, nsetvs, 0) (List.rev sel.s_params) in
          params, lm, nsetvs in
    (* - off_2nid map from offset to new creat nid, at first it is empty
     * - lind_edges store the list information need be add
     * - create a pointer edge the destination node of which
     *   should carry the list inductive *)
    let add_pt_edge (off: int) (ldd: l_def) (lm: lmem)
        (nsetvs: set_par_type IntMap.t)
        : (int * int) * (int * l_call) * lmem * set_par_type IntMap.t =
      let n_id, lm = create_pt Ntaddr off Flags.abi_ptr_size lm in
      let args, lm, nsetvs = gen_real_setpar lm ldd.ld_set nsetvs in
      (off, n_id), (n_id, { lc_def = ldd; lc_args = args }), lm, nsetvs in
    (* - creation of all pointer edges according to the order of offset *)
    let lm, off_2nid =
      if ld.ld_nextoff = 0 then lm, IntMap.empty
      else
        let j, lm = create_pt Ntraw 0 ld.ld_nextoff lm in
        lm, IntMap.add 0 j IntMap.empty in
    let off_2nid, lind_edges, lm, nsetvs =
      List.fold_left
        (fun (off_2nid, lind_edges, lm, nsetvs) (off, ldd) ->
          let (o, n1), x, lm, nsetvs = add_pt_edge off ldd lm nsetvs in
          IntMap.add o n1 off_2nid, (x :: lind_edges), lm, nsetvs
        ) (off_2nid, [ ], lm, IntMap.empty)
        ((ld.ld_nextoff, ld) :: ld.ld_onexts) in
    let lm, off_2nid =
      let off =
        Flags.abi_ptr_size * (List.length ld.ld_onexts + 1) + ld.ld_nextoff in
      if off < ld.ld_size then
        let j, lm = create_pt Ntraw off (ld.ld_size-off) lm in
        lm, IntMap.add off j off_2nid
      else lm, off_2nid in
    off_2nid, List.rev lind_edges, lm, nsetvs in
  (* - add the set constraints in ld_def to set_cons *
   * - p is the set args of the inductive egde needed unfold *)
  let setequ_2_real (of_2n: int IntMap.t) (p: sid list)
      (l: (int * l_call) list) (se: set_equa)
      : set_cons =
    (* deal with offset to symbolic variables*)
    let selt_2_real (e: set_elt): int =
      match e with
      | Se_this -> i
      | Se_field f ->
          try IntMap.find f of_2n
          with Not_found -> Log.fatal_exn "offset without match sv" in
    (* deal with set var in ld_def to real set args *)
    let setv_2_real (s: set_var): sid =
      match s with
      | Sv_actual x ->
          begin
            try List.nth p x
            with
            | Failure _ ->
                Log.fatal_exn "current: cannot find real set parameter"
          end
      | Sv_nextpar x ->
         begin
           match l with
           | [] -> Log.fatal_exn "next: cannot find next ldesc"
           | (_, lst) :: _ ->
               try List.nth lst.lc_args x
               with
               | Failure _ ->
                   Log.fatal_exn "nth: cannot find set arguments of next"
          end
      | Sv_subpar (x, y) ->
          begin
            try
              let _, n = List.nth l (x+1) in
              List.nth n.lc_args x
            with
            | Failure _ -> Log.fatal_exn "nth: cannot find nth ldesc"
          end in
    let setdef_2_real (sd: set_def): set_expr =
      match sd with
      | Sd_var v -> S_var (setv_2_real v)
      | Sd_uplus (e, v) ->
          S_uplus (S_node (selt_2_real e), S_var (setv_2_real v))
      | Sd_eunion (e, v) ->
          S_union (S_node (selt_2_real e), S_var (setv_2_real v))
      | Sd_union (v0, v1) ->
          S_union (S_var (setv_2_real v0), S_var (setv_2_real v1)) in
    match se with
    | Se_mem (x, y) -> S_mem (selt_2_real x, setdef_2_real y)
    | Se_eq  (x, y) -> S_eq (S_var (setv_2_real x), setdef_2_real y) in
  let setequ_2_real (of_2n: int IntMap.t) (p: sid list)
      (l: (int*l_call) list) (se: set_equa)
      : set_cons =
    let r = setequ_2_real of_2n p l se in
    if debug_module then
      Log.debug "unfold %s => %s" (set_equa_2str se)
        (Set_utils.set_cons_2str r);
    r in
  let add_setcons (c: set_cons) (l: set_cons list): set_cons list =
    match c with (* pruning empty constraints *)
    | S_eq (S_var x, S_var y) -> if x = y then l else c :: l
    | _ -> c :: l in
  let ln = sv_find i lm in
  (* general construction of the empty case *)
  let make_empty lc remsetvs (oidst: int option) =
    let lm, cons =
      match oidst with
      | Some idst ->
          lseg_edge_rem i lm, Nc_cons (Apron.Tcons1.EQ, Ne_var i, Ne_var idst)
      | None ->
          list_edge_rem i lm,
          Nc_cons (Apron.Tcons1.EQ, Ne_csti lc.lc_def.ld_emp_csti, Ne_var i) in
    let paras =
      match lc.lc_def.ld_set with
      | None -> []
      | Some x -> x.s_params in
    let setcons =
      try
        List.fold_left2
          (fun setcons i j ->
            if j.st_add || j.st_head then
              S_eq (S_var i, S_empty) :: setcons
            else setcons
          ) [ ] lc.lc_args paras
      with Invalid_argument _ ->
        Log.fatal_exn "list_unfold: parameters does not match" in
    { ur_lmem     = lm;
      ur_cons     = [ cons ];
      ur_mcons    = lc.lc_def.ld_emp_mcons;
      ur_setcons  = setcons;
      ur_newsetvs = IntMap.empty;
      ur_remsetvs = remsetvs; } in
  match ln.ln_e with
  | Lhpt _ -> Log.fatal_exn "unfold to empty / points-to"
  | Lhemp -> Log.fatal_exn "non-local unfold"
  | Lhlist lc ->
      let remsetvs = setv_to_remove lc lm in
      (* empty segment *)
      let ur_empty = make_empty lc remsetvs None in
      (* inductive of length at least 1 *)
      let ur_next =
        let ln = { ln with ln_e = Lhemp } in
        let lm = { lm with lm_mem = IntMap.add i ln lm.lm_mem } in
        let o2n, n2l, lm, nsetvs = create_ld_block lc.lc_args lc.lc_def lm in
        let lm =
          List.fold_left (fun lm (i, ld) -> list_edge_add i ld lm) lm n2l in
        let setcons =
          match lc.lc_def.ld_set with
          | None -> [ ]
          | Some x ->
              List.fold_left
                (fun setcons l ->
                  add_setcons (setequ_2_real o2n lc.lc_args n2l l) setcons
                ) [ ] x.s_equas in
        { ur_lmem     = lm;
          ur_cons     = [ Nc_cons (Apron.Tcons1.DISEQ,
                                   Ne_csti lc.lc_def.ld_emp_csti, Ne_var i) ];
          ur_mcons    = lc.lc_def.ld_next_mcons;
          ur_setcons  = setcons;
          ur_newsetvs = nsetvs;
          ur_remsetvs = remsetvs } in
      [ ur_next; ur_empty ]
  | Lhlseg (lc, idst) ->
      let remsetvs = setv_to_remove lc lm in
      (* empty segment *)
      let ur_empty = make_empty lc remsetvs (Some idst) in
      (* segment of length at least 1 *)
      let ur_next =
        (* TODO: check if there is an issue with this list edge *)
        let n_lm = lseg_edge_rem i lm in
        let o2n, n2l, n_lm, nsetvs =
          create_ld_block lc.lc_args lc.lc_def n_lm in
        let o_ff, o_ld = List.hd n2l in
        let n_lm = lseg_edge_add o_ff idst o_ld n_lm in
        let n_lm =
          List.fold_left (fun m (i, lc) -> list_edge_add i lc m)
            n_lm (List.tl n2l) in
        let setcons =
          match lc.lc_def.ld_set with
          | None -> [ ]
          | Some x ->
              List.fold_left
                (fun setcons l ->
                  add_setcons (setequ_2_real o2n lc.lc_args n2l l) setcons
                ) [ ]  x.s_equas in
        { ur_lmem     = n_lm ;
          ur_cons     = [ Nc_cons (Apron.Tcons1.DISEQ,
                                   Ne_csti lc.lc_def.ld_emp_csti, Ne_var i) ] ;
          ur_mcons    = lc.lc_def.ld_next_mcons;
          ur_setcons  = setcons;
          ur_newsetvs = nsetvs;
          ur_remsetvs = remsetvs  } in
      if only_non_emp then [ ur_next ]
      else [ ur_next ; ur_empty ]
