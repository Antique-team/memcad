(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: inst_utils.ml
 **       utilities for the instantiation of set parameters
 ** Xavier Rival, Huisong Li, 2015/04/05 *)
open Data_structures
open Lib

open Graph_sig
open Ind_sig
open Inst_sig
open Nd_sig
open Set_sig

open Nd_utils
open Set_utils
open Graph_utils

(** Error report *)
module Log =
  Logger.Make(struct let section = "ins_uts_" and level = Log_level.DEBUG end)

let debug_module = false


(** Data-type *)
type setv_inst = Inst_sig.setv_inst


(** Basic functions on set parameters instantiations *)
(* Empty *)
let setv_inst_empty =
  { setvi_add   = IntSet.empty;
    setvi_rem   = IntSet.empty;
    setvi_eqs   = IntMap.empty;
    setvi_guess = IntMap.empty;
    setvi_none  = IntSet.empty;
    setvi_props = [ ];
    setvi_prove = [ ];
    setvi_fresh = IntSet.empty; }

let sv_inst_empty =
  { sv_fresh = IntSet.empty;
    sv_ie    = IntSet.empty;
    sv_eqs   = IntMap.empty;
    sv_low   = IntMap.empty;
    sv_up    = IntMap.empty;
    sv_eqlow = IntMap.empty;
    sv_equp  = IntMap.empty;
    sv_cons = [ ]; }

(* Pretty-printing *)
let setv_inst_2stri (ind: string) (inst: setv_inst): string =
  let s =
    Printf.sprintf "%sadd: %s\n%srem: %s\n" ind (intset_2str inst.setvi_add)
       ind (intset_2str inst.setvi_rem) in
  let s =
    IntMap.fold
      (fun setv ex acc ->
        Printf.sprintf "%s%sS[%d] |=> %s\n" acc ind setv (set_expr_2str ex)
      ) inst.setvi_eqs s in
  let s =
    IntMap.fold
      (fun setv sv acc ->
        Printf.sprintf "%s%sS[%d] |:> N[%d]\n" acc ind setv sv
      ) inst.setvi_guess s in
  let s =
    IntSet.fold
      (fun setv acc ->
        Printf.sprintf "%s%sS[%d] |=> ???\n" acc ind setv
      ) inst.setvi_none s in
  let s =
    List.fold_left
      (fun acc sc ->
        Printf.sprintf "%s%s+ %s\n" acc ind (set_cons_2str sc)
      ) s inst.setvi_props in
  let s =
    List.fold_left
      (fun acc sc ->
        Printf.sprintf "%s%s? |- %s\n" acc ind (set_cons_2str sc)
      ) s inst.setvi_prove in
  let sf =
    IntSet.fold
      (fun setv acc ->
        Printf.sprintf "%sS[%d]" acc setv
      ) inst.setvi_fresh "" in
  Printf.sprintf "%sFresh setvars:{%s}\n" s sf

let sv_inst_2stri (ind: string) (inst: sv_inst): string =
  let s =
    Printf.sprintf "%sInstantiable svs: %s\n"
      ind (intset_2str inst.sv_fresh) in
  let s =
    IntMap.fold
      (fun sv ex acc ->
        Printf.sprintf "%s%sN[%d] |== %s\n" acc ind sv (n_expr_2str ex)
      ) inst.sv_eqs s in
  let f_2str s op m =
    IntMap.fold
      (fun sv exs acc ->
         Printf.sprintf "%s%sN[%d] %s %s\n" acc ind sv op
           (gen_list_2str "" n_expr_2str ";" exs)
      ) m s in
  let s = f_2str s  "|>" inst.sv_low in
  let s = f_2str s  "|<" inst.sv_up in
  let s = f_2str s  "|>=" inst.sv_eqlow in
  let s = f_2str s  "|<=" inst.sv_equp in
  Printf.sprintf "%sLeft constraints:\n%s\n"
  s (gen_list_2str "" n_cons_2str "\n" inst.sv_cons)

(* Add a new setv *)
let add_setv (setv: int) (inst: setv_inst): setv_inst =
  assert (not (IntSet.mem setv inst.setvi_add));
  assert (not (IntSet.mem setv inst.setvi_rem));
  { inst with setvi_add = IntSet.add setv inst.setvi_add }

(* Remove a previously added setv *)
let rem_setv (setv: int) (inst: setv_inst): setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  assert (not (IntSet.mem setv inst.setvi_rem));
  { inst with setvi_rem = IntSet.add setv inst.setvi_rem }

(* Is setv free in inst ? *)
let setv_inst_free (setv: int) (inst: setv_inst): bool =
  not (IntMap.mem setv inst.setvi_eqs) && not (IntSet.mem setv inst.setvi_none)
    && not (IntMap.mem setv inst.setvi_guess)

(* Bind setv to eq in inst *)
let setv_inst_bind (setv: int) eq (inst: setv_inst): setv_inst =
  if debug_module then
    Log.debug "trying to bind: %d\n%s" setv (setv_inst_2stri "  " inst);
  assert (IntSet.mem setv inst.setvi_add);
  if setv_inst_free setv inst then
    { inst with setvi_eqs = IntMap.add setv eq inst.setvi_eqs }
  else Log.fatal_exn "setv_inst_bind: %d already specified" setv

(* Mark setv as unknown, with no information *)
let setv_inst_nobind (setv: int) (inst: setv_inst): setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if setv_inst_free setv inst then
    { inst with setvi_none = IntSet.add setv inst.setvi_none }
  else Log.fatal_exn "setv_inst_nobind: %d already specified" setv

(* Mark setv as unknown, can be "guessed" later using an element *)
let setv_inst_guess (setv: int) (sv: int) (inst: setv_inst): setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if setv_inst_free setv inst then
    { inst with setvi_guess = IntMap.add setv sv inst.setvi_guess }
  else Log.fatal_exn "setv_inst_guess: %d already specified" setv

(* Overwrite a previously done binding *)
let setv_inst_over_bind (setv: int) (ex: set_expr) (inst: setv_inst)
    : setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if IntSet.mem setv inst.setvi_none then
    setv_inst_bind setv ex
      { inst with setvi_none = IntSet.remove setv inst.setvi_none }
  else Log.fatal_exn "setv_inst_make_guess: setv not guessable"

(* Constrain setv, by "guessing" it as ex *)
let setv_inst_make_guess (setv: int) (ex: set_expr) (inst: setv_inst)
    : setv_inst =
  assert (IntSet.mem setv inst.setvi_add);
  if IntMap.mem setv inst.setvi_guess then
    setv_inst_bind setv ex
      { inst with setvi_guess = IntMap.remove setv inst.setvi_guess }
  else Log.fatal_exn "setv_inst_make_guess: setv not guessable"


(** Completion of an instantiation *)
let setv_inst_complete
    (roots: IntSet.t)
    (set_sat: set_cons -> bool)
    (inst: setv_inst)
    : setv_inst =
  let debug_loc = false in
  (* 1. improve instantiation by binding roots instead of others
   *    if S[i] |=> S[k] and xnum |- S[k] = S[j], with S[j] root, then
   *    we use S[i] |=> S[j] instead *)
  let inst =
    IntMap.fold
      (fun setv ex acc ->
        match ex with
        | S_var setv0 ->
            if IntSet.mem setv0 roots then acc
            else
              let rootsok =
                IntSet.fold
                  (fun i acc ->
                    if debug_loc then Log.info "point: %d, %d" i setv0;
                    if set_sat (S_eq (S_var i, S_var setv0)) then
                      IntSet.add i acc
                    else acc
                  ) roots IntSet.empty in
              if IntSet.cardinal rootsok > 0 then
                (* replace with the lowest root ID *)
                let root = IntSet.min_elt rootsok in
                { inst with
                  setvi_eqs = IntMap.add setv (S_var root) inst.setvi_eqs }
              else acc
        | _ -> acc
      ) inst.setvi_eqs inst in
  (* 2. adjust guesses based on membership *)
  let inst =
    IntMap.fold
      (fun setv sv acc ->
        let l =
          IntSet.fold
            (fun root acc ->
              if set_sat (S_mem (sv, S_var root)) then root :: acc
              else acc
            ) roots [ ] in
        match l with
        | root0 :: _ -> setv_inst_make_guess setv (S_var root0) acc
        | _ -> acc
      ) inst.setvi_guess inst in
  if debug_loc then Log.info "setv_inst_complete,Ph3";
  inst


(** Strengthening of an instantiation *)
let setv_inst_strengthen (iref: setv_inst) (itgt: setv_inst): setv_inst =
  IntSet.fold
    (fun setv acc ->
      try setv_inst_over_bind setv (IntMap.find setv iref.setvi_eqs) acc
      with Not_found -> acc
    ) itgt.setvi_none itgt


let fold_add (f: int -> 'a -> 'a) (inst: setv_inst) (x: 'a): 'a =
  IntSet.fold f inst.setvi_add x
let fold_rem (f: int -> 'a -> 'a) (inst: setv_inst) (x: 'a): 'a =
  IntSet.fold f inst.setvi_rem x


(* Instantiated fresh set variables from set constraints *)
let rec instantiate_cons (inst: set_expr IntMap.t)
    (setctr: set_cons list) (fresh: IntSet.t)
    : set_expr IntMap.t * set_cons list * IntSet.t =
  (* instantaite a set variable accoring to equal set expressions *)
  let inst_var (sl: set_expr) (sr: set_expr) (setvs: IntSet.t)
    : (int * set_expr) option =
    let sl_uplus = linear_svars sl true in
    let sr_uplus = linear_svars sr true in
    let sl_union = linear_svars sl false in
    let sr_union = linear_svars sr false in
    let inst b ssl ssr nsl nsr =
      let ssl_f = IntSet.inter ssl setvs in
      let ssr_f = IntSet.inter ssr setvs in
      let f_inst setvl setvr svl svr v =
        let v_s, v_n = IntSet.diff setvl setvr, IntSet.diff svl svr in
        Some (v, if b then make_sexp v_s v_n true
              else make_sexp v_s v_n false) in
      if ssl_f = IntSet.empty && IntSet.cardinal ssr_f = 1 then
        let v = IntSet.min_elt ssr_f in
        f_inst ssl ssr nsl nsr v
      else if ssr_f = IntSet.empty && IntSet.cardinal ssl_f = 1 then
      let v = IntSet.min_elt ssl_f in
      f_inst ssr ssl nsr nsl v
      else None in
    match sl_uplus, sr_uplus, sl_union, sr_union with
    | Some (ssl, nsl),  Some (ssr, nsr), _, _ ->
      inst true ssl ssr nsl nsr
    | _, _, Some (ssl, nsl),  Some (ssr, nsr) ->
      inst false ssl ssr nsl nsr
    | _ -> None in
  let r_inst, r_setctr, r_fresh =
    List.fold_left
      (fun (inst, ctr, s) con ->
        match con with
        | S_mem _ -> inst, (con::ctr), s
        | S_subset _ ->inst,  (con::ctr), s
        | S_eq (sl, sr) ->
            begin
              let ins = inst_var sl sr fresh in
              match ins with
              | Some (i, e) ->
                  IntMap.add i e inst, ctr, IntSet.remove i s
              | None -> inst, con::ctr, s
            end
      ) (inst, [ ], fresh) setctr in
  if List.length r_setctr == List.length setctr then
    inst, setctr, fresh
  else instantiate_cons r_inst r_setctr r_fresh


(* Replace fresh setv according to their instantiation *)
let rename_inst (setvi_eqs: set_expr IntMap.t) (sinst: set_expr IntMap.t) =
  let rec rename_expr (er: set_expr) (sinst: set_expr IntMap.t) =
    match er with
    | S_var sid ->
        if IntMap.mem sid sinst then IntMap.find sid sinst
        else S_var sid
    | S_empty -> S_empty
    | S_node nid -> S_node nid
    | S_uplus (sl, sr) ->
        S_uplus (rename_expr sl sinst, rename_expr sr sinst)
    | S_union (sl, sr) ->
        S_union (rename_expr sl sinst, rename_expr sr sinst) in
  IntMap.fold
    (fun key ex acc ->
      IntMap.add key (rename_expr ex sinst) acc
    ) setvi_eqs IntMap.empty


(* instantiate fresh set variables according to guessed equal relationship *)
let instantiate_eq (inst: setv_inst) (eq: int IntMap.t)
    (smap: set_expr IntMap.t): setv_inst =
  let fresh = inst.setvi_fresh in
  (* collect instantiation with fresh set variables *)
  let ninst, ainst =
    IntMap.fold
      (fun key se (accn, acca) ->
        let svars = Set_utils.set_expr_setvs se in
        let fsh_svars = IntSet.inter svars fresh in
        if IntSet.is_empty fsh_svars then
          accn, IntMap.add key se acca
        else
          IntMap.add key se accn, acca
      ) inst.setvi_eqs (IntMap.empty, IntMap.empty) in
  let setctr =
    IntMap.fold
      (fun key i acc ->
        match IntMap.mem key ainst, IntMap.mem i ainst with
        | true, true  -> acc
        | true, false ->
            (S_eq (IntMap.find key ainst, IntMap.find i ninst)) :: acc
        | false, true ->
            (S_eq (IntMap.find key ninst, IntMap.find i ainst)) :: acc
        | false, false ->
            (S_eq (IntMap.find key ninst, IntMap.find i ninst)) :: acc
      ) eq [] in
  let setctr =
    IntMap.fold (fun k se acc ->
        (S_eq (IntMap.find k inst.setvi_eqs, se))::acc
      ) smap setctr in
  let f_inst, setctr, f_fresh = instantiate_cons IntMap.empty setctr fresh in
  { inst with
    setvi_fresh = f_fresh;
    setvi_eqs   = rename_inst inst.setvi_eqs f_inst; }


(* generate equality from parameters of output graph to input graph *)
let gen_eq (sl: int list) (ol: int list) (m: set_expr IntMap.t) =
  assert (List.length sl = List.length ol);
  List.fold_left2
    (fun acc ii io ->
       IntMap.add io (S_var ii) m
    ) m  sl ol

(* generate equality from set parameters of output inductive edge to
 * set parameters of input inductive edge *)
let l_call_inst
    (ls_i: ind_args) (* set pars from the join input *)
    (g: graph)    (* join input graph *)
    (ls_o: ind_args) (* set pars from the join output being constructed *)
    (inst: setv_inst) (* instantiation being constructed *)
    (sv_inst: sv_inst)  (* sv instantiation being constructed *)
    (wkt: int_wk_typ IntMap.t)  (* weaken type *)
    : graph * setv_inst * sv_inst * int list=
  let f i accg accs =
    let ia, accg = sv_add_fresh Ntint Nnone accg in
    i+1, accg, ia, { accs with sv_fresh = IntSet.add ia accs.sv_fresh } in
  let _, g, rev_args, sv_inst =
    List.fold_left
      (fun (i, accg, acca, accs) ele ->
        match IntMap.find i wkt with
        | `Eq | `Add -> i+1, accg, ele :: acca, accs
        | `Non ->
            let i, accg, ia, accs = f i accg accs in
            i, accg, ia :: acca, accs
        | `Leq ->
            let i, accg, ia, accs =  f i accg accs in
            let cons = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var ia, Ne_var ele) in
            i, accg, ia::acca,
            { accs with sv_cons = cons :: accs.sv_cons }
        | `Geq ->
          let i, accg, ia, accs =  f i accg accs in
          let cons = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var ele, Ne_var ia) in
          i, accg, ia :: acca, { accs with sv_cons = cons :: accs.sv_cons }
      )
      (0, g, [], sv_inst) ls_i.ia_int in
  let i_args = List.rev rev_args in
  g, { inst with setvi_eqs = gen_eq ls_i.ia_set ls_o.ia_set inst.setvi_eqs },
  sv_inst, i_args

(* Generate equality from set parameters of output segment edge
 * to set parameters of input segment edge *)
let l_seg_inst
    (ls_i: seg_edge) (* set pars from the join input *)
    (g: graph)    (* join input graph *)
    (ls_o: seg_edge) (* set pars from the join output being constructed *)
    (inst: setv_inst) (* instantiation being constructed *)
    (sv_inst: sv_inst)  (* sv instantiation being constructed *)
    (wkt: int_wk_typ IntMap.t)  (* weaken type *)
    : graph * setv_inst * sv_inst * int list * int list =
  let setv_inst =
    let eqs =
      gen_eq ls_i.se_dargs.ia_set ls_o.se_dargs.ia_set
        (gen_eq ls_i.se_sargs.ia_set ls_o.se_sargs.ia_set inst.setvi_eqs) in
    { inst with setvi_eqs = eqs } in
  let f accg accs =
    let ia, accg = sv_add_fresh Ntint Nnone accg in accg, ia,
    { accs with sv_fresh = IntSet.add ia accs.sv_fresh } in
  let _, g, rev_sargs, rev_dargs, sv_inst =
    List.fold_left2
      (fun (i, g, args_s, args_d, accs) id_s id_d ->
        match IntMap.find i wkt with
        | `Eq ->i+1, g, id_s :: args_s, id_d :: args_d, accs
        | `Non ->
            let g, is, accs = f g accs in
            let g, id, accs = f g accs in
            i+1, g, is :: args_s, id :: args_d, accs
        | `Leq ->
            let g, is, accs = f g accs in
            let g, id, accs = f g accs in
            let cons0 = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var is, Ne_var id_s) in
            let cons1 = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var id_d, Ne_var id) in
            let cons = cons0 :: cons1 :: accs.sv_cons in
            i+1, g, is :: args_s, id :: args_d, { accs with sv_cons = cons }
        | `Geq ->
            let g, is, accs = f g accs in
            let g, id, accs = f g accs in
            let cons0 = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var id_s, Ne_var is) in
            let cons1 = Nc_cons (Apron.Tcons1.SUPEQ, Ne_var id, Ne_var id_d) in
            let cons = cons0 :: cons1 :: accs.sv_cons in
            i+1, g, is::args_s, id :: args_d, { accs with sv_cons = cons }
        | `Add ->
            let g, is, accs = f g accs in
            let g, id, accs = f g accs in
            let cons =
              Nc_cons (Apron.Tcons1.EQ, Ne_var is,
                       Ne_bin (Apron.Texpr1.Add, Ne_var id,
                               Ne_bin (Apron.Texpr1.Sub, Ne_var id_s,
                                       Ne_var id_d))) in
            let cons = cons :: accs.sv_cons in
            i+1, g, is :: args_s, id :: args_d, { accs with sv_cons = cons }
      )
      (0, g, [], [], sv_inst) ls_i.se_sargs.ia_int ls_i.se_dargs.ia_int in
  g, setv_inst, sv_inst, (List.rev rev_sargs), (List.rev rev_dargs)

(* Generate equality map from set parameters of output
 * summarized edge to set parameters of summarized edge
 * generated in inclusion checking *)
let gen_map (is: int list) (io: int list) (m: int IntMap.t) =
  List.fold_left2 (fun acc is o -> IntMap.add is o acc) m is io
let rename_is_le_inst
    (is_le_inst: set_expr IntMap.t)
    (jinst:  set_expr IntMap.t)
    (m: int IntMap.t): set_expr IntMap.t =
  IntMap.fold
    (fun i ex acc ->
       let j = IntMap.find i m in
       if IntMap.mem j acc then
         (* double instantiation attempt, fail *)
         Log.fatal_exn "attempt at double instantiation"
       else IntMap.add j ex acc
    ) is_le_inst jinst

(* Merging sv_inst in join and sv_inst return from is_le:
 * as is_le only returns instantiation on fresh sv, therefore,
 * this, merging will just join these two sv_inst *)
let sv_inst_merge (instl: sv_inst) (instr: sv_inst): sv_inst =
  assert((IntSet.inter instl.sv_fresh instr.sv_fresh) = IntSet.empty);
  let f_merge key el er =
    Log.fatal_exn "attempt at double instantiation" in
  { sv_fresh = IntSet.union instl.sv_fresh instr.sv_fresh;
    sv_ie    = IntSet.union instl.sv_ie instr.sv_ie;
    sv_cons  = instl.sv_cons @ instr.sv_cons;
    sv_eqs   = IntMap.union f_merge instl.sv_eqs instr.sv_eqs;
    sv_low   = IntMap.union f_merge instl.sv_low instr.sv_low;
    sv_up    = IntMap.union f_merge instl.sv_up instr.sv_up;
    sv_eqlow = IntMap.union f_merge instl.sv_eqlow instr.sv_eqlow;
    sv_equp  = IntMap.union f_merge instl.sv_equp instr.sv_equp; }

(* Deal with instantaition from is_le_ind *)
let is_le_call_inst
    (ls_i: ind_args) (* set pars from the is_le output *)
    (ls_o: ind_args) (* set pars from the join output being constructed *)
    (inst: setv_inst) (* set instantiation being constructed *)
    (jsv_inst: sv_inst)  (* sv instantiation being constructed *)
    (sinst: set_expr IntMap.t)  (* instantiation from is_le *)
    (sv_inst: sv_inst) (* sv instantiation from is_le *)
    (nset: IntSet.t) (* new set variables generated from is_le *)
    (cons: set_cons list)       (* non proved set constraints *)
    (rel:  int IntMap.t)   (* sv mapping inferred by the inclusion *)
    : setv_inst * sv_inst * int list =
  (* generate maps of set parameters from is_le ind to out ind *)
  let setpar_maps = gen_map ls_i.ia_set ls_o.ia_set IntMap.empty in
  let setv_inst =
    { inst with
      setvi_eqs   = rename_is_le_inst sinst inst.setvi_eqs setpar_maps;
      setvi_fresh = IntSet.union nset inst.setvi_fresh;
      setvi_prove = cons@inst.setvi_prove } in
  let sv_inst = sv_inst_merge jsv_inst sv_inst in
  setv_inst, sv_inst, List.map (fun i -> IntMap.find i rel) ls_i.ia_int

(* Deal with instantaition from is_le_seg *)
let is_le_seg_inst
    (ls_i: seg_edge) (* set pars from the is_le output *)
    (ls_o: seg_edge) (* set pars from the join output being constructed *)
    (inst: setv_inst) (* instantiation being constructed *)
    (jsv_inst: sv_inst)  (* sv instantiation being constructed *)
    (sinst: set_expr IntMap.t)  (* instantiation from is_le *)
    (sv_inst: sv_inst) (* sv instantiation from is_le *)
    (nset: IntSet.t) (* new set variables generated from is_le *)
    (cons: set_cons list)  (* non proved set constraints *)
    (rel:  int IntMap.t)   (* sv mapping inferred by the inclusion *)
    : setv_inst * sv_inst * int list * int list=
  (* generate maps of set parameters from is_le ind to out ind *)
  let setpar_maps =
    gen_map ls_i.se_dargs.ia_set ls_o.se_dargs.ia_set
      (gen_map ls_i.se_sargs.ia_set ls_o.se_sargs.ia_set IntMap.empty) in
  let setv_inst =
    { inst with
      setvi_eqs = rename_is_le_inst sinst inst.setvi_eqs setpar_maps;
      setvi_fresh = IntSet.union nset inst.setvi_fresh;
      setvi_prove = cons@inst.setvi_prove } in
  let sv_inst = sv_inst_merge jsv_inst sv_inst in
  setv_inst, sv_inst,
  List.map (fun i -> IntMap.find i rel) ls_i.se_sargs.ia_int,
  List.map (fun i -> IntMap.find i rel) ls_i.se_dargs.ia_int

(* Instantiation of symbolic variables according to equality constraints,
 * that is, when a fresh sv (instantiable sv) is constrainted to be equal
 * to a numerical expression with only non fresh SV, then, we instantiate
 * this fresh sv to the expression *)
let nd_instantiation_eq (cons: n_cons list) (fsvs: IntSet.t)
    (inst: n_expr IntMap.t): (n_expr IntMap.t) * n_cons list * n_cons list =
  (* compute fresh svs that has been instantiated and fresh svs that
   * still not instantiated *)
  let inst_vars =
    IntMap.fold (fun i _ acc -> IntSet.add i acc) inst IntSet.empty in
  let fsvs = IntSet.diff fsvs inst_vars in
  (* instantiation of a sv *)
  let rec do_inst_i (n: int) (svs: IntSet.t) (inst: n_expr IntMap.t)
      (ctrs: n_cons list): n_expr IntMap.t =
    if IntMap.mem n inst then inst
    else
      let f e inst =
        Nd_utils.n_expr_fold
          (fun i acc -> if IntSet.mem i svs then false else acc) e true in
      let f_sub e inst =
        Nd_utils.n_expr_subst
          (fun i -> try IntMap.find i inst with Not_found -> Ne_var i) e in
      match ctrs with
      | [] -> inst
      | ctr :: tl ->
          begin
            match ctr with
            | Nc_rand
            | Nc_bool _ -> do_inst_i n svs inst tl
            | Nc_cons (Apron.Tcons1.EQ, e0, e1) ->
                if e0 = Ne_var n &&f e1 inst then
                  IntMap.add n (f_sub e1 inst) inst
                else if e1 = Ne_var n &&f e0 inst then
                  IntMap.add n (f_sub e0 inst) inst
                else
                  do_inst_i n svs inst tl
            | _ -> do_inst_i n svs inst tl
          end in
  (* instantiation of a set of svs, and return instantiation and non
   * instantiated svs *)
  let rec do_inst (svs: IntSet.t) (inst: n_expr IntMap.t) (ctrs: n_cons list)
      : n_expr IntMap.t * IntSet.t =
    let svs_res, inst_res =
      IntSet.fold
        (fun s (accs, acci) ->
          let acci = do_inst_i s (IntSet.diff svs accs) acci ctrs in
          if IntMap.mem s acci then
            (IntSet.add s accs), acci
          else accs, acci
        ) svs (IntSet.empty, inst) in
    if IntSet.is_empty svs_res then inst_res, svs
    else do_inst (IntSet.diff svs svs_res) inst_res ctrs in
  (* do instantiation of a set of svs *)
  let inst, noninst_vars = do_inst fsvs inst cons in
  (* seperate constraints on left side into two parts: one parts need to be
     proved, the other parts is for future instantiation *)
  let ctr_to_prove, ctr_to_inst =
    List.fold_left
      (fun (accp, acci) ctr ->
        let no_uninst_svs =
          Nd_utils.n_cons_fold
            (fun i acc -> if IntSet.mem i noninst_vars then false else acc)
            ctr true in
        if no_uninst_svs then
          let ctr =
            Nd_utils.n_cons_subst
              (fun i -> try IntMap.find i inst with Not_found -> Ne_var i)
              ctr in
          ctr :: accp, acci
        else accp, ctr :: acci
      ) ([], []) cons in
  inst, ctr_to_prove, ctr_to_inst

(* SV instantiation: first instantiate some fresh sv according to equality
 * constraints, and then, if a non-instantiated sv \alpha is constrainted
 * to be, l_e <= \alpha <= r_e, and l_e and r_e only contain already
 * instantiated sv, then, if we can prove that, l_e <= r_e, we can instantiate
 * \alpha to be a value from l_e to r_e *)
let sv_instantiation (sv_inst: sv_inst)
    (is_sat: n_cons -> bool): sv_inst =
  (* SV instantiation according to eq numerical constraints *)
  let nd_inst_eq, ctr_to_prove, ctr_to_inst =
    nd_instantiation_eq sv_inst.sv_cons sv_inst.sv_fresh sv_inst.sv_eqs in
  let sv_inst =
    let ie =
      IntMap.fold (fun k _ acc -> IntSet.add k acc) nd_inst_eq sv_inst.sv_ie in
    { sv_inst with
      sv_ie   = ie;
      sv_eqs  = nd_inst_eq;
      sv_cons = ctr_to_inst; } in
  let non_inst_svs = IntSet.diff sv_inst.sv_fresh sv_inst.sv_ie in
  (* check whether a expression has non instantiated svs *)
  let no_fsv e =
    Nd_utils.n_expr_fold
      (fun i acc -> if IntSet.mem i non_inst_svs then false else acc)
      e true in
  (* update the instantiation of a sv according to a constraint *)
  let do_inst_cons (sv: int) (ctr: n_cons) (inst: sv_inst): sv_inst * bool =
    match ctr with
    | Nc_rand | Nc_bool _ -> inst, false
    | Nc_cons (Apron.Tcons1.SUP, el, er) ->
        if el = Ne_var sv && no_fsv er
            &&
          List.for_all
            (fun x -> is_sat (Nc_cons (Apron.Tcons1.SUP, x, er)))
            (IntMap.find sv inst.sv_up @ IntMap.find sv inst.sv_equp)
        then
          let sv_low = IntMap.find sv inst.sv_low in
          {inst with sv_low = IntMap.add sv (er::sv_low) inst.sv_low;}, true
        else if er = Ne_var sv && no_fsv el
            &&
          List.for_all
            (fun x -> is_sat (Nc_cons (Apron.Tcons1.SUP, el, x)))
            (IntMap.find sv inst.sv_low @ IntMap.find sv inst.sv_eqlow)
        then
          let sv_up = IntMap.find sv inst.sv_up in
          { inst with sv_up = IntMap.add sv (el :: sv_up) inst.sv_up }, true
        else inst, false
    | Nc_cons (Apron.Tcons1.SUPEQ, el, er) ->
        if el = Ne_var sv && no_fsv er
            &&
          List.for_all
            (fun ele -> is_sat (Nc_cons (Apron.Tcons1.SUP, ele, er)))
            (IntMap.find sv inst.sv_up)
            &&
          List.for_all
            (fun ele -> is_sat (Nc_cons (Apron.Tcons1.SUPEQ, ele, er)))
            (IntMap.find sv inst.sv_equp)
        then
          let sv_eqlow = IntMap.find sv inst.sv_eqlow in
          { inst with
            sv_eqlow = IntMap.add sv (er :: sv_eqlow) inst.sv_eqlow }, true
        else
          if er = Ne_var sv && no_fsv el
              &&
            List.for_all
              (fun ele -> is_sat (Nc_cons (Apron.Tcons1.SUP, el, ele)))
              (IntMap.find sv inst.sv_low)
              &&
            List.for_all
              (fun ele -> is_sat (Nc_cons (Apron.Tcons1.SUPEQ, el, ele)))
              (IntMap.find sv inst.sv_eqlow)
          then
            let sv_equp = IntMap.find sv inst.sv_equp in
            { inst with
              sv_equp = IntMap.add sv (el :: sv_equp) inst.sv_equp }, true
          else inst, false
    | _ -> inst, false in
  (*  instantiate a sv according to a list of constraints *)
  let do_inst_sv (sv: int) (inst: sv_inst): sv_inst  =
    let inst =
      if not (IntMap.mem sv inst.sv_eqs || IntMap.mem sv inst.sv_low
         || IntMap.mem sv inst.sv_up || IntMap.mem sv inst.sv_eqlow
         || IntMap.mem sv inst.sv_equp)
      then
        (* init instantiation for sv *)
        { inst with
          sv_low   = IntMap.add sv [] inst.sv_low;
          sv_up    = IntMap.add sv [] inst.sv_up;
          sv_eqlow = IntMap.add sv [] inst.sv_eqlow;
          sv_equp  = IntMap.add sv [] inst.sv_equp; }
      else inst in
    let inst, ctrs =
      List.fold_left
        (fun (acci, acct) ctr ->
          let acci, b = do_inst_cons sv ctr acci in
          if b then acci, acct
          else acci, ctr :: acct
        ) (inst, []) inst.sv_cons in
    { inst with sv_cons = ctrs } in
  (* instantiate each non instantiated sv *)
  let sv_inst =
    IntSet.fold (fun sv inst -> do_inst_sv sv inst) non_inst_svs sv_inst in
  sv_inst

(* Deal with some constraints left from sv_instantiation function:
 * as an example, for constraint \alpha <= \beta, where both \alpha and
 * \beta are fresh sv, and in sv_inst, we have e1 <= \alpha, \beta <= e2,
 * in this case, if we can prove that e1 <= e2, then, we can instantiate
 * \alpha be a value from e1 to \beta, and instantiate \beta be a value
 * from \alpha to e2. *)
let do_sv_inst_left_ctrs (sv_inst: sv_inst)
    (is_sat: n_cons -> bool): sv_inst =
  let f e inst =
    Nd_utils.n_expr_fold
      (fun i acc ->
        if IntSet.mem i inst.sv_fresh && not (IntMap.mem i sv_inst.sv_eqs) then
          false
        else acc)
      e true in
  let do_sup inst lexprs uexprs op =
    List.for_all
      (fun le ->
        List.for_all
          (fun ue ->
            f le inst && f ue inst && is_sat (Nc_cons (op, ue, le))
          ) uexprs
      ) lexprs in
  let do_all_sup sv_inst sl sr =
    assert (not (IntMap.mem sl sv_inst.sv_eqs || IntMap.mem sr sv_inst.sv_eqs));
    let sl_low = IntMap.find sl sv_inst.sv_low in
    let sl_eqlow = IntMap.find sl sv_inst.sv_eqlow in
    let sr_up = IntMap.find sr sv_inst.sv_up in
    let sr_equp = IntMap.find sr sv_inst.sv_equp in
    do_sup sv_inst sl_low sr_up Apron.Tcons1.SUP
      && do_sup sv_inst sl_eqlow sr_up Apron.Tcons1.SUP
      && do_sup sv_inst sl_low sr_equp Apron.Tcons1.SUP
      && do_sup sv_inst sl_eqlow sr_equp Apron.Tcons1.SUPEQ in
  let do_ctr sv_inst ctr =
    match ctr with
    | Nc_rand | Nc_bool _ -> { sv_inst with sv_cons = ctr :: sv_inst.sv_cons }
    | Nc_cons (Apron.Tcons1.SUPEQ, Ne_var sl, Ne_var sr) ->
        if do_all_sup sv_inst sl sr then
          { sv_inst with
            sv_equp = IntMap.add sr
              (Ne_var sl :: IntMap.find sr sv_inst.sv_equp) sv_inst.sv_equp;
            sv_eqlow = IntMap.add sl
              (Ne_var sr :: IntMap.find sl sv_inst.sv_eqlow) sv_inst.sv_eqlow }
        else
          { sv_inst with
            sv_cons = ctr :: sv_inst.sv_cons }
    | Nc_cons (Apron.Tcons1.EQ, Ne_var sl, Ne_var sr) ->
        if do_all_sup sv_inst sl sr && do_all_sup sv_inst sr sl then
          let eqs =
            IntMap.add sl (Ne_var sr)
              (IntMap.add sr (Ne_var sl) sv_inst.sv_eqs) in
          { sv_inst with sv_eqs = eqs }
      else { sv_inst with sv_cons = ctr :: sv_inst.sv_cons }
    | _ -> { sv_inst with sv_cons = ctr :: sv_inst.sv_cons } in
  List.fold_left do_ctr { sv_inst with sv_cons = [] } sv_inst.sv_cons

(* Instantiation according to the weakening type of integer parameters *)
let rec typed_sv_instantiation (sv_inst: sv_inst)
    (wktyp: int_wk_typ IntMap.t)
    (is_sat: n_cons -> bool): sv_inst =
  let f_no_fresh e sv_inst =
    Nd_utils.n_expr_fold
      (fun i acc -> not (IntSet.mem i sv_inst.sv_fresh) && acc) e true in
  let sat_min_or_max (is_min: bool) (el: n_expr) (er: n_expr): bool =
    if is_min then
      is_sat (Nc_cons (Apron.Tcons1.SUPEQ,el,er))
    else
      is_sat (Nc_cons (Apron.Tcons1.SUPEQ,er,el)) in
  let rec find_min_or_max (is_min: bool) (e: n_expr) (es: n_expr list)
      (sv_inst: sv_inst): n_expr option =
    match es with
    | [] -> Some e
    | h :: tl ->
        if f_no_fresh h sv_inst then
          if sat_min_or_max is_min h e then
            find_min_or_max is_min e tl sv_inst
          else if sat_min_or_max is_min e h then
            find_min_or_max is_min h tl sv_inst
          else None
        else None in
  let check_min_or_max (is_min: bool) (e: n_expr) (es: n_expr list)
      (sv_inst: sv_inst): bool =
    List.for_all
      (fun ele ->
        if f_no_fresh ele sv_inst then
          if is_min then
            is_sat (Nc_cons (Apron.Tcons1.SUP,ele,e))
          else
            is_sat (Nc_cons (Apron.Tcons1.SUP,e,ele))
        else false
      ) es in
  let f_min_or_max (is_min: bool) (n: int) (sv_inst: sv_inst): sv_inst =
    let e_exprs, o_exprs =
      if is_min then
        IntMap.find n sv_inst.sv_equp, IntMap.find n sv_inst.sv_up
      else
        IntMap.find n sv_inst.sv_eqlow, IntMap.find n sv_inst.sv_low in
    match e_exprs with
    | [] -> sv_inst
    | h :: tl ->
        if f_no_fresh h sv_inst then
          match find_min_or_max is_min h tl sv_inst with
          | None -> sv_inst
          | Some min_e ->
              let f_rename n ex map =
                IntMap.map
                  (List.map
                     (Nd_utils.n_expr_subst
                        (fun i -> if i = n then ex else Ne_var i))) map in
              if check_min_or_max is_min min_e o_exprs sv_inst then
                { sv_inst with
                  sv_ie    = IntSet.add n sv_inst.sv_ie;
                  sv_eqs   = IntMap.add n min_e sv_inst.sv_eqs;
                  sv_low   = f_rename n min_e (IntMap.remove n sv_inst.sv_low);
                  sv_up    = f_rename n min_e (IntMap.remove n sv_inst.sv_up);
                  sv_eqlow = f_rename n min_e
                    (IntMap.remove n sv_inst.sv_eqlow);
                  sv_equp  = f_rename n min_e (IntMap.remove n sv_inst.sv_equp);
                }
              else sv_inst
        else sv_inst in
  let res_sv_inst =
    IntMap.fold
      (fun n t acc ->
        if IntSet.mem n acc.sv_ie then acc
        else
          match t with
          | `Leq -> f_min_or_max false n acc
          | `Geq -> f_min_or_max true n acc
          | _ -> acc
      ) wktyp sv_inst in
  if IntSet.equal res_sv_inst.sv_ie sv_inst.sv_ie then res_sv_inst
  else typed_sv_instantiation res_sv_inst wktyp is_sat

(* Rename left constraints in sv_inst and prove them *)
let prove_sv_cons (sv_inst: sv_inst) (is_sat: n_cons -> bool): sv_inst =
  let cons =
    List.map
      (fun ctr ->
        Nd_utils.n_cons_subst
          (fun i ->
            try IntMap.find i sv_inst.sv_eqs
            with Not_found -> Ne_var i
          ) ctr
      ) sv_inst.sv_cons in
  let cons = List.filter (fun ctr -> not (is_sat ctr)) cons in
  { sv_inst with sv_cons = cons }
