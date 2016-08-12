(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ind_analysis.ml
 **       extracts cstr relations from an inductive
 ** Antoine Toubhans, 2012/04/22 *)
open Data_structures
open Flags
open Lib

open Ast_sig
open Constrain_sig
open Ind_sig
open Off_sig

open Ast_utils
open Constrain_utils

(** To improve:
 **  - fields of cstr_indcall and cstr_segcall could be shared
 **    => because of that, there is a lot of code duplication,
 **    with very similar code for both sets of fields...
 **)


(** Error report *)
module Log =
  Logger.Make(struct let section = "i_ana___" and level = Log_level.DEBUG end)


(** Utilities *)

(* Integration of results; Unsound and Killed mean the analysis bailed out *)
let propagate_status (iname: string) (infos: 'a gen_info StringMap.t) = 
  let info = StringMap.find iname infos in
  match info.status with
  | Unsound -> infos
  | Sound -> (* remove dependence *)
      StringMap.map
        (fun i -> { i with depends = StringSet.remove iname i.depends }) infos
  | Killed -> infos

(* pretty printing, for debugging *)
let pp_gen_info (a_name: string) (a_2stri: string -> 'a -> string) 
    (iname: string) (i: 'a gen_info): unit = 
  Log.info
    "Inductive pre-analysis: %s\n==========================" iname;
  let s =
    match i.status with
    | Sound -> "sound"
    | Unsound -> "unsound"
    | Killed -> "killed" in
  Log.info "\tstatus: %s" s; 
  Log.info "\tdepends: %s" (StringSet.t_2str "," i.depends);
  let s =
    match i.ocstr with
    | None -> "\t  not computed yet\n"
    | Some a -> a_2stri "\t  " a in
  Log.info "\t%s: {\n%s\t}" a_name s

let pp_ind_info = pp_gen_info "cstr_indcall" cstr_indcall_2stri
let pp_seg_info = pp_gen_info "cstr_segcall" cstr_segcall_2stri

(* tools for pre-analysis *)
let get_arg (err: string) (i: int) (l: id list): id =
  List.nthd (fun ( ) -> Log.fatal_exn "args not found: %s" err) l i

let cstri_get_formal_arg (new_vars: id list) (s: cstr_indcall) 
    (fa: formal_arg): id = 
  match fa with
  | `Fa_this      -> s.cstri_main
  | `Fa_var_new i -> get_arg "Fa_var_new" i new_vars 
  | `Fa_par_ptr i -> get_arg "Fa_par_ptr" i s.cstri_ppars 
  | `Fa_par_int i -> get_arg "Fa_par_int" i s.cstri_ipars
  | `Fa_par_set _ -> Log.todo_exn "cstri_get_formal_arg: set type parameter"

let cstrs_get_formal_arg (new_vars: id list) (s: cstr_segcall)
    (fa: formal_arg): id = 
  match fa with
  | `Fa_this      -> s.cstrs_src
  | `Fa_var_new i -> get_arg "Fa_var_new" i new_vars 
  | `Fa_par_ptr i -> get_arg "Fa_par_ptr" i s.cstrs_sppars 
  | `Fa_par_int i -> get_arg "Fa_par_int" i s.cstrs_sipars
  | `Fa_par_set _ -> Log.todo_exn "cstrs_get_formal_arg: set type parameter"

(* reading for inductive preds *)
let cstri_read_aform (a: aform) (new_vars: id list) (s: cstr_indcall): cstr = 
  match a with
  | Af_equal (Ae_var x, Ae_cst 0) 
  | Af_equal (Ae_cst 0, Ae_var x) ->
      let n = cstri_get_formal_arg new_vars s (x :> formal_arg) in
      add_null n s.cstri_cstr
  | Af_equal (Ae_var x, Ae_var y) ->
      let nx = cstri_get_formal_arg new_vars s (x :> formal_arg)  
      and ny = cstri_get_formal_arg new_vars s (y :> formal_arg) in
      add_eq nx ny s.cstri_cstr 
  | Af_equal _ | Af_noteq _ -> s.cstri_cstr

let cstri_read_cell (c: cell) (new_vars: id list) (s: cstr_indcall): cstr = 
  let dst = cstri_get_formal_arg new_vars s (c.ic_dest :> formal_arg)  
  and path = Regular_expr.label c.ic_off in
  add_path s.cstri_main path (Pd_id dst) s.cstri_cstr 

let cstri_read_indcall (i: indcall) (new_vars: id list)
    (si: cstr_indcall) (s: cstr_indcall): cstr = 
  let get_fa = cstri_get_formal_arg new_vars s in
  (* creating the map *)
  let map = PMap.empty in
  (* main id *)
  let nmain = get_fa (i.ii_maina :> formal_arg) in
  let map = PMap.add si.cstri_main nmain map in  
  (* ptr args *)
  let map =
    List.fold_left2
      (fun map si_par n_par -> 
        PMap.add si_par (get_fa (n_par :> formal_arg)) map
      ) map si.cstri_ppars i.ii_argp in 
  (* int args *)
  let map =
    List.fold_left2
      (fun map si_par n_par -> 
        PMap.add si_par (get_fa (n_par :> formal_arg)) map
      ) map si.cstri_ipars i.ii_argi in 
  Constrain_ops.meet_left map si.cstri_cstr s.cstri_cstr

(* reading for segment preds *)
let cstrs_read_aform (a: aform) (new_vars: id list) (s: cstr_segcall): cstr = 
  match a with
  | Af_equal (Ae_var x, Ae_cst 0) 
  | Af_equal (Ae_cst 0, Ae_var x) ->
      let n = cstrs_get_formal_arg new_vars s (x :> formal_arg) in
      add_null n s.cstrs_cstr
  | Af_equal (Ae_var x, Ae_var y) ->
      let nx = cstrs_get_formal_arg new_vars s (x :> formal_arg) 
      and ny = cstrs_get_formal_arg new_vars s (y :> formal_arg) in
      add_eq nx ny s.cstrs_cstr 
  | Af_equal _ | Af_noteq _ -> s.cstrs_cstr

let cstrs_read_cell (c: cell) (new_vars: id list) (s: cstr_segcall): cstr = 
  let dst = cstrs_get_formal_arg new_vars s (c.ic_dest :> formal_arg)
  and path = Regular_expr.label c.ic_off in
  add_path s.cstrs_src path (Pd_id dst) s.cstrs_cstr 

let cstrs_read_indcall (i: indcall) (new_vars: id list)
    (si: cstr_indcall) (s: cstr_segcall): cstr = 
  let get_fa = cstrs_get_formal_arg new_vars s in
  (* creating the map *)
  let map = PMap.empty in
  (* main id *)
  let nmain = get_fa (i.ii_maina :> formal_arg) in
  let map = PMap.add si.cstri_main nmain map in  
  (* ptr args *)
  let map =
    List.fold_left2
      (fun map si_par n_par -> 
        PMap.add si_par (get_fa (n_par :> formal_arg)) map
      ) map si.cstri_ppars i.ii_argp in
  (* int args *)
  let map =
    List.fold_left2
      (fun map si_par n_par -> 
        PMap.add si_par (get_fa (n_par :> formal_arg)) map
      ) map si.cstri_ipars i.ii_argi in 
  Constrain_ops.meet_left map si.cstri_cstr s.cstrs_cstr

let cstrs_read_segcall (i: indcall) (new_vars: id list)
    (si: cstr_segcall) (s: cstr_segcall): cstr = 
  let get_fa = cstrs_get_formal_arg new_vars s in
  (* creating the map *)
  let map = PMap.empty in
  (* src and dst id *)
  let nmain = get_fa (i.ii_maina :> formal_arg) in
  let map = PMap.add si.cstrs_src nmain map in 
  let map = PMap.add si.cstrs_dst s.cstrs_dst map in
  (* ptr args *)
  let map =
    List.fold_left2
      (fun map si_par n_par -> 
        PMap.add si_par (get_fa (n_par :> formal_arg)) map
      ) map si.cstrs_sppars i.ii_argp in 
  let map =
    List.fold_left2
      (fun map si_par s_par -> PMap.add si_par s_par map)
      map si.cstrs_dppars s.cstrs_dppars in 
  (* int args *)
  let map =
    List.fold_left2
      (fun map si_par n_par -> 
        PMap.add si_par (get_fa (n_par :> formal_arg)) map
      ) map si.cstrs_sipars i.ii_argi in 
  let map =
    List.fold_left2 (fun map si_par s_par -> PMap.add si_par s_par map)
      map si.cstrs_dipars s.cstrs_dipars in 
  Constrain_ops.meet_left map si.cstrs_cstr s.cstrs_cstr


(** Set of inductive-inferred predicates *)
let ind_preds: cstr_indcall StringMap.t ref = ref StringMap.empty

let ind_preds_find (indname: string): cstr_indcall = 
  try StringMap.find indname !ind_preds
  with Not_found ->
    Log.fatal_exn "inductive cstr predicates %s not_found" indname

let ind_apply_rule (nb_ipars: int) (nb_ppars: int) (ir: irule)
    (ss: ind_info StringMap.t): cstr_indcall = 
  let s_res, news = Constrain_ops.make_cstri nb_ipars nb_ppars ir.ir_num in
  (* first we read heap part *)
  let s_res =
    List.fold_left
      (fun s_res heap_atom -> 
        let cstr =
          match heap_atom with
          | Hacell c -> cstri_read_cell c news s_res
          | Haind i ->
              begin 
                match (StringMap.find i.ii_ind ss).ocstr with
                | None ->
                    Log.fatal_exn
                      "ind_apply_rule: [ %s ] called cstr not found" i.ii_ind
                | Some cstr_i -> cstri_read_indcall i news cstr_i s_res 
              end in
        { s_res with cstri_cstr = cstr }
      ) s_res ir.ir_heap in
  (* then the pure part *)
  let s_res =
    List.fold_left
      (fun s_res pform_atom -> 
        match pform_atom with
        | Pf_arith a ->
            { s_res with cstri_cstr = cstri_read_aform a news s_res }
        | Pf_set _ | Pf_alloc _ -> s_res (* can't deal with that *))
      s_res ir.ir_pure in
  if !flag_ind_analysis_verbose = Print_all then 
    Log.info "Result apply rule:\n%s" (cstr_2stri "\t" s_res.cstri_cstr);
  (* try to introduce c_paths *)
  let cstri_cstr = Constrain_rules.c_path_intro s_res.cstri_cstr in
  (* try to introduce c_paths *)
  let cstri_cstr = Constrain_rules.d_path_intro cstri_cstr in
  if !flag_ind_analysis_verbose = Print_all then 
    Log.info "Result apply rule [ c-paths introcuded ]:\n%s"
      (cstr_2stri "\t" cstri_cstr);
  (* delete new ids *)
  let cstri_cstr =
    List.fold_left (fun cstr id -> Constrain_rules.forget_id id cstr) 
      cstri_cstr news in
  if !flag_ind_analysis_verbose = Print_all then 
    Log.info "Result apply rule [ intermediate vars removed ]:\n%s"
      (cstr_2stri "\t" cstri_cstr);
  { s_res with cstri_cstr } 

(* initialisation of ind infos *)
let ind_preds_start_analysis (): ind_info StringMap.t = 
  StringMap.fold
    (fun iname ind infos ->
      let depends, term_rules, no_term_rules = 
        List.fold_left
          (fun (depends, term_rules, no_term_rules) irule ->
            let depends, b =
              List.fold_left
                (fun (depends, b) ha ->
                  match ha with 
                  | Hacell _ -> depends, b
                  | Haind ic -> 
                      if String.compare ic.ii_ind iname = 0 then
                        depends, true
                      else
                        StringSet.add ic.ii_ind depends, b
                ) (depends, false) irule.ir_heap in
            if b then (* there is a call to itself *)
              depends, term_rules, (irule::no_term_rules)
            else depends, (irule::term_rules), no_term_rules
          ) (StringSet.empty, [], []) ind.i_rules in
      let info = 
        { n_ipars = ind.i_ipars;
          n_ppars = ind.i_ppars;
          status = Unsound;
          depends;
          ocstr = None;
          term_rules;
          no_term_rules } in
      StringMap.add iname info infos
    ) !Ind_utils.ind_defs StringMap.empty 

let rec ind_preds_do_one (iname: string)
    (infos: ind_info StringMap.t) (iter: int): ind_info StringMap.t = 
  let info = StringMap.find iname infos in
  match info.status with
  | Sound | Killed -> infos 
  | Unsound ->
      if (!flag_ind_analysis_verbose = Print_each_iter 
        || !flag_ind_analysis_verbose = Print_all) then 
        Log.info "iteration <%i> :" iter;
      let info =
        if iter > pl_max_ind_analysis_iter then
          { info with status = Killed } 
        else 
          let status, cstr_i =
            match info.ocstr with
            | Some cstr_i -> 
                let l_cstr_i =
                  List.map 
                    (fun ir ->
                      ind_apply_rule info.n_ipars info.n_ppars ir infos
                    ) info.no_term_rules in
                let cstr_i_post =
                  List.fold_left
                    Constrain_ops.join_cstr_indcall cstr_i l_cstr_i in
                let cstr_i_post = 
                  { cstr_i_post with cstri_cstr = 
                    Constrain_rules.simplify_paths cstr_i_post.cstri_cstr } in
                let a =
                  if Constrain_ops.is_le_cstr_indcall cstr_i_post cstr_i then 
                    Sound
                  else
                    Unsound in
                a, cstr_i_post
            | None -> 
                let l_cstr_i =
                  List.map 
                    (fun ir ->
                      ind_apply_rule info.n_ipars info.n_ppars ir infos) 
                    info.term_rules in
                Unsound,
                Constrain_ops.join_cstr_indcall_list l_cstr_i in
          { n_ipars = info.n_ipars;
            n_ppars = info.n_ppars;
            status;
            depends = info.depends;
            ocstr = Some cstr_i;
            term_rules = info.term_rules;
            no_term_rules = info.no_term_rules } in
      if (!flag_ind_analysis_verbose = Print_each_iter
        || !flag_ind_analysis_verbose = Print_all) then
        pp_ind_info iname info;
      let infos = StringMap.add iname info infos in
      let infos = propagate_status iname infos in
      (* reccursive call *)
      ind_preds_do_one iname infos (iter+1) 

let ind_preds_init (): unit = 
  let infos = ind_preds_start_analysis () in
  if !flag_ind_analysis_verbose = Print_all then 
    begin 
      Log.info "*** Starting inductive pre-analysis ***";
      StringMap.iter pp_ind_info infos
    end;
  let rec aux pendant infos = 
    let pendant_post, infos =
      StringMap.fold
        (fun iname info (pendant, infos) ->
          if StringSet.is_empty info.depends then
            pendant, ind_preds_do_one iname infos 0
          else
            pendant+1, infos
        ) infos (0, infos) in
    if pendant_post = 0 then infos
    else if pendant_post < pendant then aux pendant_post infos
    else Log.fatal_exn "ind_preds_init: can not resolve dependancies" in
  let infos = aux (StringMap.cardinal infos) infos in
  (* write the found preds in ind_preds meta variable *)
  StringMap.iter
    (fun iname info -> 
      if info.status = Sound then 
        match info.ocstr with
        | None -> Log.fatal_exn "ind_preds_init: shall not happen"
        | Some cstr_i -> ind_preds := StringMap.add iname cstr_i !ind_preds
    ) infos;
  Log.info "Inductive pre-analysis finished!";  
  if !flag_ind_analysis_verbose != No_verbose then 
    StringMap.iter
      (fun iname cstr_i -> 
        Log.info "Inductive %s:\n\t{\n%s\t}" 
          iname (cstr_indcall_2stri "\t  " cstr_i)
      ) !ind_preds
(** Set of segment-inferred predicates *)
let seg_preds: cstr_segcall StringMap.t ref = ref StringMap.empty

let seg_preds_find (indname: string): cstr_segcall = 
  try StringMap.find indname !seg_preds
  with Not_found ->
    Log.fatal_exn "segment cstr predicates %s not_found" indname

let seg_apply_term_rule (nb_ipars: int) (nb_ppars: int): cstr_segcall =
  let t, _ = Constrain_ops.make_cstrs nb_ipars nb_ppars 0 in
  let cstr = t.cstrs_cstr in
  let cstr = add_eq t.cstrs_src t.cstrs_dst cstr in
  let cstr =
    List.fold_left2 (fun cstr cstrpar dppar -> add_eq cstrpar dppar cstr)
      cstr t.cstrs_sppars t.cstrs_dppars in
  let cstr =
    List.fold_left2 (fun cstr sipar dipar -> add_eq sipar dipar cstr)
      cstr t.cstrs_sipars t.cstrs_dipars in
  { t with cstrs_cstr = cstr }

let seg_apply_rule (iname: string) (nb_ipars: int) (nb_ppars: int) 
    (ir: irule) (t_prev: cstr_segcall): cstr_segcall list = 
  let t, news = Constrain_ops.make_cstrs nb_ipars nb_ppars ir.ir_num in
  (* first we read heap part *)
  let t, selfcalls =
    List.fold_left
      (fun (t, selfcalls) heap_atom -> 
        match heap_atom with
        | Hacell c ->
            { t with cstrs_cstr = cstrs_read_cell c news t }, selfcalls
        | Haind i -> 
            let icname = i.ii_ind in
            if iname = icname then t, i::selfcalls
            else
              let cstrc = ind_preds_find icname in
              let cstrs_cstr = cstrs_read_indcall i news cstrc t in
              { t with cstrs_cstr }, selfcalls
      ) (t, []) ir.ir_heap in
  (* then the pure part *)
  let t =
    List.fold_left
      (fun t pform_atom -> 
        match pform_atom with
        | Pf_arith a -> { t with cstrs_cstr = cstrs_read_aform a news t }
        | Pf_set _ | Pf_alloc _ -> t (* can't deal with that *)
      ) t ir.ir_pure in
  (* dealing self calls *)
  let self_cstri = ind_preds_find iname in
  let _, lt =
    List.fold_left
      (fun (ti, lt) i -> 
        let lt_cstr = List.map (cstrs_read_indcall i news self_cstri) lt in
        let lt_cstr = (cstrs_read_segcall i news t_prev ti)::lt_cstr in
        let lt = List.map (fun cstrs_cstr -> { t with cstrs_cstr }) lt_cstr in
        let cstrs_cstr = cstrs_read_indcall i news self_cstri ti in
        let ti = { ti with cstrs_cstr } in
        ti, lt
      ) (t, []) selfcalls in
  (* try to introduce c_paths *)
  let lt =
    List.map
      (fun t ->
        let cstrs_cstr = Constrain_rules.c_path_intro t.cstrs_cstr in
        let cstrs_cstr = Constrain_rules.d_path_intro cstrs_cstr in
        { t with cstrs_cstr }
      ) lt in
  if !flag_ind_analysis_verbose = Print_all then 
    List.iter
      (fun t ->
        Log.info "Result apply rule [ c-paths introcuded ]:\n%s"
          (cstr_2stri "\t" t.cstrs_cstr)
      ) lt;
  (* delete new ids *)
  let lt =
    List.map
      (fun t -> 
        let cstrs_cstr =
          List.fold_left 
            (fun cstr id -> Constrain_rules.forget_id id cstr)
            t.cstrs_cstr news in
        { t with cstrs_cstr }
      ) lt in
  if !flag_ind_analysis_verbose = Print_all then 
    List.iter (fun t ->
      Log.info "Result apply rule [ intermediate vars removed ]:\n%s"
        (cstr_2stri "\t" t.cstrs_cstr)) lt;
  lt

let seg_preds_start_analysis (): seg_info StringMap.t = 
  StringMap.fold
    (fun iname ind infos ->
      let depends, term_rules, no_term_rules = 
        List.fold_left
          (fun (depends, term_rules, no_term_rules) irule ->
            let depends, b =
              List.fold_left
                (fun (depends, b) ha ->
                  match ha with 
                  | Hacell _ -> depends, b
                  | Haind ic -> 
                      if String.compare ic.ii_ind iname = 0 then
                        depends, true
                      else  
                        StringSet.add ic.ii_ind depends, b
                ) (depends, false) irule.ir_heap in
            if b then (* there is a call to itself *)
              depends, term_rules, (irule::no_term_rules)
            else depends, (irule::term_rules), no_term_rules
          ) (StringSet.empty, [], []) ind.i_rules in
      let info = 
        { n_ipars = ind.i_ipars;
          n_ppars = ind.i_ppars;
          status = Unsound;
          depends;
          ocstr = None;
          term_rules;
          no_term_rules } in
      StringMap.add iname info infos
    ) !Ind_utils.ind_defs StringMap.empty 

let rec seg_preds_do_one (iter: int) (iname: string)
    (info: seg_info): seg_info = 
  match info.status with
  | Sound | Killed -> info 
  | Unsound -> 
      if (!flag_ind_analysis_verbose = Print_each_iter
        || !flag_ind_analysis_verbose = Print_all) then
        Log.info "iteration <%i> :" iter;
      let info =
        if iter > pl_max_ind_analysis_iter then { info with status = Killed } 
        else
          match info.ocstr with
          | None -> 
              let cstrs = seg_apply_term_rule info.n_ipars info.n_ppars in
              let ocstr = Some cstrs in
              { info with ocstr }
          | Some cstrs ->
              let ll_cstrs = 
                List.map (fun ir -> 
                  seg_apply_rule iname info.n_ipars info.n_ppars ir cstrs)
                  info.no_term_rules in 
              let l_cstrs =
                List.map Constrain_ops.join_cstr_segcall_list ll_cstrs in
              let cstrs_post =
                List.fold_left Constrain_ops.join_cstr_segcall cstrs l_cstrs in
              let cstrs_post =
                let cstr =
                  Constrain_rules.simplify_paths cstrs_post.cstrs_cstr in
                { cstrs_post with cstrs_cstr = cstr } in
              let ocstr = Some cstrs_post in
              let info = { info with ocstr } in
              if Constrain_ops.is_le_cstr_segcall cstrs_post cstrs then
                { info with status = Sound }
              else
                info in
      if (!flag_ind_analysis_verbose = Print_each_iter 
        || !flag_ind_analysis_verbose = Print_all) then 
        pp_seg_info iname info;
      (* reccursive call *)
      seg_preds_do_one (iter+1) iname info

let seg_preds_init (): unit = 
  let infos = seg_preds_start_analysis () in
  if !flag_ind_analysis_verbose = Print_all then 
    begin 
      Log.info "*** Starting inductive pre-analysis ***";
      StringMap.iter pp_seg_info infos
    end;
  let infos = StringMap.mapi (seg_preds_do_one 0) infos in
  (* write the found preds in ind_preds meta variable *)
  StringMap.iter
    (fun iname info -> 
      if info.status = Sound then 
        match info.ocstr with
        | None -> Log.fatal_exn "seg_preds_init: shall not happen"
        | Some cstr_s -> seg_preds := StringMap.add iname cstr_s !seg_preds
    ) infos;
  Log.info "Segment pre-analysis finished!";
  if !flag_ind_analysis_verbose != No_verbose then
    StringMap.iter 
      (fun iname cstr_s ->
        Log.info "Segment %s:\n\t{\n%s\t}"
          iname (cstr_segcall_2stri "\t  " cstr_s)
      ) !seg_preds
