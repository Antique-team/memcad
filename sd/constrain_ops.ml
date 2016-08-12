(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: constrain_ops.ml
 **       . meet_left algorithms
 **       . is_le algorithms
 **       . join algorithms
 ** Antoine Toubhans, 2012/04/22 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig
open Ind_sig
open Constrain_sig
open Constrain_utils


(** Error report *)
module Log =
  Logger.Make(struct let section = "ctrn_ops" and level = Log_level.DEBUG end)


(* id_mapping utilitary functions *)
let id_map_empty (): id_mapping = 
  { nm_left = PMap.empty;
    nm_right = PMap.empty;
    nm_rev = PMap.empty }

let id_map_add (n_left: id) (n_right: id) (n: id) 
    (map: id_mapping): id_mapping = 
  { nm_left = PMap.add n_left n map.nm_left;
    nm_right = PMap.add n_right n map.nm_right;
    nm_rev = PMap.add n (n_left, n_right) map.nm_rev }

(* todo: do I need this? *)
let id_map_left_right (n_l: id) (map: id_mapping): id = 
  try 
    let n = PMap.find n_l map.nm_left in
    snd (PMap.find n map.nm_rev)
  with Not_found -> Log.fatal_exn "id_map_left_right: can't find the node"

(* todo: do I need this? *)    
let id_map_right_left (n_r: id) (map: id_mapping): id = 
  try 
    let n = PMap.find n_r map.nm_right in
    fst (PMap.find n map.nm_rev)
  with Not_found -> Log.fatal_exn "id_map_right_left: can't find the node"

(* comparison operator functions *)
let c_path_is_le (c1: c_path) (c2: c_path) (t: cstr): bool =   
  are_destination_eq c1.cp_prop_dst c2.cp_prop_dst t
    && Regular_expr.eq c1.cp_induc_path c2.cp_induc_path
    && Regular_expr.is_le c1.cp_prop_path c2.cp_prop_path
    &&
  PSet.for_all
    (fun tgt1 ->
      (PSet.exists
        (fun tgt2 -> are_id_eq tgt1 tgt2 t) c2.cp_targets
     || (is_id_null tgt1 t && c2.cp_target_null))
    ) c1.cp_targets
    && (not c1.cp_target_null || c2.cp_target_null) 

(* map is assumed to be a complete mapping from right-id to left-id  *)
let is_le (map: (id, id) PMap.t) (t_left: cstr) (t_right: cstr): bool =
  (* auxiliary function  *)
  let rec aux l_set r_set =
    if PSet.is_empty r_set then true
    else
      let r = PSet.choose r_set in
      if PSet.mem (PMap.find r map) l_set then
        aux l_set (PSet.remove r r_set) 
      else false in
  (* match all r-paths to some l-path *)
  for_all_node
    (fun n_right no_right -> 
      let n_left = PMap.find n_right map in
      for_all_paths
        (fun p dst_right -> 
          let dst_left =
            match dst_right with
            | Pd_null -> Pd_null
            | Pd_id dst_right -> Pd_id (PMap.find dst_right map) in
          is_there_path n_left p dst_left t_left
        ) no_right
    ) t_right 
    (* eq-classes *)
    && aux t_left.eq_class.null_cl t_right.eq_class.null_cl
    &&
  IntMap.for_all
    (fun i r_cl -> 
      if PSet.is_empty r_cl then true else
      let r = PSet.choose r_cl in
      let l = PMap.find r map in
      let eq_loc = (get_node l t_left).n_eqs in
      let l_cl = eq_class_find eq_loc t_left.eq_class in
      aux l_cl r_cl
    ) t_right.eq_class.cl
    (* c_paths *)
    &&
  for_all_node
    (fun n_r no_r -> 
      let n_l = PMap.find n_r map in
      let no_l = get_node n_l t_left in
      for_all_c_paths
        (fun cp_r -> 
          let cp_rl = c_path_map (fun x -> PMap.find x map) cp_r in
          not (for_all_c_paths
                 (fun cp_l -> not (c_path_is_le cp_l cp_rl t_left)) no_l)
        ) no_r
    ) t_right
    (* d_paths *)
    &&
  for_all_node
    (fun n_r no_r -> 
      let n_l = PMap.find n_r map in
      let no_l = get_node n_l t_left in
      for_all_d_paths
        (fun dp_r -> 
          let dp_rl = d_path_map (fun x -> PMap.find x map) dp_r in
          not (for_all_d_paths (fun dp_l -> not (d_path_eq dp_l dp_rl)) no_l)
        ) no_r
    ) t_right

(* meeting functions *)
let meet_left (map: (id, id) PMap.t) (t_left: cstr) (t: cstr): cstr = 
  if pl_do_sanity_check_before then 
    begin
      sanity_check "meet_left, left" t_left;    
      sanity_check "meet_left" t
    end;
  let aux_add_map l_id map t = 
    try PMap.find l_id map, t, map
    with Not_found -> 
      let id, t = create_fresh_node t in
      id, t, PMap.add l_id id map in 
  let map, t =
    PMap.fold
      (fun l_src l_nsrc (map, t) -> 
        let src, t, map = aux_add_map l_src map t in
        fold_fw_paths
          (fun p l_dst (map, t) ->
            match l_dst with
            | Pd_null -> map, add_path src p Pd_null t
            | Pd_id l_dst -> 
                let dst, t, map = aux_add_map l_dst map t in
                map, add_path src p (Pd_id dst) t) l_nsrc (map, t)
      ) t_left.nodes (map, t) in 
  let map, t =
    PSet.fold
      (fun l_n (map, t) -> 
        let n, t, map = aux_add_map l_n map t in
        map, add_null n t
      ) t_left.eq_class.null_cl (map, t) in
  (* dealing with c-paths *)
  let map, t =
    PMap.fold
      (fun src_l nsrc_l (map, t) ->
        let src, t, map = aux_add_map src_l map t in
        fold_c_paths
          (fun cp_l (map, t) -> 
            let map, t, cp_targets =
              PSet.fold 
                (fun i_l (map, t, s) -> 
                  let i, t, map = aux_add_map i_l map t in
                  map, t, PSet.add i s
                ) cp_l.cp_targets (map, t, PSet.empty) in
            let map, t, cp_prop_dst =
              match cp_l.cp_prop_dst with
              | Pd_null -> map, t, Pd_null
              | Pd_id x_l -> 
                  let x, t, map = aux_add_map x_l map t in
                  map, t, Pd_id x in
            let cp =
              { cp_targets;
                cp_target_null = cp_l.cp_target_null;
                cp_induc_path = cp_l.cp_induc_path;
                cp_prop_path = cp_l.cp_prop_path;
                cp_prop_dst } in
            map, add_c_path src cp t
          ) nsrc_l (map, t)
      ) t_left.nodes (map, t) in      
  (* dealing with d-paths *)
  let map, t =
    PMap.fold
      (fun src_l nsrc_l (map, t) ->
        let src, t, map = aux_add_map src_l map t in
        fold_d_paths
          (fun dp_l (map, t) -> 
            let map, t, dp_targets =
              PSet.fold 
                (fun (i_l, j_l) (map, t, s) -> 
                  let i, t, map = aux_add_map i_l map t in
                  let j, t, map = aux_add_map j_l map t in
                  map, t, PSet.add (i, j) s
                ) dp_l.dp_targets (map, t, PSet.empty) in
            let dp_bw_target, t, map = 
              aux_add_map dp_l.dp_bw_target map t in
            let dp = { dp_bw_target;
                       dp_fw_induc = dp_l.dp_fw_induc;
                       dp_bw_induc = dp_l.dp_bw_induc;
                       dp_targets } in
            map, add_d_path src dp t
          ) nsrc_l (map, t)
      ) t_left.nodes (map, t) in      
  (* dealing with eq classes *)
  (* brutal code, consider doing sthg better here *)
  fold_eq_class
    (fun n1_l n2_l t -> 
      let n1, t, map = aux_add_map n1_l map t in
      let n2, t, map = aux_add_map n2_l map t in
      add_eq n1 n2 t)
    (fun n_l t -> 
      let n, t, map = aux_add_map n_l map t in
      add_null n t)
    t_left.eq_class t
    
let path_join (p_left: path) (p_right: path): path = 
  Regular_expr.plus p_left p_right

let c_path_join (map: id_mapping) (cl: c_path) (cr: c_path): c_path option =
  let prop_dst_l =
    match cl.cp_prop_dst with
    | Pd_id x -> Pd_id (PMap.find x map.nm_left)
    | Pd_null -> Pd_null
  and prop_dst_r =
    match cr.cp_prop_dst with
    | Pd_id x -> Pd_id (PMap.find x map.nm_right)
    | Pd_null -> Pd_null in
  if destination_eq prop_dst_l prop_dst_r
    && Regular_expr.eq cl.cp_induc_path cr.cp_induc_path then 
    let cp_targets0 =
      PSet.fold (fun nl -> PSet.add (PMap.find nl map.nm_left)) 
        cl.cp_targets PSet.empty in
    let cp_targets =
      PSet.fold (fun nr -> PSet.add (PMap.find nr map.nm_right)) 
        cr.cp_targets cp_targets0 in
    let cp ={ cp_targets;
              cp_target_null = cl.cp_target_null || cr.cp_target_null;
              cp_induc_path = cl.cp_induc_path;
              cp_prop_path = Regular_expr.simplify 
                (Regular_expr.plus cl.cp_prop_path cr.cp_prop_path);
              cp_prop_dst = prop_dst_l } in
    Some cp
  else None

let c_path_join_eq_left (map: id_mapping): c_path -> c_path =
  c_path_map (fun nl -> PMap.find nl map.nm_left)

let c_path_join_eq_right (map: id_mapping): c_path -> c_path =
  c_path_map (fun nr -> PMap.find nr map.nm_right)

let d_path_join (map: id_mapping) (dl: d_path) (dr: d_path): d_path option =
  let ddl = d_path_map (fun nl -> PMap.find nl map.nm_left) dl
  and ddr = d_path_map (fun nr -> PMap.find nr map.nm_right) dr in
  if d_path_eq ddl ddr then Some ddl else None

let d_path_join_eq_left (map: id_mapping): d_path -> d_path =
  d_path_map (fun nl -> PMap.find nl map.nm_left)

let d_path_join_eq_right (map: id_mapping): d_path -> d_path =
  d_path_map (fun nr -> PMap.find nr map.nm_right)

(* we assume the mapping to be complete *)
let join (map: id_mapping) (t_left: cstr) (t_right: cstr) 
    (t_init: cstr): cstr =
  (* saturates equality classes *)
  let t_left = Constrain_rules.all_satur_null t_left 
  and t_right = Constrain_rules.all_satur_null t_right in
  let t_left = Constrain_rules.all_satur_eqs t_left 
  and t_right = Constrain_rules.all_satur_eqs t_right in
  let t_left = Constrain_rules.all_modus_ponens_paths t_left 
  and t_right = Constrain_rules.all_modus_ponens_paths t_right in
  let t_left = Constrain_rules.all_modus_ponens_c_paths t_left 
  and t_right = Constrain_rules.all_modus_ponens_c_paths t_right in
  (* first we try to join: 
   * - left paths with right paths 
   * - left paths with right eq   *)
  let t =
    PMap.fold 
      (fun src_left nsrc_left t -> 
        let src = PMap.find src_left map.nm_left in
        let src_right = snd (PMap.find src map.nm_rev) in
        let nsrc_right = get_node src_right t_right in
        fold_fw_paths
          (fun p_left dst_left t -> 
            let dst_right, dst =
              match dst_left with
              | Pd_id dst_left -> 
                  let dst = PMap.find dst_left map.nm_left in
                  let dst_right = snd (PMap.find dst map.nm_rev) in
                  Pd_id dst_right, Pd_id dst
              | Pd_null -> Pd_null, Pd_null in
            (* with r-paths *)
            let t =
              fold_fw_paths
                (fun p_right dst_r_candidate t -> 
                  if destination_eq dst_right dst_r_candidate then
                    let p = path_join p_left p_right in
                    add_path src p dst t
                  else t
                ) nsrc_right t in
            (* with r-eq *)
            if are_destination_eq (Pd_id src_right) dst_right t_right then
              let p = path_join p_left Regular_expr.one in
              add_path src p dst t
            else t
          ) nsrc_left t
      ) t_left.nodes t_init in   
  (* then, we try to join;
   * - left-eq with right path *)
  let t =
    PMap.fold 
      (fun src_right nsrc_right t -> 
        let src = PMap.find src_right map.nm_right in
        let src_left = snd (PMap.find src map.nm_rev) in
        fold_fw_paths
          (fun p_right dst_right t -> 
            let dst_left, dst =
              match dst_right with
              | Pd_id dst_right -> 
                  let dst = PMap.find dst_right map.nm_right in
                  let dst_left = snd (PMap.find dst map.nm_rev) in
                  Pd_id dst_left, Pd_id dst
              | Pd_null -> Pd_null, Pd_null in
            if are_destination_eq (Pd_id src_left) dst_left t_left then
              let p = path_join p_right Regular_expr.one in
              add_path src p dst t
            else t
          ) nsrc_right t
      ) t_right.nodes t in   
  (* then, we treat c_paths :
   * . left-c-path with right-c-path *)
  let t =
    PMap.fold 
      (fun n_left no_left t -> 
        let n = PMap.find n_left map.nm_left in
        let n_right = snd (PMap.find n map.nm_rev) in
        let no_right = get_node n_right t_right in
        fold_c_paths
          (fun c_left t -> 
            fold_c_paths
              (fun c_right t -> 
                match c_path_join map c_left c_right with
                | Some c -> add_c_path n c t
                | None -> t
              ) no_right t
          ) no_left t
      ) t_left.nodes t in    
  (* then, we treat c_paths :
   * . left-c-path with right-eq *)
  let t =
    PMap.fold 
      (fun n_left no_left t -> 
        let n = PMap.find n_left map.nm_left in
        let n_right = snd (PMap.find n map.nm_rev) in
        fold_c_paths
          (fun c_left t ->
            let b0 =
              PSet.exists 
                (fun tgt_left ->
                  let tgt_right = id_map_left_right tgt_left map in
                  are_id_eq tgt_right n_right t_right) 
                c_left.cp_targets in
            if b0 || (c_left.cp_target_null && is_id_null n_right t_right) then
              let c = c_path_join_eq_left map c_left in
              add_c_path n c t
            else t
          ) no_left t
      ) t_left.nodes t in
  (* then, we treat d_paths :
   * . left-eq with right-c-path *)
  let t =
    PMap.fold 
      (fun n_right no_right t -> 
        let n = PMap.find n_right map.nm_right in
        let n_left = snd (PMap.find n map.nm_rev) in
        fold_c_paths
          (fun c_right t ->
            let b0 =
              PSet.exists
                (fun tgt_right ->
                  let tgt_left = id_map_right_left tgt_right map in
                  are_id_eq tgt_left n_left t_left
                ) c_right.cp_targets in
            if b0 || (c_right.cp_target_null && is_id_null n_left t_left) then
              let c = c_path_join_eq_right map c_right in
              add_c_path n c t
            else t
          ) no_right t
      ) t_right.nodes t in
  (* then, we treat c_paths :
   * . left-d-path with right-d-path *)
  let t =
    PMap.fold 
      (fun n_left no_left t -> 
        let n = PMap.find n_left map.nm_left in
        let n_right = snd (PMap.find n map.nm_rev) in
        let no_right = get_node n_right t_right in
        fold_d_paths
          (fun d_left t -> 
            fold_d_paths
              (fun d_right t -> 
                match d_path_join map d_left d_right with
                | Some d -> add_d_path n d t
                | None -> t
              ) no_right t
          ) no_left t
      ) t_left.nodes t in    
  (* then, we treat d_paths :
   * . left-d-path with right-eq *)
  let t =
    PMap.fold 
      (fun n_left no_left t -> 
        let n = PMap.find n_left map.nm_left in
        let n_right = snd (PMap.find n map.nm_rev) in
        fold_d_paths
          (fun d_left t ->
            let bw_tgt_l = d_left.dp_bw_target in
            let bw_tgt_r = id_map_left_right bw_tgt_l map in
            let b0 =
              PSet.exists 
                (fun (tgt1_l, tgt2_l) ->
                  let tgt1_r = id_map_left_right tgt1_l map 
                  and tgt2_r = id_map_left_right tgt2_l map in
                  are_id_eq tgt1_r bw_tgt_r t_right
                    && are_id_eq tgt2_r n_right t_right
                ) d_left.dp_targets in
            if b0 || (is_id_null n_right t_right) then
              let d = d_path_join_eq_left map d_left in
              add_d_path n d t
            else t
          ) no_left t
      ) t_left.nodes t in
  (* then, we treat d_paths :
   * . left-eq with right-d-path *)
  let t =
    PMap.fold 
      (fun n_right no_right t -> 
        let n = PMap.find n_right map.nm_right in
        let n_left = snd (PMap.find n map.nm_rev) in
        fold_d_paths
          (fun d_right t ->
            let bw_tgt_r = d_right.dp_bw_target in
            let bw_tgt_l = id_map_right_left bw_tgt_r map in
            let b0 =
              PSet.exists 
                (fun (tgt1_r, tgt2_r) ->
                  let tgt1_l = id_map_right_left tgt1_r map 
                  and tgt2_l = id_map_right_left tgt2_r map in
                  are_id_eq tgt1_l bw_tgt_l t_left
                    && are_id_eq tgt2_l n_left t_left
                ) d_right.dp_targets in
            if b0 || (is_id_null n_left t_left) then 
              let d = d_path_join_eq_right map d_right in
              add_d_path n d t
            else t
          ) no_right t
      ) t_right.nodes t in
  (* then, we join left and right eq *)
  (* todo: this code is a bit brutal, I shall consider 
   * perfoming the join as a straight operation over 
   * eq classes *)
  fold_eq_class 
    (fun n1_l n2_l t -> 
      let n1 = PMap.find n1_l map.nm_left 
      and n2 = PMap.find n2_l map.nm_left in
      let n1_r = snd (PMap.find n1 map.nm_rev) 
      and n2_r = snd (PMap.find n2 map.nm_rev) in
      if are_id_eq n1_r n2_r t_right then add_eq n1 n2 t
      else t) 
    (fun n_l t ->
      let n = PMap.find n_l map.nm_left in
      let n_r = snd (PMap.find n map.nm_rev) in 
      if is_id_null n_r t_right then add_null n t
      else t)
    t_left.eq_class t


(* inductive *)
let make_cstri (nb_ipars: int) (nb_ppars: int) 
    (nb_news: int): cstr_indcall * id list = 
  let cstri_cstr = top() in
  let cstri_main, cstri_cstr = create_fresh_node cstri_cstr in
  let cstri_ppars, cstri_cstr = create_nfresh_nodes nb_ppars cstri_cstr in
  let cstri_ipars, cstri_cstr = create_nfresh_nodes nb_ipars cstri_cstr in
  let news, cstri_cstr = create_nfresh_nodes nb_news cstri_cstr in
  let s_res = { cstri_cstr; cstri_main; cstri_ppars; cstri_ipars } in
  s_res, news

let is_le_cstr_indcall (t_left: cstr_indcall) (t_right: cstr_indcall): bool = 
  try 
    let map = PMap.empty in
    let map = PMap.add t_right.cstri_main t_left.cstri_main map in  
    let map =
      List.fold_left2 (fun map nr nl -> PMap.add nr nl map)
        map t_right.cstri_ppars t_left.cstri_ppars in
    let map =
      List.fold_left2 (fun map nr nl -> PMap.add nr nl map)
        map t_right.cstri_ipars t_left.cstri_ipars in
    is_le map t_left.cstri_cstr t_right.cstri_cstr
  with Invalid_argument _ -> 
    Log.fatal_exn "is_le_cstr_indcall: not the same number of parameters"

let join_cstr_indcall (t_left: cstr_indcall) (t_right: cstr_indcall): cstr_indcall = 
  if flag_debug_pl_join then 
    Log.force "Joining cstr for inductives\nLeft:\n%sRight:\n%s"
      (cstr_indcall_2stri "\t" t_left)
      (cstr_indcall_2stri "\t" t_right);
  let nb_ppars_left = List.length t_left.cstri_ppars
  and nb_ppars_right = List.length t_right.cstri_ppars
  and nb_ipars_left = List.length t_left.cstri_ipars
  and nb_ipars_right = List.length t_right.cstri_ipars in
  let nb_ppars = 
    if nb_ppars_left = nb_ppars_right then nb_ppars_left
    else
      Log.fatal_exn
        "can't compute cstr_indcall join: not the same num of ppars" 
  and nb_ipars = 
    if nb_ipars_left = nb_ipars_right then nb_ipars_left
    else
      Log.fatal_exn
        "can't compute cstr_indcall join: not the same num of ipars" in
  let t, _ = make_cstri nb_ipars nb_ppars 0 in
  (* building map *)
  let map = id_map_empty () in
  let map = id_map_add t_left.cstri_main t_right.cstri_main t.cstri_main map in
  let rec aux map ll lr ln =
    match ll, lr, ln with
    | nl::ll, nr::lr, n::ln -> aux (id_map_add nl nr n map) ll lr ln
    | [], [], [] -> map
    | _ ->
        Log.fatal_exn "join_cstr_indcall: inconsistant number of arguments" in
  let map = aux map t_left.cstri_ppars t_right.cstri_ppars t.cstri_ppars in
  let map = aux map t_left.cstri_ipars t_right.cstri_ipars t.cstri_ipars in
  if flag_debug_pl_join then
    Log.force "%s" (id_mapping_2stri "" map);
  (* join of the cstr part *)
  let cstri_cstr = join map t_left.cstri_cstr t_right.cstri_cstr t.cstri_cstr in
  let t = { t with cstri_cstr } in
  if flag_debug_pl_join then 
    Log.force "Result:\n%s" (cstr_indcall_2stri "\t" t);
  t

let join_cstr_indcall_list (l: cstr_indcall list): cstr_indcall = 
  if l = [] then Log.fatal_exn "join_cstr_indcall_list called to the empty list"
  else List.fold_left join_cstr_indcall (List.hd l) (List.tl l)


(* segment *)
let make_cstrs (nb_ipars: int) (nb_ppars: int) 
    (nb_news: int): cstr_segcall * id list = 
  let cstrs_cstr = top() in
  let cstrs_src, cstrs_cstr = create_fresh_node cstrs_cstr in
  let cstrs_sppars, cstrs_cstr = create_nfresh_nodes nb_ppars cstrs_cstr in
  let cstrs_sipars, cstrs_cstr = create_nfresh_nodes nb_ipars cstrs_cstr in
  let cstrs_dst, cstrs_cstr = create_fresh_node cstrs_cstr in
  let cstrs_dppars, cstrs_cstr = create_nfresh_nodes nb_ppars cstrs_cstr in
  let cstrs_dipars, cstrs_cstr = create_nfresh_nodes nb_ipars cstrs_cstr in
  let news, cstrs_cstr = create_nfresh_nodes nb_news cstrs_cstr in
  { cstrs_cstr;
    cstrs_src; cstrs_sppars; cstrs_sipars;
    cstrs_dst; cstrs_dppars; cstrs_dipars }, news

let is_le_cstr_segcall (t_left: cstr_segcall) (t_right: cstr_segcall): bool = 
  try 
    let map = PMap.empty in
    let map = PMap.add t_right.cstrs_src t_left.cstrs_src map in  
    let map =
      List.fold_left2
        (fun map nr nl -> PMap.add nr nl map)
        map t_right.cstrs_sppars t_left.cstrs_sppars in
    let map =
      List.fold_left2
        (fun map nr nl -> PMap.add nr nl map)
        map t_right.cstrs_sipars t_left.cstrs_sipars in
    let map = PMap.add t_right.cstrs_dst t_left.cstrs_dst map in  
    let map =
      List.fold_left2
        (fun map nr nl -> PMap.add nr nl map)
        map t_right.cstrs_dppars t_left.cstrs_dppars in
    let map =
      List.fold_left2
        (fun map nr nl -> PMap.add nr nl map)
        map t_right.cstrs_dipars t_left.cstrs_dipars in
    is_le map t_left.cstrs_cstr t_right.cstrs_cstr
  with Invalid_argument _ -> 
    Log.fatal_exn "is_le_cstr_segcall: not the same number of parameters"


let join_cstr_segcall (t_left: cstr_segcall) (t_right: cstr_segcall): cstr_segcall = 
  if flag_debug_pl_join then 
    Log.force "Joining cstr for segments\nLeft:\n%sRight:\n%s"
      (cstr_segcall_2stri "\t" t_left)
      (cstr_segcall_2stri "\t" t_right);
  let nb_ppars = List.length t_left.cstrs_sppars
  and nb_ipars = List.length t_left.cstrs_sipars in
  let t, _ = make_cstrs nb_ipars nb_ppars 0 in
  (* building map *)
  let map = id_map_empty () in
  let map = id_map_add t_left.cstrs_src t_right.cstrs_src t.cstrs_src map in
  let map = id_map_add t_left.cstrs_dst t_right.cstrs_dst t.cstrs_dst map in
  let rec aux map ll lr ln =
    match ll, lr, ln with
    | nl::ll, nr::lr, n::ln -> aux (id_map_add nl nr n map) ll lr ln
    | [], [], [] -> map
    | _ ->
        Log.fatal_exn "join_cstr_segcall: inconsistant number of arguments" in
  let map = aux map t_left.cstrs_sppars t_right.cstrs_sppars t.cstrs_sppars in
  let map = aux map t_left.cstrs_sipars t_right.cstrs_sipars t.cstrs_sipars in
  let map = aux map t_left.cstrs_dppars t_right.cstrs_dppars t.cstrs_dppars in
  let map = aux map t_left.cstrs_dipars t_right.cstrs_dipars t.cstrs_dipars in
  if flag_debug_pl_join then 
    Log.force "%s" (id_mapping_2stri "" map);
  (* join of the cstr part *)
  let cstrs_cstr = join map t_left.cstrs_cstr t_right.cstrs_cstr t.cstrs_cstr in
  let t = { t with cstrs_cstr } in
  if flag_debug_pl_join then 
    Log.force "Result:\n%s" (cstr_segcall_2stri "\t" t);
  t



let join_cstr_segcall_list (l: cstr_segcall list): cstr_segcall = 
  if l = [] then Log.fatal_exn "join_cstr_segcall_list called to the empty list"
  else List.fold_left join_cstr_segcall (List.hd l) (List.tl l)
