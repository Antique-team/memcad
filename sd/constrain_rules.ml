(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: constrain_rules.ml
 **       sound reduction rules
 ** Antoine Toubhans, 2012/04/19 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig
open Constrain_sig
open Constrain_utils
open Statistics

(* To-do:
 *  - add some comments *)

(** Error report *)
module Log =
  Logger.Make(struct let section = "ctrn_rls" and level = Log_level.DEBUG end)


let satur_null (n: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check
      (Printf.sprintf "satur_null: %s" (id_2str n)) t;
  if is_id_null n t then
    let no = get_node n t in
    let t =
      fold_bw_paths
        (fun psrc src t ->
          let t = remove_path src psrc (Pd_id n) t in
          add_path src psrc Pd_null t
        ) no t in
    (* c-paths *)
    let t =
      PSet.fold
        (fun src t ->
          let nsrc = get_node src t in
          fold_c_paths
            (fun cp t ->
              if PSet.mem n (c_path_get_args cp) then
                add_c_path src (c_path_map_null n cp) t
              else t
            ) nsrc t
        ) no.n_bw_c_paths t in
    (* d-paths *)
    PSet.fold
      (fun src t ->
        let nsrc = get_node src t in
        fold_d_paths
          (fun dp t ->
            if PSet.mem n (d_path_get_args dp) then
              match d_path_map_null n dp with
              | Some d -> add_d_path src d t
              | None -> t
            else t
          ) nsrc t
      ) no.n_bw_d_paths t
  else t

let satur_eqs (n: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check (Printf.sprintf "satur_eqs: %s" (id_2str n)) t;
  let nn = get_node n t in
  let eqs = eq_class_find nn.n_eqs t.eq_class in
  let eqs = PSet.remove n eqs in
  let t =
    PSet.fold
      (fun m t ->
        (* saturates all paths from n *)
        let t = fold_fw_paths (add_path m) nn t in
        (* saturates all paths to n *)
        let t = fold_bw_paths (fun p src -> add_path src p (Pd_id m)) nn t in
        (* saturates c_paths from n *)
        fold_c_paths (add_c_path m) nn t
      ) eqs t in
  (* saturates c_paths to n *)
  let t =
    PSet.fold
      (fun src t ->
        let nsrc = get_node src t in
        fold_c_paths
          (fun cp t ->
            if PSet.mem n (c_path_get_args cp) then
              PSet.fold
                (fun m ->
                  let cp_n = c_path_map (fun x -> if x = n then m else x) cp in
                  add_c_path src cp_n
                ) eqs t
            else t
          ) nsrc t
      ) nn.n_bw_c_paths t in
  (* saturates d_paths to n *)
  PSet.fold
    (fun src t ->
      let nsrc = get_node src t in
      fold_d_paths
        (fun dp t ->
          if PSet.mem n (d_path_get_args dp) then
            PSet.fold
              (fun m ->
                let dp_n = d_path_map (fun x -> if x = n then m else x) dp in
                add_d_path src dp_n
              ) eqs t
          else t
        ) nsrc t
    ) nn.n_bw_d_paths t

let all_satur_null (t: cstr): cstr =
  PMap.fold (fun id _ -> satur_null id) t.nodes t

let all_satur_eqs (t: cstr): cstr =
  PMap.fold (fun id _ -> satur_eqs id) t.nodes t

let modus_ponens_path (n: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check (Printf.sprintf "modus_ponens_path: %s" (id_2str n)) t;
  let no = get_node n t in
  (* modus ponens of all couple of paths whose middle id is n *)
  fold_fw_paths
    (fun pdst dst t ->
      PMap.fold
        (fun psrc lsrc t ->
          let p = path_concat psrc pdst in
          PSet.fold (fun src -> add_path src p dst) lsrc t
        ) no.n_bw_paths t
    ) no t

let modus_ponens_c_path (n: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check (Printf.sprintf "modus_ponens_c_path: %s" (id_2str n)) t;
  let no = get_node n t in
  (* modus ponens of c_paths whose middle id is n *)
  PSet.fold
    (fun src t ->
      let nsrc = get_node src t in
      fold_c_paths
        (fun csrc t ->
          if PSet.mem n csrc.cp_targets then
            fold_c_paths
              (fun cdst t ->
                match c_path_concat csrc n cdst with
                | Some c -> add_c_path src c t
                | None -> t
              ) no t
          else t
        ) nsrc t
    ) no.n_bw_c_paths t

let modus_ponens_d_path (n: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check (Printf.sprintf "modus_ponens_d_path: %s" (id_2str n)) t;
  let no = get_node n t in
  (* modus ponens of d_paths whose middle id is n *)
  PSet.fold
    (fun src t ->
      let nsrc = get_node src t in
      fold_d_paths
        (fun dsrc t ->
          if PSet.exists (fun (_, x) -> x=n) dsrc.dp_targets then
            fold_d_paths
              (fun ddst t ->
                match d_path_concat dsrc n ddst with
                | Some d -> add_d_path src d t
                | None -> t
              ) no t
          else t
        ) nsrc t
    ) no.n_bw_d_paths t

let all_modus_ponens_paths (t: cstr): cstr =
  PMap.fold (fun id _ -> modus_ponens_path id) t.nodes t

let all_modus_ponens_c_paths (t: cstr): cstr =
  PMap.fold (fun id _ -> modus_ponens_c_path id) t.nodes t

(* "forget_id id cstr" saturates constrains about id in cstr
 * and then remove all constrains where id appears *)
let forget_id (n: id) (t: cstr): cstr =
  let t = satur_null n t in
  let t = satur_eqs n t in
  let t = modus_ponens_path n t in
  let t = modus_ponens_c_path n t in
  let t = modus_ponens_d_path n t in
  remove_node n t

(** reduction rules *)
(* rigidity rule:
 * propagate equalities between
 * targets of finite paths e.g. :
 *
 * SP |  Eq.cl: id[15]. { |17| }
 * SP |  Eq.cl: id[16]. { |9| }
 * ...
 * SP |  |1|.@{0}{1} |>> |17|
 * SP |  |1|.@{0}{1} |>> |9|
 *
 * becomes:
 *
 * SP |  Eq.cl: id[15]. { |17|, |9| }
 * ...
 * SP |  |1|.@{0}{1} |>> |17|
 * SP |  |1|.@{0}{1} |>> |9|             *)
let node_rigidity_rule (i: id) (n: node) (t: cstr): cstr =
  PMap.fold
    (fun p dst_lst t ->
      if path_is_rigid p then
        let dst_x = PSet.choose dst_lst in
        let aux dst_y t =
          if flag_debug_pl_rules then
            Log.force
              "Rigidity rule:  %s.%s|>>%s /\\ %s.%s|>>%s => %s = %s\n"
              (id_2str i) (path_2str p) (destination_2str dst_x)
              (id_2str i) (path_2str p) (destination_2str dst_y)
              (destination_2str dst_x) (destination_2str dst_y);
          if flag_reduction_stat then incr red_stat_num_rigid_edge_rule;
          add_dst_eq dst_x dst_y t in
        PSet.fold aux (PSet.remove dst_x dst_lst) t
      else t
    ) n.n_fw_paths t

let rigidity_rule (t: cstr): cstr =
  PMap.fold node_rigidity_rule t.nodes t

(* eq. reducing rule:
 * reduce ids that denote the same concrete
 * value, e.g. :
 *
 * SP |  Eq.cl: id[7]. { |2|, |3| }
 * ...
 * SP |  |1|.@{0}{1} |>> |2|
 * SP |  |1|.@{0}{1} |>> |3|
 * SP |  |2|.@{0}{1} |>> |19|
 * SP |  |3|.@{0}{1} |>> |15|
 *
 * becomes:
 *
 * SP |  Eq.cl: id[7]. { |7| }
 * ...
 * SP |  |1|.@{0}{1} |>> |7|
 * SP |  |7|.@{0}{1} |>> |19|
 * SP |  |7|.@{0}{1} |>> |15|
 *
 * returns mapping:
 * |2| -> |7|
 * |3| -> |7|
 * ...
 * and reversed mapping:
 * |7| -> { |2|,|3| }
 * ...                      *)
let aux_red_equalities (e: id PSet.t) (t, glue_map) =
  if PSet.cardinal e < 2 then
    t, glue_map
  else
    (* choose won't failed, an eq-class is non empty *)
    let x = PSet.choose e in
    let ee = PSet.remove x e in
    (* process nodes *)
    let t =
      PSet.fold
        (fun y t ->
          let ny = get_node y t in
          let t = if ny.n_not_null then add_not_null x t else t in
          let t = fold_fw_paths (add_path x) ny t in
          let t = fold_bw_paths (fun p src -> add_path src p (Pd_id x)) ny t in
          let t = fold_c_paths (add_c_path x) ny t in
          let t = fold_d_paths (add_d_path x) ny t in
          let t =
            PSet.fold
              (fun z ->
                fold_c_paths
                  (fun c t ->
                    if PSet.mem y (c_path_get_args c) then
                      add_c_path z
                        (c_path_map (fun k -> if k=y then x else k) c) t
                    else t
                  ) (get_node z t)
              ) ny.n_bw_c_paths t in
          let t =
            PSet.fold
              (fun z ->
                fold_d_paths
                  (fun d t ->
                    if PSet.mem y (d_path_get_args d) then
                      add_d_path z
                        (d_path_map (fun k -> if k=y then x else k) d) t
                    else t
                  ) (get_node z t)
              ) ny.n_bw_d_paths t in
          remove_node y t)
        ee t in
    let glue_map = PMap.add x e glue_map in
    t, glue_map

let red_equalities (t: cstr): cstr * (id, id PSet.t) PMap.t =
  let t, map =
    IntMap.fold (fun _ -> aux_red_equalities) t.eq_class.cl (t, PMap.empty) in
  aux_red_equalities t.eq_class.null_cl (t, map)

let simplify_paths (t: cstr): cstr =
  if pl_do_sanity_check_before then sanity_check "simplify_paths" t;
  PMap.fold
    (fun id n t ->
      fold_fw_paths
        (fun p dst t ->
          let t = remove_path id p dst t
          and simp_p = Regular_expr.simplify p in
          add_path id simp_p dst t
        ) n t
    ) t.nodes t

(* c_path rules *)
let node_c_path_intro (id: id) (n: node) (t: cstr): cstr =
  (* gathering rigid paths from n *)
  let s_p, map =
    fold_fw_paths
      (fun p dst (x, y) ->
        if Regular_expr.is_rigid p then
          PSet.add p x,
          match dst with
          | Pd_null -> y
          | Pd_id dst -> PMap.add p dst y
        else x, y
      ) n (PSet.empty, PMap.empty) in
  let make_path s =
    let p = PSet.choose s in
    PSet.fold Regular_expr.plus (PSet.remove p s) p in
  let make_c_path s_p_induc map p dst =
    let cp_targets, cp_target_null =
      PSet.fold
        (fun q (s, b) ->
          try PSet.add (PMap.find q map) s, b
          with Not_found -> s, true
        ) s_p_induc (PSet.empty, false) in
    { cp_targets;
      cp_target_null;
      cp_induc_path = Regular_expr.star (make_path (s_p_induc));
      cp_prop_path = p;
      cp_prop_dst = dst } in
  let f_aux s_p t =
    if PSet.cardinal s_p < 2 then t
    else
      PSet.fold
        (fun p t ->
          let dst = try Pd_id (PMap.find p map) with Not_found -> Pd_null in
          let cp = make_c_path (PSet.remove p s_p) map p dst in
          add_c_path id cp t) s_p t in
  PSet.fold_subset f_aux s_p t

let fine_c_path_intro
    (src: id)
    (induc_path: path)
    (prop_path: path)
    (prop_dst: destination) (t: cstr): c_path option =
  (* check local property *)
  if is_there_path src prop_path prop_dst t then
    (* check induc *)
    let labls = Regular_expr.generators induc_path in
    let op =
      PSet.fold
        (fun lbl -> function
          | None -> None
          | Some (s, b) ->
              let dsts = find_paths src (Regular_expr.label lbl) t in
              let imgs, null =
                PSet.fold
                  (fun dst (imgs, null) ->
                    match dst with
                    | Pd_id dst -> PSet.add dst imgs, null
                    | Pd_null -> imgs, true) dsts (PSet.empty, false) in
              if null then Some (s, true)
              else
                try Some (PSet.add (PSet.choose imgs) s, b)
                with Not_found -> None
        ) labls (Some (PSet.empty, false)) in
    Option.map
      (fun (cp_targets, cp_target_null) ->
        let c = { cp_targets;
                  cp_target_null;
                  cp_induc_path = induc_path;
                  cp_prop_path = prop_path;
                  cp_prop_dst = prop_dst } in
        if flag_debug_pl_rules then
          Log.force "C-path intro rule:\n%s ==> %s\n"
            (node_2stri " " src (get_node src t)) (c_path_2str src c);
        c
      ) op
  else None

let c_path_intro (t: cstr): cstr =
  if pl_do_sanity_check_before then sanity_check "c_path_intro" t;
  PMap.fold node_c_path_intro t.nodes t

(* todo: rewrite this in a more efficient manner *)
let rec c_path_elim_one (n: id) (c: c_path) (t: cstr): cstr =
  if PSet.mem n c.cp_targets then
    begin
      if flag_debug_pl_rules then
        Log.force "C-path elim reule: %s " (c_path_2str n c);
      remove_c_path n c t
    end
  else
    let c0, b =
      PSet.fold
        (fun tgt (c, b0) ->
          (* first try to find matching c-path *)
          let ntgt = get_node tgt t in
          let c, b =
            fold_c_paths
              (fun cp (c, b) ->
                match b, c_path_concat c tgt cp with
                | true, _ -> c, true
                | false, Some c1 ->
                    if flag_debug_pl_rules then
                      Log.force
                        "C-path modus ponens rule:\n   %s\n/\\ %s\n  ==> %s\n\n"
                        (c_path_2str n c) (c_path_2str tgt cp)
                        (c_path_2str n c1);
                    c1, true
                | false, None -> c, false
              ) ntgt (c, false) in
          (* try to introduce c-paths *)
          let c, b =
            if not b then
              let ocp =
                fine_c_path_intro tgt c.cp_induc_path c.cp_prop_path
                  c.cp_prop_dst t in
              match ocp with
              | None -> c, false
              | Some cp ->
                  begin
                    match c_path_concat c tgt cp with
                    | Some c0 ->
                        if flag_debug_pl_rules then
                          Log.force
                            "C-path modus ponens rule:\n %s\n/\\ %s\n  ==> %s\n"
                            (c_path_2str n c) (c_path_2str tgt cp)
                            (c_path_2str n c0);
                        c0, true
                    | None -> c, false
                  end
            else c, true in
          c, (b0 || b)
        ) c.cp_targets (c, false) in
    (* here b is false iff nothing has been done *)
    if b then
      let t = remove_c_path n c t in
      let t = add_c_path n c0 t in
      c_path_elim_one n c0 t
    else t

let c_path_elim (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check "c_path_elim" t;
  PMap.fold (fun n -> fold_c_paths (c_path_elim_one n)) t.nodes t

(* for now, we do not introduces disjunction
   thus, we introduce path from path when
   .  targets is of the form { null }
   .  the reachable node is context-proved not null *)
let node_path_c_path (n: id) (no: node) (t: cstr): cstr  =
  fold_c_paths
    (fun c t ->
      if PSet.is_empty c.cp_targets then
        (* empty path from n to itself *)
        let t =
          if Regular_expr.has_empty c.cp_induc_path
              && is_id_not_null n t then
            begin
              if flag_debug_pl_rules then
                begin
                  Log.force "C-path / path application rule:";
                  Log.force "   %s\n/\\ %s.%s|>>%s"
                    (c_path_2str n c) (id_2str n)
                    (path_2str Regular_expr.one) (id_2str n);
                  Log.force "/\\ %s not null\n   ==> %s.%s|>>%s\n"
                    (id_2str n) (id_2str n)
                    (path_2str c.cp_prop_path)
                    (destination_2str c.cp_prop_dst)
                end;
              if flag_reduction_stat then
                incr red_stat_num_c_path_rule;
              add_path n c.cp_prop_path c.cp_prop_dst t
            end
          else t in
        fold_fw_paths
          (fun p dst t ->
            match Regular_expr.is_le p c.cp_induc_path, dst with
            | false, _
            | true, Pd_null -> t
            | true, Pd_id dst ->
                if is_id_not_null dst t then
                  begin
                    if flag_debug_pl_rules then
                      begin
                        Log.force "C-path / path application rule:";
                        Log.force "   %s\n/\\ %s.%s|>>%s"
                          (c_path_2str n c) (id_2str n)
                          (path_2str p) (id_2str dst);
                        Log.force "/\\ %s not null\n   ==> %s.%s|>>%s\n"
                          (id_2str dst) (id_2str dst)
                          (path_2str c.cp_prop_path)
                          (destination_2str c.cp_prop_dst)
                      end;
                    if flag_reduction_stat then
                      incr red_stat_num_c_path_rule;
                    add_path dst c.cp_prop_path c.cp_prop_dst t
                  end
                else t
          ) no t
      else t
    ) no t

let path_c_path (t: cstr): cstr =
  PMap.fold node_path_c_path t.nodes t

(* d_path rules *)
let node_d_path_intro (src: id) (n: node) (t: cstr): cstr =
  (* gathering rigid paths from n *)
  let os: (Offs.t * id) PSet.t = fold_fw_paths (fun p dst os ->
    match Regular_expr.is_label p, dst with
    | Some o, Pd_id dst -> PSet.add (o, dst) os
    | _ -> os) n PSet.empty in
  let aux (os: (Offs.t * id) PSet.t): cstr -> cstr =
    PSet.fold
      (fun (dp_bw_induc, dp_bw_target) t ->
        let dp_fw_induc, dp_targets =
          PSet.fold
            (fun (o, id) (oo, ids) ->
              PSet.add o oo, PSet.add (src, id) ids
            ) (PSet.remove (dp_bw_induc, dp_bw_target) os)
            (PSet.empty, PSet.empty) in
        let dp = { dp_bw_target;
                   dp_fw_induc;
                   dp_bw_induc;
                   dp_targets } in
        add_d_path src dp t) os in
  let aux1 os t = if PSet.cardinal os < 2 then t else aux os t in
  PSet.fold_subset aux1 os t

let d_path_intro (t: cstr): cstr =
  PMap.fold node_d_path_intro t.nodes t

let d_path_fine_intro (x: id) (dp: d_path) (t: cstr): cstr * bool =
  let b = ref false in
  (* first try modus ponens *)
  let dp_new, t =
    PSet.fold
      (fun (_, j) (dp, t) ->
        let nj = get_node j t in
        fold_d_paths
          (fun d_app (dp, t) ->
            match d_path_concat dp j d_app with
            | None -> dp, t
            | Some d_new ->
                b := true;
                d_new, remove_d_path j d_app t)
          nj (dp, t)
      ) dp.dp_targets (dp, t) in
  (* try thin edges *)
  let dp_new =
    PSet.fold
      (fun (i, j) dp ->
        let tgts =
          PSet.fold
            (fun o s ->
              PSet.add (find_paths j (Regular_expr.label o) t) s
            ) dp.dp_fw_induc PSet.empty in
        let bw_cand = find_bw_paths i (Regular_expr.label dp.dp_bw_induc) t in
        (* search an edge j.p|->i, and then search edges j.o1|->k_1 ... *)
        if PSet.mem j bw_cand && not (PSet.exists PSet.is_empty tgts) then
          begin
            let dp_targets = PSet.remove (i, j) dp.dp_targets in
            let tgts =
              PSet.fold
                (fun s tgts ->
                  let b =
                    PSet.exists (fun x -> are_destination_eq x Pd_null t) s in
                  if b then tgts
                  else
                    match PSet.choose s with
                    | Pd_null ->
                        Log.fatal_exn "d_path_fine_intro: shall not happens"
                    | Pd_id x -> PSet.add x tgts
                ) tgts PSet.empty in
            let dp_targets =
              PSet.fold (fun tgt -> PSet.add (j, tgt)) tgts dp_targets in
            b := true;
            { dp with dp_targets }
          end
        else dp
      ) dp_new.dp_targets dp_new in
  let t =
    if !b then add_d_path x dp_new (remove_d_path x dp t)
    else t in
  t, !b

let rec d_path_elim_aux (iter: int) (t: cstr): cstr =
  if iter = 0 then
    Log.fatal_exn "d_path_elim_aux: maximum number of iteration reached";
  let b = ref false (* if sthg is reduced then set b true *) in
  let t =
    PMap.fold
      (fun x _ t ->
        let nx = get_node x t in
        fold_d_paths
          (fun dp t ->
            let t, b0 = d_path_fine_intro x dp t in
            b := (!b || b0);
            t
          ) nx t
      ) t.nodes t in
  if !b then d_path_elim_aux (iter-1) t else t

let d_path_elim: cstr -> cstr =
  d_path_elim_aux pl_internal_reduction_iteration

let aux_node_p_d_p (x: id) (n: Offs.t) (p: Offs.t) (t: cstr): cstr =
  let ys = find_paths x (Regular_expr.label n) t in
  PSet.fold
    (fun y t ->
      match y with
      | Pd_null -> t
      | Pd_id y ->
          if is_id_not_null y t then
            begin
              if flag_debug_pl_rules then
                Log.force "D-rule applied: %s.%s|>>%s introduced"
                  (id_2str y) (path_2str (Regular_expr.label p)) (id_2str x);
              if flag_reduction_stat then
                incr red_stat_num_c_path_rule;
              add_path y (Regular_expr.label p) (Pd_id x) t
            end
          else t
    ) ys t

let node_path_d_path (n: id) (no: node) (t: cstr): cstr =
  fold_d_paths
    (fun d t ->
      if PSet.is_empty d.dp_targets then
        let t =
          if is_id_not_null n t then
            begin
              if flag_debug_pl_rules then
                Log.force "D-rule applied (2): %s.%s|>>%s introduced"
                  (id_2str n) (path_2str (Regular_expr.label d.dp_bw_induc))
                  (id_2str d.dp_bw_target);
              add_path n (Regular_expr.label d.dp_bw_induc)
                (Pd_id d.dp_bw_target) t
            end
          else t in
        let p_induc = Regular_expr.star (Regular_expr.set_2t d.dp_fw_induc) in
        fold_fw_paths
          (fun p dst t ->
            if Regular_expr.is_le p p_induc then
              match dst with
              | Pd_null -> t
              | Pd_id dst ->
                  PSet.fold (fun o -> aux_node_p_d_p dst o d.dp_bw_induc)
                    d.dp_fw_induc t
            else t
          ) no t
      else t
    ) no t

let path_d_path (t: cstr): cstr =
  PMap.fold node_path_d_path t.nodes t


let find_hint (n: id) (t: cstr): (id * Offs.t PSet.t * id) list =
  let no = get_node n t in
  fold_bw_paths
    (fun p src reqs ->
      let s =
        find_d_path src
          (fun d ->
            Regular_expr.is_le p
              (Regular_expr.star (Regular_expr.set_2t d.dp_fw_induc))
          ) t in
      match s with
      | None -> reqs
      | Some d ->
          let bs = find_bw_paths n (Regular_expr.label d.dp_bw_induc) t in
          PSet.fold (fun b reqs -> (src, d.dp_fw_induc, b)::reqs) bs reqs
    ) no []

(** reduction summary rules *)
(* "compose_glue_map map0 map" returns (map) o (map0) *)
let compose_glue_map
    (map0: (id, id PSet.t) PMap.t)
    (map: (id, id PSet.t) PMap.t): (id, id PSet.t) PMap.t =
  (* notation: map0: i -> j and map: j -> k *)
  let map1, map =
    PMap.fold
      (fun i sj (map1, map) ->
        let map, sk =
          PSet.fold
            (fun j (map, sk) ->
              try
                let ssk = PMap.find j map in
                let map = PMap.remove j map
                and sk = PSet.union ssk sk in
                map, sk
              with
              | Not_found ->
                  let sk = PSet.add j sk in
                  map, sk)
            sj (map, PSet.empty) in
        let map1 = PMap.add i sk map1 in
        map1, map)
      map0 (PMap.empty, map) in
  PMap.fold
    (fun j sk map1 ->
      if PMap.mem j map1 then
        Log.fatal_exn "compose_glue_map: inconstitent glueing map";
      PMap.add j sk map1)
    map map1

(* maximum reduction: iteration of the above rules *)
let reduce (t: cstr): cstr * (id, id PSet.t) PMap.t =
  (* 0) reduce c/d_path at maximum using modus ponens rules *)
  let t = c_path_elim t in
  let t = d_path_elim t in
  let rec aux n (t, glue_map) =
    if flag_debug_pl_rules then
      Log.force "Constrain_rules: reduction [ iter %i ]" n;
    if n > pl_internal_reduction_iteration then t, glue_map
    else
      (* 1) apply c/d_path instantiation and rigidity rule *)
      let t0 = path_c_path t in
      let t1 = path_d_path t0 in
      let t2 = rigidity_rule t1 in
      (* 2) reduce the equalities *)
      let t3, glue_map0 = red_equalities t2 in
      (* 3) compose glueing maps *)
      let glue_map1 = compose_glue_map glue_map glue_map0 in
      aux (n+1) (t3, glue_map1) in
  aux 0 (t, PMap.empty)
