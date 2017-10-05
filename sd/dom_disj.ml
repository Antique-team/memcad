(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_disj.ml
 **       the disjunction abstract domain
 ** Xavier Rival, 2011/07/25 *)
open Ast_sig
open Data_structures
open Disj_sig
open Disj_utils
open Flags
open Lib
open Dom_sig
open Dom_utils

(** This module implements a weak version of trace partitioning, with
 ** tokens describing the history of the states;
 **
 ** But it is not a real partitioning; a same token may occur several
 ** times, with different abstract states. A future improvement will
 ** turn this functor into a real trace partitioning layer, yet this
 ** will be possible only when better trace partitioning criteria are
 ** identified.
 **)


(** Error report *)
module Log =
  Logger.Make(struct let section = "d_disj__" and level = Log_level.DEBUG end)


(** Functor lifting an environment domain into a disjunctive domain *)
module Dom_disj = functor (D: DOM_ENV) -> functor (GE: GRAPH_ENCODE) ->
  (struct
    let module_name = "dom_disj"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s -> %s\n%s%s"
        module_name D.module_name
        module_name GE.module_name
        (D.config_2str ())
        (GE.config_2str ())

    (* For now, we simply use lists... *)
    type t = D.t abs_hist_fun

    (* Disjunction size *)
    let disj_size (x: t): int = List.length x

    (** Utilities *)
    let map_flatten (f: D.t -> D.t list) (x: t): t =
      List.flatten
        (List.map (fun (ah, x) -> List.map (fun y -> ah, y) (f x)) x)
    (* iteration *)
    let map (f: D.t -> D.t): t -> t = List.map (fun (ah, x) -> ah, f x)
    (* repeated annotation *)
    let annotate (f: int -> abs_hist_atom) (x: t): t =
      List.mapi (fun i (ah, y) -> (f i :: ah, y)) x
    (* conditional annotation:
     * in case several branches occur, add a token *)
    let conditional_annotate (f: int -> abs_hist_atom) (l: t list): t list =
      List.map
        (fun ul ->
          match ul with
          | [ ] | [ _ ] -> ul
          | _ -> annotate f ul
        ) l

    (** Domain implementation *)
    (* Bottom element *)
    let bot: t = [ ]
    let is_bot: t -> bool =
      List.fold_left (fun acc (_, x) -> acc && D.is_bot x) true
    (* Top element *)
    let top (): t = [ [ ], D.top () ]
    (* Pretty-printing *)
    let t_2stri (ind: string) (x: t) =
      match x with
      | [ ] ->
          Printf.sprintf "%s_|_" ind
      | _ ->
          let nind = "   " ^ ind in
          let buff = Buffer.create 80 in
          Buffer.add_string buff
            (Printf.sprintf "%s%d disjunctions\n" ind (List.length x));
          List.iteri
            (fun i (ah, y) ->
              Buffer.add_string buff
                (Printf.sprintf "%s<disj %d: %s>\n%s\n"
                  ind i (abs_hist_2str ah) (D.t_2stri nind y))
            ) x;
          Buffer.contents buff
    let t_2str: t -> string = t_2stri ""
    (* External output *)
    let ext_output (o: output_format) (base: string) (x: t): unit =
      List.iteri
        (fun i (_, u) -> D.ext_output o (Printf.sprintf "%s-D%d" base i) u) x
    let output_graph_counter = ref 0
    (* dot output the graph for debugging inside this layer/domain *)
    let output_graph (live_vars: var list) (x: t): unit =
      let save_then_incr iref =
        let res = !iref in
        incr iref;
        res in
      let vars = List.map (fun v -> v.v_name) live_vars in
      List.iteri
        (fun i (_, u) ->
          D.ext_output (Out_dot (vars, ["SUCC"]))
            (Printf.sprintf "d_disj_D%d_%d"
               i (save_then_incr output_graph_counter)) u
        ) x
    (* Garbage collection *)
    let gc (x: t): t = map D.gc x

    (** Comparison and Join operators *)
    (* Checks if the left argument is included in the right one *)
    let rec is_le (xl: t) (xr: t): bool =
      let under_is_le (l: D.t) (r: D.t): bool =
        try D.is_le l r with _ -> false in
      let aux (xl0: D.t): bool =
        List.fold_left
          (fun acc (_, xr0) ->
            acc || under_is_le xl0 xr0) false xr in
      match xl with
      | [ ] -> (* xl denotes _|_ so is "less or equal" than xr *)
          true
      | (_, xl0) :: xlo ->
          aux xl0 && is_le xlo xr
    (* Fusion of a number of disjuncts into only one, while keeping the
     * most general token *)
    let merge_disjuncts (x: t): t =
      ahf_sanity_check "merge,in" x;
      let r =
        match x with
        | [ ] -> [ ]
        | y :: z ->
            let fusion (a0,u0) (a1,u1) =
              ah_unify a0 a1,
              D.join None None (u0, ext_graph None None)
                (u1, ext_graph None None) in
            [ List.fold_left fusion y z ] in
      ahf_sanity_check "merge,out" r;
      r

    (** Disjuncts partitionning based on encoded graphs *)

    (* list of encoded graphs *)
    type graph_list = (GE.encoded_graph * (abs_hist * D.t)) list
    (* each group has a representative graph and an elements list inside *)
    type group = GE.encoded_graph * graph_list
    (* groups *)
    type groups = group list

    (* insert a group into groups  *)
    let rec insert_into_partition (ag: group) (gs: groups)
        : group option * groups =
      match gs with
      | [] -> None, [ag]
      | hd :: tl ->
          let jo = GE.join (fst ag) (fst hd) in
          match jo with
          | None ->
              let ag, gs = insert_into_partition ag tl in
              ag, hd :: gs
          | Some go ->
              Some (go, (snd hd) @ (snd ag)), tl

    (* partition the left groups  *)
    let rec group_partition (gs: groups) (left: groups): groups =
      match left with
      | []  ->  gs
      | hd::tl ->
          let mg, gs = insert_into_partition hd gs in
          match mg with
          | None -> group_partition gs tl
          | Some m -> group_partition gs (m :: tl)

    (* partition a list of graphs into groups *)
    let list_groups (lg: graph_list): groups =
      let init_groups =
        List.fold_left (fun acc ele -> (fst ele, [ele])::acc) [] lg in
      let res = group_partition [] init_groups in
      if not !Flags.very_silent_mode then
        begin (* debug logs *)
          Log.info "group_partition:";
          List.iter
            (fun ag ->
              let rep, eles = ag in
              Log.info "partition_rep:%s"
                (GE.string_of_renamed_paths (fst3 rep) );
              List.iter
                (fun ele ->
                  Log.info " disj:%d\n {%s}" (trd3 (fst ele))
                    (GE.string_of_renamed_paths (fst3 (fst ele)))
                ) eles;
            ) res
        end;
      res

    (** Management of disjunctions *)

    (* Selective disjunct merge *)
    let sel_merge (l: var list) (ho: hint_be option)
        (lo: (var lint_be) option) (x: t): t =
      Log.info "sel_merge: #disj. before: %d" (List.length x);
      if not !Flags.sel_widen then
        let _ =
          Log.warn
            "sel_merge command ignored because sel_widen flag not present" in
        x
      else
        (* get the live variables, and use it for encoding *)
        let hint_encode =
          match ho with
          | None -> l
          | Some ho -> VarSet.fold (fun ele acc -> ele :: acc) ho.hbe_live l in
        (* encoding all the graphs *)
        let _, encode_graphs =
          List.fold_left
            (fun (disj_num, acc) (a, e) ->
               let g = D.encode disj_num hint_encode e in
               (disj_num + 1, (g, (a,e)) :: acc)
            ) (0, []) x in
        (* partition the graph list into groups *)
        let groups = list_groups encode_graphs in
        (* joining of two disjunts *)
        let fusion
            (((a0, u0), jl): (abs_hist * D.t) * join_ele)
            (((a1, u1), jr): (abs_hist * D.t) * join_ele)
            (ho: hint_be option) (lo: (var lint_be) option) =
          let arg_l, arg_r =
            if !Flags.guided_join then
              { abs_gi = jl.abs_gi ;
                abs_go = jl.abs_go },
              { abs_gi = jr.abs_gi ;
                abs_go = jr.abs_go }
            else
              { abs_gi = None ;
                abs_go = None },
              { abs_gi = None ;
                abs_go = None } in
          let ao = ah_unify a0 a1 in
          let uo = D.join ho lo (u0, arg_l) (u1, arg_r) in
          jl.abs_go, (ao, uo) in
        (* merge all disjuntions in one partition group *)
        let res =
          List.fold_left
            (fun p_acc (go, ges) ->
              assert (1 <= List.length ges);
              let hd_go, hd_g = List.hd ges in
              let tl = try List.tl ges with Failure _ -> [ ] in
              let m_ele =
                List.fold_left
                  (fun (acc_eg, acc_g) (eg, g) ->
                    let arg_e = g, ext_graph (Some eg) (Some go) in
                    let arg_acc = acc_g, ext_graph acc_eg (Some go) in
                    let rdisj_num =
                      match acc_eg with
                      | None -> -1
                      | Some acc_eg -> trd3 acc_eg in
                    Log.info "joinl:%d, joinr: %d " (trd3 eg) (rdisj_num);
                    fusion arg_e arg_acc ho lo
                  ) (Some hd_go, hd_g) tl in
              (snd m_ele) :: p_acc
            ) [] groups in
        Log.info "sel_merge: #disj. after: %d" (List.length res);
        res


    (* joining *)
    let join (ho: hint_be option) (lo: (var lint_be) option)
        (xl: t) (xr: t): t =
      ahf_sanity_check "join,inl" xl;
      ahf_sanity_check "join,inr" xr;
      let xl =
        List.filter (fun ul -> not (List.exists (fun a -> a == ul) xr)) xl in
      let r = xl @ xr in
      ahf_sanity_check "join,out" r;
      r

    (*  encoded graphs *)
    type encoded  = GE.encoded_graph option * (abs_hist * D.t)

    (* Widening will fold lists of disjuncts if there are several;
     * - in the sel-widen mode, disjuntions in the right will be
     *  - partitioned into groups accoring to disjunction in the left
     *  - directed weakening will not make that effort (for now) *)
    let widen (ho: hint_be option) (lo: (var lint_be) option)
        (xl: t) (xr: t): t * t option =
      if !Flags.sel_widen then
        Log.info "sel_widen: #disj. xl xr: %d %d"
          (List.length xl) (List.length xr);
      (* use live variable for encodeing *)
      let hint_encode =
        match ho with
        | None -> []
        | Some ho -> VarSet.fold (fun ele acc -> ele::acc) ho.hbe_live [] in
      (* Fusion of a number of disjuncts into only one, while keeping the
       * most general token *)
      let merge_encoded_disjuncts (x: encoded list): encoded list =
        let r =
          match x with
          | [ ] -> [ ]
          | y :: z ->
              let fusion (u0_g, (a0,u0)) (u1_g, (a1,u1)) =
                let r_a = ah_unify a0 a1 in
                try
                  let u0_g, u1_g = BatOption.get u0_g, BatOption.get u1_g in
                  let r_g = GE.widen u0_g u1_g in
                  let r_u =
                    D.join ho lo (u0, ext_graph (Some u0_g) (Some r_g))
                      (u1, ext_graph (Some u1_g) (Some r_g)) in
                  let r_g = D.encode (-1) hint_encode r_u in
                  (Some r_g, (r_a, r_u))
                with
                | Invalid_argument _ ->
                    let r_u =
                      D.join ho lo (u0, ext_graph None None)
                        (u1, ext_graph None None) in
                    (None, (r_a, r_u)) in
              [ List.fold_left fusion y z ] in
        r in
      (* function to widen, with one disjunct in the left *)
      let widen_1n (u0_g, (ah, u0): encoded) (rr: encoded list): t =
        let ext u = u, ext_graph None None in
        let f u0_g ur_g =
          try
            let u0_g, ur_g = BatOption.get u0_g, BatOption.get ur_g in
            let r_g = GE.widen u0_g ur_g in
            ext_graph (Some u0_g) (Some r_g), ext_graph (Some ur_g) (Some r_g)
          with
          | Invalid_argument _ -> ext_graph None None, ext_graph None None in
        match rr with
        | [ ] -> [ah, u0 ]
        | [(ur_g, (ahr, u0r))] ->
            let l_ele, r_ele =
              if !Flags.guided_widen then f u0_g ur_g
              else ext_graph None None, ext_graph None None in
            let u_w = D.widen ho lo (u0, l_ele) (u0r, r_ele) in
            [ ah, u_w ]
        | (ur_g, (ahr, u0r)) :: lrr ->
            let u0 =
              if !Flags.do_unary_abstraction then
                let hro = Option.map (fun h -> { hue_live = h.hbe_live }) ho in
                D.local_abstract hro u0
              else u0 in
            if !Flags.sel_widen then
              let l_ele, r_ele =
                if !Flags.guided_widen then f u0_g ur_g
                else ext_graph None None, ext_graph None None in
              let res =  D.widen ho lo (u0, l_ele) (u0r, r_ele) in
              let r_g =
                if !Flags.guided_widen then Some (D.encode (-1) hint_encode res)
                else None in
              match merge_encoded_disjuncts ((r_g, (ah, res))::lrr) with
              | [ur_g, (_, u_j) ] ->
                  let l_ele, r_ele =
                    if !Flags.guided_widen then f u0_g ur_g
                    else ext_graph None None, ext_graph None None in
                  let u_w = D.widen ho lo (u0, l_ele) (u_j, r_ele) in
                  [ ah, u_w ]
              | _ -> Log.fatal_exn "merge_disjuncts"
            else
              match merge_disjuncts (List.map (fun (_, (ah,t)) ->
                ah, D.widen ho lo (ext u0) (ext t)) rr) with
              | [ _, u ] -> [ ah, u ]
              | _ -> Log.fatal_exn "merge_disjuncts" in
      (* pre-widening sanity checks *)
      ahf_sanity_check "widen,inl" xl;
      ahf_sanity_check "widen,inr" xr;
      (* optional weak abstraction in the right hand side *)
      let xr =
        let xr0 =
          if !Flags.do_unary_abstraction then
            let hro = Option.map (fun h -> { hue_live = h.hbe_live }) ho in
            map (D.local_abstract hro) xr
          else xr in
        if !Flags.disj_merge_before_join then merge_disjuncts xr0
        else xr0 in
      (* main match *)
      let res_0, res_1 =
        if !Flags.part_through_lfps || !Flags.sel_widen then
          match xl, xr with
          | [ ], _ ->
              if !Flags.flag_debug_disj then
                Log.force "widen 0-%d" (List.length xr);
              xr, None
          | _, [ ] ->
              if !Flags.flag_debug_disj then
                Log.force "widen %d-0" (List.length xl); xl, None
          | _ ->
              if !Flags.flag_debug_disj then
                Log.force "widen %d-%d" (List.length xl) (List.length xr);
              let fu (ah, _) = abs_hist_2str ah in
              let ft = gen_list_2str "" fu "\n" in
              if !Flags.flag_debug_disj then
                Log.force "left:\n%s\nright:\n%s" (ft xl) (ft xr);
              let _, xr_encode =
                List.fold_left
                  (fun (disj_num, acc) (a, e) ->
                    let g = D.encode disj_num hint_encode e in
                    (disj_num + 1, (g, (a, e)) :: acc)
                  ) (0, []) xr in
              let _, l_pairings, l_remain =
                List.fold_left
                  (fun (disj_num, acc, rem) (ahl, ul) ->
                    let ul_g = D.encode disj_num hint_encode ul  in
                    let nur, rem =
                      List.fold_left
                        (fun (accr, rem) (ur_g, (ahr, ur)) ->
                          let b =
                            (* detect disjuntions in the right which should *
                               be widen with same left *)
                            if !Flags.sel_widen then
                              GE.can_widen ur_g ul_g
                            else
                              (* when the checking fails, we motivate the *
                               * path information (not sure) *)
                              ah_is_prefix ahl ahr in
                          if b then
                            (Some ur_g, (ahr, ur)) :: accr, rem
                          else accr, (ur_g, (ahr, ur)) :: rem
                        ) ([], []) rem in
                    disj_num + 1, (Some ul_g, ahl, ul, nur) :: acc, rem
                  ) (0, [ ], xr_encode) (List.rev xl) in
              if l_remain != [ ] then
                begin
                  Log.info "remain";
                  List.iter
                    (fun (_, (ahl, ur)) ->
                      Log.info "  %s " (abs_hist_2str ahl)
                    ) l_remain;
                end;
              if !Flags.flag_debug_disj then
                begin
                  Log.force "pre-processed";
                  List.iter
                    (fun (_, ahl, _, ur) ->
                      Log.force "%s -> [%d]" (abs_hist_2str ahl)
                        (List.length ur)
                    ) l_pairings;
                end;
              let l_pairings, l_empty =
                List.fold
                  (fun (l_nem, l_em) (ul_g, ah, ul, ur) ->
                     if ur = [] then l_nem, (ah, ul)::l_em
                     else (ul_g, ah, ul, ur)::l_nem, l_em
                  ) ([], []) l_pairings in
              let res =
                List.flatten
                  (List.map
                     (fun (ul_g, ah, ul, ur) -> widen_1n (ul_g, (ah, ul)) ur)
                     l_pairings) in
              let res =
                (* HS: I am not sure it can guarantee termination *)
                List.fold_left (fun acc (_, ele) -> ele::acc) res l_remain in
              if l_empty <> [] && !Flags.sel_widen then
                res, Some l_empty
              else
                l_empty @ res, None
        else
          match merge_disjuncts xl with
          | [ ] -> xr, None
          | [ ah, xl0 ] ->
              widen_1n (None, (ah, xl0)) (List.map (fun ele -> None, ele) xr),
              None
          | _ :: _ :: _ -> Log.fatal_exn "merge_disjunct output is wrong" in
      ahf_sanity_check "widen,out" res_0;
      if !Flags.sel_widen then
        Log.info "sel_widen: #disj. res_0 res_1: %d %s"
          (List.length res_0)
          (match res_1 with
           | None -> "N/A"
           | Some res -> Printf.sprintf "%d" (List.length res));
      res_0, res_1
    (* directed weakening *)
    let directed_weakening (ho: hint_be option) (xl: t) (xr: t): t =
      ahf_sanity_check "dirweak,inl" xl;
      ahf_sanity_check "dirweak,inr" xr;
      let r =
        match xl with
        | [ ] -> xr
        | [ ah, xl0 ] ->
            merge_disjuncts (map (D.directed_weakening ho xl0) xr)
        | _ :: _ :: _ ->
            Log.fatal_exn "directed_weakening: too many disjuncts in left" in
      ahf_sanity_check "dirweak,out" r;
      r

    (** Transfer functions for the analysis *)
    (* Assignment operator *)
    let assign (loc: location)
        (lv: var tlval) (ex: var texpr) (x: t): t list =
      ahf_sanity_check "assign,in" x;
      let f i (ah, u) =
        if !Flags.flag_debug_disj then
          Log.force "\n\ndisjunct: %d\n" i;
        List.map (fun y -> ah, y) (D.assign lv ex u) in
      let l = List.mapi f x in
      let l = conditional_annotate (fun i -> Ah_unfold (Uassign, loc, i )) l in
      let r = [ List.flatten l ] in
      ahf_sanity_check "assign,out" (List.flatten r);
      r
    (* Condition test *)
    let guard (loc: location) (b: bool) (ex: var texpr) (x: t): t list =
      ahf_sanity_check "guard,in" x;
      let f (ah, u) =
        (* reduction performed on the fly: throwing out _|_ elements *)
        let l = List.filter (fun y -> not (D.is_bot y)) (D.guard b ex u) in
        List.map (fun y -> ah, y) l in
      let l = List.map f x in
      let l = conditional_annotate (fun i -> Ah_unfold (Uguard, loc, i)) l in
      let r = [ List.flatten l ] in
      ahf_sanity_check "guard,out" (List.flatten r);
      r
    (* Checking that a constraint is satisfied; returns over-approx sat *)
    let sat (ex: var texpr) (t: t): bool =
      List.fold_left (fun accb (_, x) -> accb && D.sat ex x) true t

    (* Adding an abs_hist_atom *)
    let push_hist_atom (aha: Disj_sig.abs_hist_atom) (x: t): t =
      List.map (fun (ah, x) -> aha :: ah, x) x

    (** Analysis control *)
    (* Reduction + node relocalization *)
    let reduce_localize (lv: var tlval) (x: t): t =
      let l = List.map (fun (ah, u) -> ah, D.reduce_localize lv u) x in
      List.fold_left
        (fun acc -> function
          | _, None -> acc
          | ah, Some u -> (ah, u) :: acc
        ) [ ] (List.rev l)
    (* Eager reduction *)
    let reduce_eager (x: t): t =
      List.flatten
        (List.map
           (fun (ah, u) -> List.map (fun u -> ah, u) (D.reduce_eager u)) x)

    (** Assuming and checking inductive edges *)
    (* Unfold *)
    let ind_unfold (loc: location)
        (udir: Graph_sig.unfold_dir) (lv: var tlval) (x: t): t =
      ahf_sanity_check "unfold,in" x;
      let f (ah, u) = List.map (fun y -> ah, y) (D.ind_unfold udir lv u) in
      let l = List.map f x in
      let l = conditional_annotate (fun i -> Ah_unfold (Uunfold, loc, i)) l in
      let r = List.flatten l in
      ahf_sanity_check "unfold,out" r;
      r

    (** Unary domain operations *)
    (* Allocation *)
    let do_allocate (l: var tlval) (s: var texpr) (u: D.t): D.t list =
      let lzero =
        D.assign l (Ecst (Cint 0), Tint (Flags.abi_ptr_size, Tsigned)) u in
      let lnzero = D.memory (MO_alloc (l, s)) u in
      lzero @ lnzero

    (* operand types and constructors for add/rem/assume/check *)
    let unary_op (op: unary_op) (x: t) =
      match op with
      | UO_env eop -> map (D.unary_op eop) x
      | UO_ret _   -> Log.fatal_exn "return_var"
      | UO_mem (MO_alloc (l, s) as mop) ->
          if !flag_malloc_never_null then map_flatten (D.memory mop) x
          else map_flatten (do_allocate l s) x
      | UO_mem (MO_dealloc _ as mop) -> map_flatten (D.memory mop) x

    (* set expr assume *)
    let assume (op: state_log_form): t -> t = map (D.assume op)
    let check (op: state_log_form) (t: t): bool =
      List.for_all (fun (_, y) -> D.check op y) t

    (** Statistics *)
    (* For now, simply a number of disjuncts *)
    let get_stats (x: t): int = List.length x

  end: DOM_DISJ)

module Dom_disj_timing =
  functor (D: DOM_DISJ) ->
    (struct
      module T = Timer.Timer_Mod( struct let name = "Dom_disj" end )
      type t = D.t
      let module_name = "dom_disj_timing"
      let config_2str = T.app1 "config_2str" D.config_2str
      let disj_size = T.app1 "disj_size" D.disj_size
      let bot = D.bot
      let is_bot = T.app1 "is_bot" D.is_bot
      let top = T.app1 "top" D.top
      let t_2stri = T.app2 "t_2stri" D.t_2stri
      let t_2str = T.app1 "t_2str" D.t_2str
      let ext_output = T.app3 "ext_output" D.ext_output
      let gc = T.app1 "gc" D.gc
      let is_le = T.app2 "is_le" D.is_le
      let merge_disjuncts = T.app1 "merge_disjuncts" D.merge_disjuncts
      let sel_merge = T.app4 "sel_merge" D.sel_merge
      let join = T.app4 "join" D.join
      let widen = T.app4 "widen" D.widen
      let directed_weakening = T.app3 "directed_weakening" D.directed_weakening
      let assign = T.app4 "assign" D.assign
      let guard = T.app4 "guard" D.guard
      let sat = T.app2 "sat" D.sat
      let push_hist_atom = T.app2 "push_hist_atom" D.push_hist_atom
      let reduce_localize = T.app2 "reduce_localize" D.reduce_localize
      let reduce_eager = T.app1 "reduce_eager" D.reduce_eager
      let ind_unfold = T.app4 "ind_unfold" D.ind_unfold
      let unary_op = T.app2 "unary_op" D.unary_op
      let assume = T.app2 "assume" D.assume
      let check = T.app2 "check" D.check
      let get_stats = T.app1 "get_stats" D.get_stats
    end: DOM_DISJ)
