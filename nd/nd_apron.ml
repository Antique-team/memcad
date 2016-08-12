(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_apron.ml
 **       binding with the Apron library
 ** Xavier Rival, 2011/07/03 *)
open Data_structures
open Lib
open Nd_sig
open Nd_utils
(* External: Apron components *)
open Apron

(** Improvements to consider:
 **  - try to reduce the cost of node addition / removal functions
 **    . nodes_filter could be removed, replaced with rem_node
 **    . rem_node and add_node should apply to sets, to speed up
 **      removals / additions of large sets of variables
 **  - add a packing functor in the numerical domain
 **)


(* Error reporting *)
module Log =
  Logger.Make(struct let section = "nd_apron" and level = Log_level.DEBUG end)


(** Pre domain; intermediate used as part of the binding *)
(* An Apron manager encloses a numerical domain.       *)
(* We should switch a module with the signature below, *)
(* in order to fix an Apron domain.                    *)
module type PRE_APRON =
  sig
    type t
    val man: t Manager.t
  end
module PA_box =
  (struct
    type t = Box.t
    let man: t Manager.t =
      Box.manager_alloc ()
  end: PRE_APRON)
module PA_oct =
  (struct
    type t = Oct.t
    let man: t Manager.t =
      Oct.manager_alloc ()
  end: PRE_APRON)
module PA_polka =
  (struct
    type t = Polka.strict Polka.t
    let man: t Manager.t =
      Polka.manager_alloc_strict ()
  end: PRE_APRON)


(** Wrapper around Abstract1, to add statistics *)
(* Interface *)
type 'a man = 'a Apron.Manager.t
type env = Apron.Environment.t
module type ABSTRACT1_TYPE =
  sig
    type 'a t = 'a Abstract1.t
    val top: 'a man -> env -> 'a t
    val is_bottom: 'a man -> 'a t -> bool
    val env: 'a t -> env
    val to_lincons_array: 'a man -> 'a t -> Apron.Lincons1.earray
    val change_environment: 'a man -> 'a t -> env -> bool -> 'a t
    val is_leq: 'a man -> 'a t -> 'a t -> bool
    val sat_tcons: 'a man -> 'a t -> Apron.Tcons1.t -> bool
    val bound_variable: 'a man -> 'a t -> Apron.Var.t -> Apron.Interval.t
    val rename_array: 'a man -> 'a t
      -> Apron.Var.t array -> Apron.Var.t array -> 'a t
    val meet_tcons_array: 'a man -> 'a t -> Apron.Tcons1.earray -> 'a t
    val join: 'a man -> 'a t -> 'a t -> 'a t
    val widening: 'a man -> 'a t -> 'a t -> 'a t
    val widening_threshold: 'a man -> 'a t -> 'a t
      -> Apron.Lincons1.earray -> 'a t
    val assign_texpr_array: 'a man -> 'a t -> Apron.Var.t array
      -> Apron.Texpr1.t array -> 'a t option -> 'a t
    val forget_array: 'a man -> 'a t -> Apron.Var.t array -> bool -> 'a t
    val expand: 'a man -> 'a t -> Apron.Var.t -> Apron.Var.t array -> 'a t
    val fold: 'a man -> 'a t -> Apron.Var.t array -> 'a t
    val meet: 'a man -> 'a t -> 'a t -> 'a t
  end
(* Histogram of the values created *)
let histo: int IntMap.t ref = ref IntMap.empty
let add_to_histo (size: int): unit =
  let v = try IntMap.find size !histo with Not_found -> 0 in
  histo := IntMap.add size (1 + v) !histo
let pp_histo () =
  Log.info "Distribution of numerical states generated in Apron:";
  IntMap.iter (Log.info "  %d vars => %d num elements generated") !histo
module Abstract1_stat =
  (struct
    module A1 = Abstract1
    type 'a t = 'a A1.t
    (* Statistics *)
    let stat x =
      add_to_histo (Environment.size (A1.env x));
      x
    (* Functions for which no statistics is needed *)
    let is_bottom = A1.is_bottom
    let top = A1.top
    let env = A1.env
    let to_lincons_array = A1.to_lincons_array
    let is_leq = A1.is_leq
    let sat_tcons = A1.sat_tcons
    let bound_variable = A1.bound_variable
    (* Functions for which statistics are needed *)
    let change_environment m x e b   = stat (A1.change_environment m x e b)
    let rename_array m x a b         = stat (A1.rename_array m x a b)
    let meet_tcons_array m x c       = stat (A1.meet_tcons_array m x c)
    let join m xl xr                 = stat (A1.join m xl xr)
    let widening m xl xr             = stat (A1.widening m xl xr)
    let widening_threshold m xl xr t = stat (A1.widening_threshold m xl xr t)
    let assign_texpr_array m x l r o = stat (A1.assign_texpr_array m x l r o)
    let forget_array m x lv b        = stat (A1.forget_array m x lv b)
    let expand m x i a               = stat (A1.expand m x i a)
    let fold m x a                   = stat (A1.fold m x a)
    let meet m lx rx                 = stat (A1.meet m lx rx)
  end: ABSTRACT1_TYPE)

(** The functor to build the Apron domain *)
module Build_apron = functor (A: ABSTRACT1_TYPE) -> functor (PA: PRE_APRON) ->
  (struct
    (** Types; here we need the underlying definition of the domain *)
    type u = PA.t (* Underlying; abstract doamin of choice *)
    type t = u A.t (* Abstract domain instance *)

    (* General definitions *)
    let man = PA.man (* "Manager" for the abstract domain *)

    (* Bottom element *)
    let is_bot (x: t) = A.is_bottom man x
    (* Top element, with empty support *)
    let top: t =
      let env_empty = Environment.make [| |] [| |] in
      A.top man env_empty
    (* Pretty-printing *)
    let t_2stri (sn: sv_namer) (ind: string) (x: t): string =
      let s0 =
        if !Flags.flag_display_num_env then
          Printf.sprintf "%s%s\n" ind (environment_2str sn (A.env x))
        else "" in
      let s1 = linconsarray_2stri sn ind (A.to_lincons_array man x) in
      Printf.sprintf "%s%s" s1 s0

    (* Variables managemement *)
    let add_node (n: int) (x: t): t =
      let env_x = A.env x in
      if !Flags.flag_debug_num_env then
        Log.force "Add_node |%d|: %s" n (environment_2str IntMap.empty env_x);
      let env_n =
        try Environment.add env_x [| make_var n |] [| |]
        with e ->
          Log.fatal_exn "Add_node fails (%d): %s" n (Printexc.to_string e) in
      A.change_environment man x env_n false
    let rem_node (n: int) (x: t): t =
      let flag_loc = false in
      let env_x = A.env x in
      if !Flags.flag_display_num_env || flag_loc then
        Log.force "rem_node %d (Dim[env]=%d)\nbefore remove:\n%s"
          n (Environment.size env_x) (t_2stri IntMap.empty "   " x);
      let env_n = Environment.remove env_x [| make_var n |] in
      let r = A.change_environment man x env_n false in
      if !Flags.flag_display_num_env || flag_loc then
        Log.force "after remove:\n%s" (t_2stri IntMap.empty "   " r);
      r
    let get_env (x: t) = A.env x
    let change_env (e: Environment.t) (x: t): t =
      A.change_environment man x e false
    let vars_rename (m: int IntMap.t) (x: t): t =
      (* this function should be removed at some point *)
      let l_from, l_to =
        IntMap.fold
          (fun i_from i_to (acc_from, acc_to) ->
            let v_from = make_var i_from in
            let v_to   = make_var i_to in
            if Environment.mem_var (get_env x) v_from then
              v_from :: acc_from, v_to :: acc_to
            else acc_from, acc_to
          ) m ([ ], [ ]) in
      let a_from = Array.of_list l_from in
      let a_to   = Array.of_list l_to   in
      try
        A.rename_array man x a_from a_to
      with
      | exn ->
          Log.info "APRON RENAMING ISSUE\n%s\n%s"
            (environment_2str IntMap.empty (get_env x))
            (IntMap.t_2str "; " string_of_int m);
          raise exn
    let vars_srename (nr: 'a node_mapping) (x: t): t =
      if !Flags.flag_debug_num_env then
        Log.force "vars_srename: %s\n%s"
          (environment_2str IntMap.empty (get_env x)) (node_mapping_2str nr);
      let x = IntSet.fold rem_node nr.nm_rem x in
      (* first we reuse the classical rename function *)
      let m = IntMap.map fst nr.nm_map in
      let x0 = vars_rename m x in
      (* second, we add variables, with equality constraints *)
      let x1 =
        IntMap.fold
          (fun _ (i, s) ->
            IntSet.fold
              (fun j accx ->
                (* create node of index j, and asserts equality to i *)
                let nx = add_node j accx in
                let c =
                  translate_n_cons (get_env nx)
                    (Nc_cons (Lincons1.EQ,Ne_var i,Ne_var j)) in
                let eacons = Tcons1.array_make (get_env nx) 1 in
                Tcons1.array_set eacons 0 c;
                A.meet_tcons_array man nx eacons
              ) s
          ) nr.nm_map x0 in
      if !Flags.flag_debug_num_env then
        Log.force "vars_srename res: %s"
          (environment_2str IntMap.empty (get_env x1));
      x1

    (* Extracts the variables as a set of keys *)
    let get_svs (x: t): IntSet.t =
      let ai, af = Environment.vars (get_env x) in
      assert (Array.length af = 0);
      Array.fold_left
        (fun (acc: IntSet.t) (v: Var.t) ->
          IntSet.add (var_2int v) acc
        ) IntSet.empty ai
    let check_nodes (s: IntSet.t) (x: t): bool =
      let nvars = get_svs x in
      let n_not_s = IntSet.diff nvars s
      and s_not_n = IntSet.diff s nvars in
      if Flags.flag_sanity_env_pp then
        Log.info "apron,env: %s"
          (environment_2str IntMap.empty (get_env x));
      if n_not_s = IntSet.empty && s_not_n = IntSet.empty then true
      else
        begin
          IntSet.iter (Log.warn "|%d| in Num, not in Shape") n_not_s ;
          IntSet.iter (Log.warn "|%d| in Shape, not in Num") s_not_n ;
          false
        end
    let nodes_filter (nkeep: IntSet.t) (x: t): t =
      let nall = get_svs x in
      let nremove = IntSet.diff nall nkeep in
      let lremove = IntSet.fold (fun x l -> x :: l) nremove [ ] in
      let aremove = Array.of_list (List.map make_var lremove) in
      let env = A.env x in
      let nenv = Environment.remove env aremove in
      (* XR: this line seems to deteriorate the performance significantly
       *     (by about 10 %) *)
      A.change_environment man x nenv false

    (** Comparison and Join operators *)
    let is_le (x0: t) (x1: t) (sat_diseq: int -> int -> bool): bool =
      (* environments need be made homogeneous *)
      let e0 = get_env x0 and e1 = get_env x1 in
      let ee = Environment.lce e0 e1 in
      let cx0 = change_env ee x0 in
      let cx1 = change_env ee x1 in
      let b = A.is_leq man cx0 cx1 in
      if !Flags.flag_debug_is_le_num then
        Log.force "Nd_apron is_le returns %b\n%s\n%s" b
          (t_2stri IntMap.empty "   " cx0) (t_2stri IntMap.empty "  " cx1);
      b
    let join (xl: t) (xr: t): t =
      if !Flags.flag_debug_num_env || !Flags.flag_debug_join_num then
        Log.force "Numeric widening:";
      if !Flags.flag_debug_num_env then
        Log.force "Environments:\n - l: %s\n - r: %s"
          (environment_2str IntMap.empty (get_env xl))
          (environment_2str IntMap.empty (get_env xr));
      let xo = A.join man xl xr in
      if !Flags.flag_debug_join_num then
        Log.force " - l:\n%s - r:\n%s - o:\n%s"
          (t_2stri IntMap.empty "   " xl) (t_2stri IntMap.empty "   " xr)
          (t_2stri IntMap.empty "   " xo);
      xo
    let widen (xl: t) (xr: t): t =
      if !Flags.flag_debug_num_env || !Flags.flag_debug_join_num then
        Log.force "Numeric widening:";
      if !Flags.flag_debug_num_env then
        Log.force "Environments:\n - l: %s\n - r: %s"
          (environment_2str IntMap.empty (get_env xl))
          (environment_2str IntMap.empty (get_env xr));
      let xo =
        let xjr= A.join man xl xr in
        if !Flags.widen_do_thr then
          let thrs = make_widening_thresholds (get_env xl) in
          A.widening_threshold man xl xjr thrs
        else A.widening man xl xjr in
      if !Flags.flag_debug_join_num then
        Log.force " - l:\n%s - r:\n%s - o:\n%s"
          (t_2stri IntMap.empty "   " xl) (t_2stri IntMap.empty "   " xr)
          (t_2stri IntMap.empty "   " xo);
      xo

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (cons: n_cons) (t: t): bool =
      if cons = Nc_rand then false
      else
        let env = get_env t in
        let tcons = translate_n_cons env cons in
        let b = A.sat_tcons man t tcons in
        if !Flags.flag_debug_sat then
          begin
            Log.force "===========================";
            Log.force "Sat %s => %b" (n_cons_2str cons) b;
            Log.force " %s" (t_2stri IntMap.empty "  " t);
            Log.force "===========================";
          end;
        b

    (** Transfer functions *)
    let assign (dst: int) (expr: n_expr) (x: t): t =
      let v = make_var dst in
      if !Flags.flag_debug_num_apron then
        Log.force "assign %d <= %s\nbefore assign:\n%s" dst
          (n_expr_2str expr) (t_2stri IntMap.empty "  " x);
      let r =
        (* either call Apron's assign, or forget constraints over dst *)
        if n_expr_no_rand expr then
          (* no random sub-expression; perform an assignment *)
          let aexpr = translate_n_expr (get_env x) expr in
          if !Flags.flag_debug_num_apron then
            Log.force "translated expr: %s"
              (texpr1_2str IntMap.empty aexpr);
          A.assign_texpr_array man x [| v |] [| aexpr |] None
        else
          (* there is a random sub-expression; abstract away info about dst *)
          A.forget_array man x [| v |] false in
      if !Flags.flag_debug_num_apron then
        Log.force "after assign:\n%s" (t_2stri IntMap.empty "  " r);
      r

    let guard (b: bool) (cons: n_cons) (x: t): t =
      if cons = Nc_rand then x
      else
        let acons = translate_n_cons (get_env x) cons in
        let c =
          if b then acons
          else Log.todo_exn "apron negation" in
        let eacons = Tcons1.array_make (get_env x) 1 in
        Tcons1.array_set eacons 0 c;
        let nx = A.meet_tcons_array man x eacons in
        if Flags.do_raise_on_bottom && is_bot nx then raise Bottom
        else nx

    (** Utilities for the abstract domain *)
    let simplify_n_expr (t: t): n_expr -> n_expr =
      let rec aux (e: n_expr): n_expr =
        match e with
        | Ne_rand | Ne_cstc _ | Ne_csti _ -> e
        | Ne_var i ->
            let interv = A.bound_variable man t (make_var i) in
            if Scalar.cmp interv.Interval.inf interv.Interval.sup = 0 then
              Ne_csti (int_of_string (Scalar.to_string interv.Interval.inf))
            else e
        | Ne_bin (b, e0, e1) -> Ne_bin (b, aux e0, aux e1)
      in aux

    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another  *)
    let expand (id: int) (nid: int) (x: t): t =
      let id = make_var id in
      let nid = make_var nid in
      A.expand man x id [| nid |]
    (* Upper bound of the constraits of two dimensions *)
    let compact (lid: int) (rid: int) (x: t): t =
      let lid = make_var lid in
      let rid = make_var rid in
      A.fold man x [| lid; rid |]
    (* Meet: a lattice operation *)
    let meet (lx: t) (rx: t): t =
      A.meet man lx rx
    (* Forget the information on a dimension *)
    let forget (id: int) (x: t): t =
      let id = make_var id in
      A.forget_array man x [| id |] false

    (** Export of range information *)
    (* the bound of a variable *)
    let bound_variable (dim: int) (x: t): interval =
      let dim = make_var dim in
      let inter = A.bound_variable man x dim in
      let inf = 
        if Scalar.is_infty inter.Interval.inf <> 0 then
          None
        else
          match inter.Interval.inf with
          | Apron.Scalar.Float f -> Some (int_of_float f )
          | Apron.Scalar.Mpqf m -> Some (int_of_float (Mpqf.to_float m))
          | Apron.Scalar.Mpfrf m -> Some (int_of_float (Mpfrf.to_float m)) in
      let sup =
        if Scalar.is_infty inter.Interval.sup <> 0 then
          None
        else
          match inter.Interval.sup with
          | Scalar.Float f ->
              Some (int_of_float f)
          | Scalar.Mpqf m ->
              Some (int_of_float (Mpqf.to_float m))
          | Scalar.Mpfrf m ->
              Some (int_of_float (Mpfrf.to_float m)) in
      { intv_inf = inf;
        intv_sup = sup; }
  end: DOM_NUM_NB)
