(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_val_maya.ml
 **       Lifting a numeric domain to abstraction of possibly-empty sets
 ** Jiangchao Liu 2015/09/24 *)
open Data_structures
open Flags
open Lib
open Offs

open Dom_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Svenv_sig

open Dom_utils
open Graph_utils
open Nd_utils

(* Apron library needed here *)
open Apron


(** Error report *)
module Log =
  Logger.Make(struct let section = "dv_maya_" and level = Log_level.DEBUG end)

(* Preserved dim-names for special uses *)
let util_dim = 0
let tmp_size_dim = 1
let l_infity = 2
let r_infity = 3

(* Preserved dim-names for expanding summary variables *)
let tmp_dim: int ref = ref 3
let get_tmp_dim () =
  tmp_dim := !tmp_dim + 1;
  !tmp_dim
let reset_tmp_dim () =
  tmp_dim := 3

let global_namer: sv_namer ref = ref IntMap.empty

(** Module construction *)
module Make_Maya = functor (Dv: DOM_VALSET) ->
  (struct
    let module_name = "dom_val_maya"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name Dv.module_name (Dv.config_2str ())

    (* The type of a variable *)
    type sclset =
      | AlExist     (* Always More or equal than one value *)
      | AlSingle    (* Always  one value *)
      | Empty       (* No value *)
      | Single      (* One value *)
      | Exist       (* More or equal than one value *)
      | Any         (* More or equal than zero value *)

    (* Fresh real dim names *)
    let real_dim = 100

    (* Avatars of a variable *)
    let op_dim (var: int) =
      real_dim + (var * 4), real_dim + (var * 4) + 1

    let orig_dim (dim: int) =
      (dim - real_dim ) / 4

    (* Dim of size information of a variable *)
    let size_dim (var: int) =
      real_dim + (var * 4) + 2

    (** Querries on types of variables   *)
    let is_scalar (x: sclset): bool =
      match x with
      | AlExist
      | AlSingle -> true
      | _ -> false

    let is_scalar_single (x: sclset): bool =
      match x with
      | AlSingle -> true
      | _ -> false

    let is_scalar_exist (x: sclset): bool =
      match x with
      | AlExist -> true
      | _ -> false

    let is_set (s: sclset): bool =
      match s with
      | AlExist
      | AlSingle -> false
      | _ -> true

    let is_set_may_empty (s: sclset): bool =
      match s with
      | Empty
      | Any  -> true
      | _ -> false

    let is_set_empty (s: sclset): bool =
      match s with
      | Empty -> true
      | _ -> false

    let is_set_sum (s: sclset): bool =
      match s with
      | Any
      | Exist -> true
      | _ -> false

    (* Over-approximation of tow varialbe types *)
    let sclset_upper_bnd (l: sclset) (r: sclset): sclset =
      match l,r with
      | AlSingle, AlSingle -> AlSingle
      | AlExist, _
      | _, AlExist ->AlExist
      | Empty, Empty -> Empty
      | Single, Single -> Single
      | Exist, Exist
      | Exist, Single
      | Single, Exist -> Exist
      | _, _ -> Any

    (* Infer types from the range of the size of a variable *)
    let sclset_of_interval (isset: bool) (low: int) (up: int option): sclset =
      if isset then
        match low,up with
        | a, Some 0 when a < 1 -> Empty
        | 1, Some 1 -> Single
        | a, Some b when a > 0 && b > 1 -> Exist
        | a, None when a > 0 -> Exist
        | a, Some b when a < 1 && b > 0  -> Any
        | a, None when a < 1 -> Any
        | _, _ ->   Log.fatal_exn "illegale size detected"
      else
        match up with
        | Some 1 -> AlSingle
        | _ -> AlExist

    (** Some utils for type operations *)
    let low_bound_of_sclset (x: sclset): int =
      match x with
      | Empty
      | Any -> 0
      | _ -> 1

    let cons_of_interval (low: int) (up: int option) (id: int)
        : n_cons * n_cons=
      let lcons = Nc_cons (Tcons1.SUPEQ, Ne_var id, Ne_csti low) in
      match up with
      | None -> lcons, Nc_bool true
      | Some u -> lcons, Nc_cons (Tcons1.SUPEQ, Ne_csti u, Ne_var id)

    let dims_of_var (id: int) (s: sclset) =
      let l,r = op_dim id in
      let dims = IntSet.singleton l in
      if is_set s then IntSet.add r (IntSet.add (size_dim id) dims)
      else dims

    let is_equal (l: sclset) (r: sclset): bool =
      match l,r with
      | AlSingle,AlSingle
      | AlExist,AlExist
      | Empty,Empty
      | Single,Single
      | Any,Any
      | Exist,Exist -> true
      | _,_ -> false

    (* Pretty-printing only for varialbe types *)
    let sclset_2str (s: sclset): string =
      match s with
      | Empty ->  "Empty"
      | Single -> "Single"
      | Exist -> "Exist"
      | Any  ->  "Any"
      | AlSingle -> "AlSingle"
      | AlExist -> "AlExist"

    (** Defintion of abstract element *)
    type t =
        { (* The main numeric element  *)
          t_num:   Dv.t;
          (* The type of each dimension *)
          t_type:  sclset IntMap.t; }

    let var_is_non_empty (var: int) (x: t): bool =
      not (is_set_may_empty (IntMap.find var x.t_type))

    let get_namer (name: sv_namer) (x: t): unit =
      let var_str key =
        if IntMap.mem key name then IntMap.find key name
        else Pervasives.string_of_int key in
      let nname =
        IntMap.fold
          (fun key s cal ->
            let l,r = op_dim key in
            let size = size_dim key in
            if is_scalar s then IntMap.add l (var_str key) cal
            else
              let cal = IntMap.add size ((var_str key)^"#num") cal in
              let cal = IntMap.add r ((var_str key)^"(l)") cal in
              IntMap.add l ((var_str key)^"(u)") cal
          ) x.t_type IntMap.empty in
      global_namer := nname

    (** Pretty-printing *)
    let t_2stri (name: sv_namer) (ind: string) (x: t) =
      let var_str key =
        if IntMap.mem key name then IntMap.find key name
        else Pervasives.string_of_int key in
      let print_tuple key s cal =
        let str =
          if is_scalar s then
            Printf.sprintf "%s: %s\n" (var_str key) (sclset_2str s)
          else
            Printf.sprintf "%s: %s\n" (var_str key) (sclset_2str s) in
        cal^str in
      let nname =
        IntMap.fold
          (fun key s cal ->
            let l,r = op_dim key in
            let size = size_dim key in
            if is_scalar s then IntMap.add l (var_str key) cal
            else
              let cal = IntMap.add size ((var_str key)^"#num") cal in
              let cal = IntMap.add r ((var_str key)^"(l)") cal in
              IntMap.add l ((var_str key)^"(u)") cal
          ) x.t_type IntMap.empty in
      (IntMap.fold print_tuple x.t_type "")^(Dv.t_2stri nname ind x.t_num)

    (* Whether an empty variable exists in the expression *)
    let rec is_expr_empty (expr: n_expr) (x: t): bool =
      match expr with
      | Ne_rand -> false
      | Ne_csti csti -> false
      | Ne_cstc cstc -> false
      | Ne_var id ->  is_set_empty (IntMap.find id x.t_type)
      | Ne_bin (op, expr1, expr2) ->
          (is_expr_empty expr1 x) || (is_expr_empty expr2 x)

    (* Whether an may-empty variable exists in the expression *)
    let rec is_expr_may_empty (expr: n_expr) (x: t): bool =
      match expr with
      | Ne_rand -> false
      | Ne_csti csti -> false
      | Ne_cstc cstc -> false
      | Ne_var id -> is_set_may_empty (IntMap.find id x.t_type)
      | Ne_bin (op, expr1, expr2) ->
          (is_expr_may_empty expr1 x) || (is_expr_may_empty expr2 x)

    (* Whether summary variable (evaluates to more than one values) exists
     * in the expression*)
    let rec is_expr_sum (expr: n_expr) (x: t): bool =
      match expr with
      | Ne_rand -> false
      | Ne_csti csti -> false
      | Ne_cstc cstc -> false
      | Ne_var id -> is_set_sum (IntMap.find id x.t_type)
      | Ne_bin (op, expr1, expr2) ->
          (is_expr_sum expr1 x) || (is_expr_sum expr2 x)

    (* Bound every variable by two varaibles which are positive and negative
     * infinity respectively*)
    let bound_by_infity (inout: bool) (ldim: int) (rdim: int) (num:Dv.t)=
      let lcons = Nc_cons (Tcons1.SUP,Ne_csti (-10000000),Ne_var ldim) in
      let rcons = Nc_cons (Tcons1.SUP,Ne_var rdim,Ne_csti 10000000) in
      if inout then num else Dv.guard true rcons (Dv.guard true lcons num)

    (* Restore the independence property of a variable *)
    let recov_dim (ldim: int) (rdim: int) (tnum: Dv.t): Dv.t =
      let tnum =
        Dv.guard true (Nc_cons (Tcons1.EQ,Ne_var ldim,Ne_var rdim)) tnum in
      let tnum = Dv.sv_add util_dim tnum in
      let tnum =
        Dv.guard true (Nc_cons (Tcons1.SUPEQ,Ne_var util_dim,Ne_csti 0)) tnum in
      let tnum =
        Dv.assign rdim (Ne_bin (Texpr1.Add,Ne_var rdim,Ne_var util_dim)) tnum in
      let tnum = Dv.sv_rem util_dim tnum in
      let tnum = Dv.sv_add util_dim tnum in
      let tnum =
        Dv.guard true (Nc_cons (Tcons1.SUPEQ,Ne_var util_dim,Ne_csti 0)) tnum in
      let tnum =
        Dv.assign ldim (Ne_bin (Texpr1.Sub,Ne_var ldim,Ne_var util_dim)) tnum in
      let tnum = Dv.sv_rem util_dim tnum in
      bound_by_infity true ldim rdim tnum

    (* Restore all variables in an expression *)
    let recov_expr (expr: n_expr) (tps: sclset IntMap.t) (num: Dv.t): Dv.t =
      n_expr_fold
        (fun key anum ->
          if is_set_may_empty (IntMap.find key tps) then
            let ldim,rdim = op_dim key in
            recov_dim ldim rdim anum
          else anum
        ) expr num

    (* Merge two avatars into one *)
    let collapse_dim (id: int) (num: Dv.t): Dv.t =
      let ldim,rdim = op_dim id in
      let num =
        Dv.guard true (Nc_cons (Tcons1.EQ,Ne_var ldim,Ne_var rdim)) num in
      Dv.sv_forget rdim num

    (* Reset the size of a variable *)
    let reset_size_op (id: int) (s: sclset) (x: t): t =
      let osize = IntMap.find id x.t_type in
      let ldim,rdim = op_dim id in
      let num =
        match is_set_may_empty osize,is_set_may_empty s with
        | false, true ->
            let tn = Dv.assign rdim (Ne_var ldim) x.t_num in
            recov_dim ldim rdim tn
        | true, false -> collapse_dim id x.t_num
        | _ -> x.t_num in
      { t_type = IntMap.add id s x.t_type;
        t_num  = num }

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t =
      { t_num  = Dv.bot;
        t_type = IntMap.empty; }

    let is_bot (x: t): bool =
      Dv.is_bot x.t_num

    (* Assert that some variable is not empty *)
    let assert_non_empty (id: int) (x: t): t =
      let s = IntMap.find id x.t_type in
      assert(is_set s);
      let reduce_dim (id: int) (num: Dv.t) =
        let num = collapse_dim id num in
        Dv.guard true
          (Nc_cons (Tcons1.SUPEQ,Ne_var (size_dim id), Ne_csti 1))
          num in
      if is_set_empty s then bot
      else
        if is_set_may_empty s && is_set_sum s then
          let tp =
            IntMap.add id (sclset_of_interval (is_set s) 1 None) x.t_type in
          { t_type = tp;
            t_num  = reduce_dim id x.t_num }
        else x

    let is_var_in (var: int) (x: t) : bool =
      IntMap.mem var x.t_type
    (* Get the size information of a variable *)
    let size_of_var (var: int) (x: t): int * int option =
      let s_of_var = IntMap.find var x.t_type in
      assert(is_set s_of_var);
      if is_set_sum s_of_var then
        let intv = Dv.sv_bound (size_dim var) x.t_num in
        let low =
          match intv.intv_inf with
          | Some a when a >= 0 -> a
          | _ -> 0 in
        let assume_low = low_bound_of_sclset s_of_var in
        let low = if low < assume_low then assume_low else low in
        low,intv.intv_sup
      else
        let low = low_bound_of_sclset s_of_var in
        low, Some low

    (* Narrow the type of a vairable by the numeric information of its size *)
    let reduced_product_to_sclset (var: int) (x: t): t =
      if is_bot x then bot
      else
        let s = IntMap.find var x.t_type in
        if is_set s then
          let low,high = size_of_var var x in
          let ns = sclset_of_interval true low high in
          let num = if is_set_sum ns && not (is_set_sum s) then
            collapse_dim var x.t_num
          else x.t_num in
          { t_type = IntMap.add var ns x.t_type;
            t_num  = num; }
        else x

    (* Top element *)
    let top: t =
      { t_num = Dv.top;
        t_type = IntMap.empty }

    (** Management of symbolic variables *)
    let rem_node (id: int) (x: t): t =
      if is_bot x then x
      else
        let s = IntMap.find id x.t_type in
        let dims = dims_of_var id s in
        let nnum = IntSet.fold Dv.sv_rem dims x.t_num in
        { t_num  = nnum;
          t_type = IntMap.remove id x.t_type }

    let add_node (id: int) (isset: bool) (low: int) (up: int option) (x: t): t =
      let ldim,rdim = op_dim id in
      let num,ss =
        if isset then
          let s = sclset_of_interval true low up in
          let tnum = Dv.sv_add ldim (Dv.sv_add rdim x.t_num) in
          let is_emp = if is_set_empty s then false else true in
          let nnum = bound_by_infity is_emp ldim rdim tnum in
          let s_dim = size_dim id in
          let nnum = Dv.sv_add s_dim nnum in
          let nnum =
            let lcons,rcons = cons_of_interval low up s_dim in
            Dv.guard true lcons (Dv.guard true rcons nnum) in
          nnum, s
        else
          let nnum = Dv.sv_add ldim x.t_num in
          let s =  sclset_of_interval false low up in
          nnum, s in
      { t_num  = num;
        t_type = IntMap.add id ss x.t_type }

    (* Forget all constraints on a variable and reset its size *)
    let forget_reset_node (id: int) (isset: bool) (low: int) (up: int option)
        (x: t): t =
      let oisset = is_set (IntMap.find id x.t_type) in
      assert(oisset == isset);
      let x = rem_node id x in
      add_node id isset low up x

    (** Comparison and join operators *)
    (* The bound of a variable *)
    let bound_variable (var: int) (x: t): interval =
      let s = IntMap.find var x.t_type in
      if is_set_may_empty s then
        let ldim,rdim = op_dim var in
        let lbound = Dv.sv_bound ldim x.t_num in
        let rbound = Dv.sv_bound rdim x.t_num in
        { intv_inf = rbound.intv_inf;
          intv_sup = lbound.intv_sup }
      else
        let ldim, _ = op_dim var in
        Dv.sv_bound ldim x.t_num

    (* Reset the size of a scalar variable *)
    let scalar_to_single (var: int) (x: t): t =
      { x with t_type = IntMap.add var AlSingle x.t_type }

    let scalar_to_exist (var: int) (x: t): t =
      { x with t_type = IntMap.add var AlExist x.t_type }

    (* Reset the size of a variable by an expression, in the expression,
     * each set varialbe will be replaced by its size dim *)
    let size_assign (var: int) (expr: n_expr) (x: t): t =
      let lsize = IntMap.find var x.t_type in
      if is_scalar lsize then
        if expr = Ne_csti 1 then
          { x with t_type = IntMap.add var AlSingle x.t_type }
        else { x with t_type = IntMap.add var AlExist x.t_type }
      else
        let expr =
          n_expr_map
            (fun iv ->
              let is = IntMap.find iv x.t_type in
              if is_scalar_single is then fst (op_dim iv)
              else if is_set is then size_dim iv
              else Log.fatal_exn "scalar_exist found in size_assign\n"
            ) expr in
        let sdim_var = size_dim var in
        let nnum = Dv.assign sdim_var expr x.t_num in
        let intv = Dv.sv_bound sdim_var nnum in
        let low =
          match intv.intv_inf with
          | Some a when a >= 0-> a
          | _ -> 0 in
        let lnsize = sclset_of_interval true low intv.intv_sup in
        let x = { t_type = IntMap.add var lnsize x.t_type;
                  t_num  = nnum } in
        if is_equal lsize lnsize then x
        else
          if is_set_empty lsize || is_set_empty lnsize then
            forget_reset_node var true low intv.intv_sup x
          else
            match is_set_may_empty lsize,is_set_may_empty lnsize with
            | false, true ->
                let ldim,rdim = op_dim var in
                { x with t_num = recov_dim ldim rdim x.t_num }
            | true, false ->
                { x with t_num = collapse_dim var x.t_num }
            | _ -> x

    (* Constrain the size of variables *)
    let size_guard (cons: n_cons) (x: t): t =
      let scons =
        n_cons_map
          (fun iv ->
            let is = IntMap.find iv x.t_type in
            if is_scalar_single is then iv
            else if is_set is then size_dim iv
            else Log.fatal_exn "scalar_exist found in size_assign\n"
          ) cons in
      let nnum = Dv.guard true scons x.t_num in
      let x = { x with t_num = nnum } in
      n_cons_fold
        (fun iv tx ->
          if is_set (IntMap.find iv tx.t_type) then
            reduced_product_to_sclset iv tx
          else tx
        ) cons x

    (* Substitude the variables in expr by its avatars *)
    let rec var_subs (typ: bool) (expr: n_expr) (tp: sclset IntMap.t): n_expr =
      let choose =
        match typ with
        | true -> fst
        | false -> snd in
      let mapdim id =
        match is_set_may_empty (IntMap.find id tp) with
        | false -> fst (op_dim id)
        | true  -> choose (op_dim id) in
      match expr with
      | Ne_rand -> Ne_rand
      | Ne_csti csti -> Ne_csti csti
      | Ne_cstc cstc -> Ne_cstc cstc
      | Ne_var id -> Ne_var (mapdim id)
      | Ne_bin (op, expr1, expr2) ->
          match op with
          | Texpr1.Add ->
              Ne_bin (op, var_subs typ expr1 tp, var_subs typ expr2 tp)
          | Texpr1.Sub ->
              Ne_bin (op, var_subs typ expr1 tp, var_subs (not typ) expr2 tp)
          | Texpr1.Mul ->
              Ne_bin (op, var_subs typ expr1 tp, var_subs typ expr2 tp)
          | _ ->
              Log.fatal_exn
                "non linear expressions detected in var substitudtion"

    (* Check whether are there non linear part in the expression
     * also check is there a empty node *)
    let rec is_linear (expr: n_expr): bool =
      match expr with
      | Ne_rand -> true
      | Ne_csti csti -> true
      | Ne_cstc cstc -> true
      | Ne_var id -> true
      | Ne_bin (op, expr1, expr2) ->
          match op with
          | Texpr1.Add
          | Texpr1.Sub ->  (is_linear expr1) && (is_linear expr2)
          | Texpr1.Mul ->
              begin
                match expr1, expr2 with
                | Ne_csti _, Ne_var _ -> true
                | Ne_var _, Ne_csti _ -> true
                | _,_-> false
              end
          | _ ->  false

    (* Comparison *)
    let is_le (lx: t) (rx: t) =
      let nlx,nrx,flag =
        IntMap.fold
          (fun key ls (tlx,trx,tflag) ->
            if not tflag then tlx,trx,false
            else if is_set_empty ls then
              rem_node key tlx,rem_node key trx,tflag
            else if is_scalar ls then tlx,trx,tflag
            else
              let rs = IntMap.find key trx.t_type in
              match is_set_may_empty ls,is_set_may_empty rs with
              | true,false -> tlx,trx,false
              | false,true ->
                  let ldim,rdim = op_dim key in
                  { tlx with t_num = recov_dim ldim rdim tlx.t_num }, trx, tflag
              | _ -> tlx,trx,tflag
          ) lx.t_type (lx,rx,true) in
      flag && Dv.is_le nlx.t_num nrx.t_num (fun i j -> false)

    (* Upper bound: serves as join and widening *)
    let upper_bnd (akind: join_kind) (lx: t) (rx: t) =
      if is_bot lx then rx
      else if is_bot rx then lx
      else
        let size_wider (var: int) (os: sclset) (ns: sclset) (x: t): t =
          let x = {x with t_type = IntMap.add var ns x.t_type} in
          match (is_set_may_empty os), (is_set_may_empty ns) with
          | false,true ->
              let ldim,rdim = op_dim var in
              let tnum = recov_dim ldim rdim x.t_num in
              { x with t_num = tnum }
          | _ , _ -> x in
        let synchronize key ls (olx, orx) =
          let rs = IntMap.find key orx.t_type in
          let ns = sclset_upper_bnd ls rs in
          size_wider key ls ns olx, size_wider key rs ns orx in
        let nlx,nrx = IntMap.fold synchronize lx.t_type (lx, rx) in
        let x = { nlx with t_num = Dv.upper_bnd akind nlx.t_num nrx.t_num } in
        if akind = Jjoin then x
        else
          IntMap.fold
            (fun v s acc ->
              if is_set_may_empty s then
                size_guard (Nc_cons (Tcons1.SUPEQ,Ne_var v, Ne_csti 0)) acc
              else acc
            ) x.t_type x

    (* Substitude the variables in expr by its l or r dimensions and expand
     * summarized dimensions*)
    let rec expand_subs (typ:bool) (expr: n_expr) (tp: sclset IntMap.t)
        (num: Dv.t) (set: IntSet.t): n_expr * Dv.t * IntSet.t =
      let choose =
        match typ with
        | true -> fst
        | false -> snd in
      let mapdim id anum aset =
        let s_id = IntMap.find id tp in
        let tdim =
          if is_set_may_empty s_id then choose (op_dim id)
          else fst (op_dim id) in
        if is_set_sum s_id || is_scalar_exist s_id then
          let fresh_dim = get_tmp_dim () in
          let anum = Dv.expand tdim fresh_dim anum in
          let aset = IntSet.add fresh_dim aset in
          fresh_dim,anum,aset
        else tdim,anum,aset in
      match expr with
      | Ne_rand -> Ne_rand,num,set
      | Ne_csti csti -> Ne_csti csti, num, set
      | Ne_cstc cstc -> Ne_cstc cstc, num, set
      | Ne_var id ->
          let tdim,num,set = mapdim id num set in
          (Ne_var tdim),num,set
      | Ne_bin (op, expr1, expr2) ->
          match op with
          | Texpr1.Add ->
              let nexpr1,num,set = expand_subs typ expr1 tp num set in
              let nexpr2,num,set = expand_subs typ expr2 tp  num set in
              Ne_bin (op, nexpr1, nexpr2), num, set
          | Texpr1.Sub ->
              let nexpr1,num,set = expand_subs typ expr1 tp num set in
              let nexpr2,num,set = expand_subs (not typ) expr2 tp num set in
              Ne_bin (op, nexpr1, nexpr2), num, set
          | Texpr1.Mul ->
              let nexpr1,num,set = expand_subs typ expr1 tp num set in
              let nexpr2,num,set = expand_subs typ expr2 tp num set in
              Ne_bin (op, nexpr1, nexpr2), num, set
          | _ ->
              Log.fatal_exn
                "non linear expressions detected in var substitudtion"

    (* Drop a set of dimensions *)
    let drop_dims (set: IntSet.t) (num: Dv.t): Dv.t =
      IntSet.fold Dv.sv_rem set num

    (* General implementation of guard *)
    let rec guard (is_s: bool) (typ: bool) (cons: n_cons) (x: t): t =
      reset_tmp_dim ();
      match cons with
      | Nc_rand -> x
      | Nc_bool true -> x
      | Nc_bool false -> bot
      | Nc_cons (op, expr1, expr2) ->
          if (is_linear expr1) && (is_linear expr2)
              && not (is_expr_empty expr1 x)
              && not (is_expr_empty expr2 x) then
            match op,typ with
            | Tcons1.SUP,_
            | Tcons1.SUPEQ,_ ->
                if is_s then
                  let nexpr1 = var_subs (not typ) expr1 x.t_type in
                  let nexpr2 = var_subs typ expr2 x.t_type in
                  let n = Dv.guard typ (Nc_cons (op, nexpr1, nexpr2)) x.t_num in
                  { x with t_num = n }
                else
                  let nexpr1,anum,aset =
                    expand_subs (not typ) expr1 x.t_type x.t_num IntSet.empty in
                  let nexpr2,anum,aset =
                    expand_subs typ expr2 x.t_type  anum aset in
                  let anum = Dv.guard typ (Nc_cons (op, nexpr1, nexpr2)) anum in
                  let anum = drop_dims aset anum in
                  { x with t_num = anum }
            | Tcons1.EQ,true
            | Tcons1.DISEQ,false ->
                let x =
                  guard is_s true (Nc_cons (Tcons1.SUPEQ,expr1,expr2)) x in
                let x =
                  guard is_s true (Nc_cons (Tcons1.SUPEQ,expr2,expr1)) x in
                if is_s then
                  let nexpr1 = var_subs true expr1 x.t_type in
                  let nexpr2 = var_subs true expr2 x.t_type in
                  let do_eq ( ) =
                    let num =
                      Dv.guard true
                        (Nc_cons (Tcons1.EQ, nexpr1, nexpr2)) x.t_num in
                    { x with t_num = num } in
                  begin
                    match expr1, expr2 with
                    | Ne_var v0, Ne_var v1 ->
                        if var_is_non_empty v0 x
                            && var_is_non_empty v1 x then do_eq ( )
                        else x
                    | Ne_var v0, Ne_csti c0
                    | Ne_csti c0, Ne_var v0 ->
                        if  var_is_non_empty v0 x then do_eq ( )
                        else x
                    | _ -> x
                  end else x
            | Tcons1.EQ,false
            | Tcons1.DISEQ,true ->
                let guard_sub (ty: bool) (tx: t) =
                  let nexpr1 = var_subs ty expr1 tx.t_type  in
                  let nexpr2 = var_subs (not ty) expr2 tx.t_type  in
                  let num1 =
                    Dv.guard true (Nc_cons (Tcons1.SUP, nexpr1, nexpr2))
                      tx.t_num in
                  let num2 =
                    Dv.guard true (Nc_cons (Tcons1.SUP, nexpr2, nexpr1))
                      tx.t_num in
                  let numa = Dv.upper_bnd Jjoin num1 num2 in
                  let numa =
                    Dv.guard true
                      (Nc_cons (Tcons1.DISEQ, nexpr2, nexpr1)) numa in
                  { tx with t_num = numa } in
                let guard_sub_w (ty: bool) (tx: t) =
                  let nexpr1,anum,aset =
                    expand_subs ty expr1 tx.t_type tx.t_num IntSet.empty in
                  let nexpr2,anum,aset =
                    expand_subs (not ty) expr2 tx.t_type anum aset in
                  let num1 =
                    Dv.guard true (Nc_cons (Tcons1.SUP, nexpr1, nexpr2)) anum in
                  let num2 =
                    Dv.guard true (Nc_cons (Tcons1.SUP, nexpr2, nexpr1)) anum in
                  let anum = Dv.upper_bnd Jjoin num1 num2 in
                  let anum = drop_dims aset anum in
                  { tx with t_num = anum } in
                if is_s then guard_sub (not typ) (guard_sub typ x)
                else guard_sub_w (not typ) (guard_sub_w typ x)
            | Tcons1.EQMOD _, _ -> x
          else x

    (* Guard, strong version
     * we do not need to modify the t_type part, because if the pre-conditin
     * is Single, it cannot be Empty in post-condition *)
    let rec guard_s (typ: bool) (cons: n_cons) (x: t): t =
      guard true typ cons x

    (* Guard, weak version  *)
    let rec guard_w (typ: bool) (cons: n_cons) (x: t): t =
      guard false typ cons x

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let rec sat_s (x: t) (cons: n_cons) =
      match cons with
      | Nc_rand -> Log.fatal_exn "undefined operation in sat_s"
      | Nc_bool b -> b
      | Nc_cons (op, expr1, expr2) ->
          if is_linear expr1 && is_linear expr2
              && not (is_expr_empty expr1 x)
              && not (is_expr_empty expr2 x) then
            match op with
            | Tcons1.SUP
            | Tcons1.SUPEQ ->
                let nexpr1 = var_subs false expr1 x.t_type in
                let nexpr2 = var_subs true expr2 x.t_type in
                Dv.sat x.t_num  (Nc_cons (op, nexpr1, nexpr2))
            | Tcons1.EQ ->
                let nexpr1 = var_subs false expr1 x.t_type in
                let nexpr2 = var_subs false expr2 x.t_type in
                Dv.sat x.t_num (Nc_cons (Tcons1.EQ,nexpr1,nexpr2))
            | Tcons1.DISEQ ->
                let nexpr1 = var_subs true expr1 x.t_type in
                let nexpr2 = var_subs true expr2 x.t_type in
                Dv.sat x.t_num (Nc_cons (op, nexpr1, nexpr2)) ||
                sat_s x (Nc_cons (Tcons1.SUP,expr1,expr2)) ||
                sat_s x (Nc_cons (Tcons1.SUP,expr2,expr1))
            | Tcons1.EQMOD _ ->
                false
          else
            false

    (* Get all variables that equal to the current one *)
    let get_eq_class (i: int) (x: t): IntSet.t =
      if var_is_non_empty i x then
        let iset = Dv.get_eq_class (fst (op_dim i)) x.t_num in
        IntSet.fold (fun key -> IntSet.add (orig_dim key)) iset IntSet.empty
      else
        IntSet.empty

    (* Weak sat *)
    let sat_w (x: t) (cons: n_cons) =
      reset_tmp_dim ();
      match cons with
      | Nc_rand -> Log.fatal_exn "Nc_rand case in sat_w"
      | Nc_bool b-> b
      | Nc_cons (op, expr1, expr2) ->
          if (is_linear expr1) && (is_linear expr2)
              && not (is_expr_empty expr1 x)
              && not (is_expr_empty expr2 x) then
            match op with
            | Tcons1.SUP ->
                not (sat_s x (Nc_cons (Tcons1.SUPEQ,expr2,expr1)))
            | Tcons1.SUPEQ ->
                not (sat_s x (Nc_cons (Tcons1.SUP,expr2,expr1)))
            | Tcons1.EQ ->
                not (sat_s x (Nc_cons (Tcons1.DISEQ,expr2,expr1)))
            | Tcons1.DISEQ ->
                not (sat_s x (Nc_cons (Tcons1.EQ,expr2,expr1)))
            | Tcons1.EQMOD _ -> Log.fatal_exn "models in sat_w"
          else false

    (* Assignment, strong update version, the size of lval in the result
     * is decided by the expression*)
    let update_subs_set (id: int) (expr: n_expr) (x: t): t =
      reset_tmp_dim ();
      let s_of_id = IntMap.find id x.t_type in
      let isset = is_set s_of_id in
      if is_expr_empty expr x then
        forget_reset_node id isset 0 (Some 0) x
      else if not (is_linear expr) then
        if is_expr_may_empty expr x then
          forget_reset_node id isset 0 (Some 1) x
        else forget_reset_node id isset 1 (Some 1) x
      else
        let ldim,rdim = op_dim id  in
        if is_expr_may_empty expr x then
          let exprt,anum,aset =
            expand_subs true expr x.t_type  x.t_num IntSet.empty in
          let exprf,anum,aset =
            expand_subs false expr x.t_type  anum aset in
          let tmp_dim_t = get_tmp_dim () in
          let tmp_dim_f = get_tmp_dim () in
          let anum =
            Dv.sv_add tmp_dim_t (Dv.sv_add tmp_dim_f anum) in
          let anum = Dv.assign tmp_dim_t exprt anum in
          let anum = Dv.assign tmp_dim_f exprf anum in
          let anum = drop_dims aset anum in
          let anum = Dv.assign ldim (Ne_var tmp_dim_t) anum in
          let anum = Dv.assign rdim (Ne_var tmp_dim_f) anum in
          let anum =
            Dv.sv_rem tmp_dim_t (Dv.sv_rem tmp_dim_f anum) in
          let anum = recov_dim ldim rdim anum in
          let anum = recov_expr expr x.t_type anum in
          let s_dim = size_dim id in
          let ns = sclset_of_interval true 0 (Some 1) in
            let anum =
              Dv.guard true
                (Nc_cons (Tcons1.SUPEQ,Ne_var s_dim,Ne_csti 0))
                (Dv.guard true (Nc_cons (Tcons1.SUPEQ,Ne_csti 0,Ne_var s_dim))
                   (Dv.sv_forget s_dim anum)) in
            { t_num  = anum;
              t_type = IntMap.add id ns x.t_type }
        else
          let nexpr,anum,aset =
            expand_subs true expr x.t_type  x.t_num IntSet.empty in
          let anum =
            if is_set_may_empty s_of_id then Dv.sv_forget rdim anum
            else anum in
          let ns = sclset_of_interval isset 1 (Some 1) in
          let anum = bound_by_infity true ldim ldim
              (Dv.assign ldim nexpr anum) in
          let anum = drop_dims aset anum in
          let x =  { t_num  = anum;
                     t_type = IntMap.add id ns x.t_type} in
          size_assign id (Ne_csti 1) x

    (* Assignment, weak update version  *)
    let update_add (id: int) (expr: n_expr) (x: t): t =
      reset_tmp_dim ();
      let id_size = IntMap.find id x.t_type in
      let isset = is_set id_size in
      if is_expr_empty expr x then x
      else if not (is_linear expr) then
        forget_reset_node id isset 0 None x
      else
        let ldim,rdim = op_dim id  in
        if is_expr_may_empty expr x then
          let exprt,anum,aset =
            expand_subs true expr x.t_type  x.t_num IntSet.empty in
          let exprf,anum,aset =
            expand_subs false expr x.t_type  anum aset in
          let tmp_dim_t = get_tmp_dim () in
          let tmp_dim_f = get_tmp_dim () in
          let anum = Dv.sv_add tmp_dim_t (Dv.sv_add tmp_dim_f anum) in
          let anum = Dv.assign tmp_dim_t exprt anum in
          let anum = Dv.assign tmp_dim_f exprf anum in
          let anum = drop_dims aset anum in
          let anum =
            if is_set_may_empty id_size then
              let tnum = Dv.compact ldim tmp_dim_t anum in
              let tnum = Dv.compact rdim tmp_dim_f tnum in
              recov_dim ldim rdim tnum
            else
              let tnum =
                Dv.guard true
                  (Nc_cons (Tcons1.EQ,Ne_var tmp_dim_t,Ne_var tmp_dim_f))
                  anum in
              let tnum =
                Dv.sv_rem tmp_dim_f tnum in
              Dv.compact ldim tmp_dim_t tnum in
          let anum = recov_expr expr x.t_type anum in
          let x = { x with t_num = anum} in
          let nx =
            size_assign id (Ne_bin (Texpr1.Add,Ne_var id,Ne_csti 1)) x in
          upper_bnd Jjoin x nx
        else
          let nexpr,anum,aset =
            expand_subs true expr x.t_type  x.t_num IntSet.empty in
          let tmp_dim_t = get_tmp_dim () in
          let anum = Dv.sv_add tmp_dim_t anum in
          let anum = Dv.assign tmp_dim_t nexpr anum in
          let anum = Dv.compact ldim tmp_dim_t anum in
          let anum =
            if is_set_may_empty  id_size then
              let tmp_dim_f = get_tmp_dim () in
              let tnum = Dv.sv_add tmp_dim_f anum in
              let tnum = Dv.assign tmp_dim_f nexpr tnum in
              Dv.compact rdim tmp_dim_f tnum
            else anum in
          let anum = drop_dims aset anum in
          let x = { x with t_num = bound_by_infity true ldim ldim anum } in
          if isset then
            size_assign id (Ne_bin (Texpr1.Add,Ne_var id,Ne_csti 1)) x
          else { x with t_type = IntMap.add id AlExist x.t_type }

    (* Remove a value from a set *)
    let update_rem (id: int) (expr: n_expr) (x: t): t =
      reset_tmp_dim ();
      let o_size = IntMap.find id x.t_type in
      assert(is_set o_size);
      if is_expr_may_empty expr x || is_expr_sum expr x then x
      else
        let x = size_assign id (Ne_bin (Texpr1.Sub,Ne_var id,Ne_csti 1)) x in
        let post_size = IntMap.find id x.t_type in
        let ldim,rdim = op_dim id  in
        let anum =
          if is_set_may_empty post_size then
            let anum = x.t_num in
            let nexpr = var_subs false expr x.t_type   in
            let num1 =
              Dv.guard true (Nc_cons (Tcons1.SUP, Ne_var rdim, nexpr)) anum in
            let num2 =
              Dv.guard true (Nc_cons (Tcons1.SUP, nexpr, Ne_var rdim)) anum in
            Dv.upper_bnd Jjoin num1 num2
          else
            let anum = x.t_num in
            let nexpr = var_subs false expr x.t_type in
            let num1 =
              Dv.guard true (Nc_cons (Tcons1.SUP, Ne_var ldim, nexpr)) anum in
            let num2 =
              Dv.guard true (Nc_cons (Tcons1.SUP, nexpr, Ne_var ldim)) anum in
            Dv.upper_bnd Jjoin num1 num2 in
        let nexpr = var_subs true expr x.t_type in
        let num1 =
          Dv.guard true (Nc_cons (Tcons1.SUP, Ne_var ldim, nexpr)) anum in
        let num2 =
          Dv.guard true (Nc_cons (Tcons1.SUP, nexpr, (Ne_var ldim))) anum in
        let anum = Dv.upper_bnd Jjoin num1 num2 in
        { x with t_num = anum }

    (* Assignment, strong update version, the size of lval in the result
     * does not change, actually, this function is a hack way which saves
     * the cost of asserting that expression could not be empty *)
    let update_subs_elt (id: int) (expr: n_expr) (x: t): t =
       reset_tmp_dim ();
      let id_size = IntMap.find id x.t_type in
      if is_set_empty id_size || is_set_sum id_size
          || is_scalar_exist id_size then
        let x = update_add id expr x in
        { x with t_type = IntMap.add id id_size x.t_type }
      else
        let ldim,_ = op_dim id in
        if is_expr_may_empty expr x then begin
          let exprt,anum,aset =
            expand_subs true expr x.t_type x.t_num IntSet.empty in
          let exprf,anum,aset = expand_subs false expr x.t_type anum aset in
          let anum = Dv.assign ldim exprt anum in
          let anum =
            Dv.guard true (Nc_cons (Tcons1.EQ,Ne_var ldim,exprf)) anum in
          let anum = drop_dims aset anum in
          let anum = recov_expr expr x.t_type anum in
          { x with t_num = anum } end
        else
          let nexpr,anum,aset =
            expand_subs true expr x.t_type  x.t_num IntSet.empty in
          let anum =
            bound_by_infity true ldim ldim (Dv.assign ldim nexpr anum) in
          let anum = drop_dims aset anum in
          { x with t_num = anum }

    (* Copy the information from a variable to another *)
    let expand (oid: int) (nid: int) (x: t): t =
      let oldim,ordim = op_dim oid in
      let nldim,nrdim = op_dim nid in
      let osdim = size_dim oid in
      let nsdim = size_dim nid in
      let otype = IntMap.find oid x.t_type in
      let nm = Dv.expand oldim nldim x.t_num in
      let nm =
        if is_set_may_empty otype then Dv.expand ordim nrdim nm
        else nm in
      let nm =
        if is_set otype then Dv.expand osdim nsdim nm
        else nm in
      { t_type = IntMap.add nid otype x.t_type;
        t_num = nm }

    (* Rename a variable *)
    let rename_var (oid: int) (nid: int) (x: t): t =
      let rename_dim (old: int) (frh: int) (x: Dv.t) =
        let rename_map =
          { nm_map    = IntMap.singleton old (frh,IntSet.empty);
            nm_rem    = IntSet.empty;
            nm_suboff = fun _ -> false; } in
        Dv.symvars_srename OffMap.empty rename_map None x in
      let oldim,ordim = op_dim oid in
      let nldim,nrdim = op_dim nid in
      let osdim = size_dim oid in
      let nsdim = size_dim nid in
      let osize = IntMap.find oid x.t_type in
      let nn = rename_dim oldim nldim x.t_num in
      let nn =
        if is_set osize then
          rename_dim ordim nrdim (  rename_dim osdim nsdim nn )
        else nn in
      { t_type = IntMap.add nid osize (IntMap.remove oid x.t_type);
        t_num = nn}

    (* Filter variables *)
    let symvars_filter (vars: IntSet.t) (x: t): t =
      let dims =
        IntSet.fold
          (fun var acc ->
            let s = IntMap.find var x.t_type in
            IntSet.union acc (dims_of_var var s)
          ) vars IntSet.empty in
      { t_type = IntMap.filter (fun key _ -> IntSet.mem key vars) x.t_type;
        t_num = Dv.symvars_filter dims x.t_num }

    (* Forget the information about an SV *)
    let sv_forget (var: int) (x: t): t =
      let s =  (IntMap.find var x.t_type) in
      let dims = dims_of_var var s in
      { x with t_num = IntSet.fold Dv.sv_forget dims x.t_num }

    (* Merge the informaiton of two variables to one *)
    let compact (l: int) (r: int) (x: t): t =
      let ls = IntMap.find l x.t_type in
      let rs = IntMap.find r x.t_type in
      let lldim,lrdim = op_dim l in
      let rldim,rrdim = op_dim r in
      let rsdim = size_dim r in
      match is_set ls, is_set rs with
      | false, false ->
          let tnum = Dv.assign lldim (Ne_var rldim) x.t_num in
          let tnum = Dv.upper_bnd Jjoin x.t_num tnum in
          let tnum = Dv.sv_rem rldim tnum in
          { t_type = IntMap.add l AlExist (IntMap.remove r x.t_type);
            t_num  = tnum }
      | true, true ->
          begin
            if is_set_empty rs then rem_node r x
            else if is_set_empty ls then rename_var r l (rem_node l x)
            else
              let x = size_assign
                  l (Ne_bin (Texpr1.Add,Ne_var l, Ne_var r)) x in
              let x = {x with t_type = IntMap.remove r x.t_type} in
              let ls = IntMap.find l x.t_type in
              let nn = Dv.sv_rem rsdim x.t_num in
              match is_set_may_empty ls,is_set_may_empty rs with
              | false,false ->
                  let nnn = Dv.assign lldim (Ne_var rldim) nn in
                  let nn = Dv.upper_bnd Jjoin nn nnn in
                  let nn = Dv.sv_rem rldim nn in
                  (** atttenion  *)
                  (* you cannt use compact since there is a bug here.
                      with case test-slist1.c *)
                   let nn = Dv.sv_rem rrdim nn in
                  { x with t_num = nn }
              | true,true ->
                  let nnn = Dv.assign lldim (Ne_var rldim) nn in
                  let nn = Dv.upper_bnd Jjoin nn nnn in
                  let nn = Dv.sv_rem rldim nn in
                  let nnn = Dv.assign lrdim (Ne_var rrdim) nn in
                  let nn = Dv.upper_bnd Jjoin nn nnn in
                  let nn = Dv.sv_rem rrdim nn in
                  { x with t_num = nn }
              | false,true ->
                  let nn = collapse_dim r nn in
                  let nnn = Dv.assign lldim (Ne_var rldim) nn in
                  let nn = Dv.upper_bnd Jjoin nn nnn in
                  let nn = Dv.sv_rem rldim nn in
                  let nn = Dv.sv_rem rrdim nn in
                  { x with t_num = nn }
              | true,false -> Log.fatal_exn "unexpected case in compact"
          end
      | _,_ -> Log.fatal_exn "non compatible case"

    (* Narrow the type of all set variables from numeric information *)
    let narrow_set_vars (x: t) : t =
      IntMap.fold
        (fun var s acc ->
          if is_set_may_empty s then
            let low,up = size_of_var var acc in
            let ns = sclset_of_interval true low up in
            if is_set_may_empty ns then acc
            else
              let nn = collapse_dim var x.t_num in
              { t_type = IntMap.add var ns acc.t_type;
                t_num = nn }
          else acc
        ) x.t_type x

    (* Comparision: variable-wise subset, for each concrete state
     * clx from lx, it exists a concrete state crx from rx, that each variable
     * in clx is a subset of those in crx*)
    let is_incl (lx: t) (rx: t): bool =
      let synchronize key ls (olx,orx,flag) :t * t * bool =
        if not flag then olx, orx, false
        else
          let rs = IntMap.find key orx.t_type in
          if is_set_empty ls then rem_node key olx, rem_node key orx, flag
          else if is_set_empty rs then olx, orx, false
          else if is_scalar ls then  olx, orx, flag
          else
            let llow, lup = size_of_var key olx in
            let rlow, rup = size_of_var key orx in
            match lup, rup with
            | None , Some b -> olx,orx,false
            | Some a, Some b when a > b -> olx, orx, false
            | _, _ ->
                let tlx = assert_non_empty key olx in
                let trx = assert_non_empty key orx in
                let rem_size tkey ts tx: t =
                  if is_set_sum ts then
                    { tx with t_num = Dv.sv_rem (size_dim tkey) tx.t_num}
                  else tx in
                rem_size key ls tlx, rem_size key rs trx, flag in
      let nlx, nrx, flag = IntMap.fold synchronize lx.t_type (lx, rx, true) in
      if flag then Dv.is_le nlx.t_num nrx.t_num (fun i j -> false)
      else false
  end: DOM_MAYA)
