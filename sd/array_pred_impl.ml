(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: array_pred_impl.ml
 **       lifting of a numerical domain into an array abstraction
 ** Jiangchao Liu 2014/09/23 *)
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
open Dom_val_maya
open Array_pred_utils 
open Array_pred_sig

(* Apron library needed here *)
open Apron

module Log =
  Logger.Make(struct let section = "ap_impl_" and level = Log_level.DEBUG end)

(** Symbolic variables for predicates  *)
let symbo_counter: int ref = ref 500000000
let get_new_symbo () =
  symbo_counter := !symbo_counter + 1;
  !symbo_counter


type com_intf =
    { head_index: int;
      tail_index: int;
      tail_succ: int; }


(** In Map:(group,field) -> dimension. take size and index as special feilds. *)
let g_size  = -1
let g_index = -2



(* module IndexRe = functor (DV: DOM_VALUE) -> *)
(*   (struct *)
(*     module Op = Make_Maya (Dv) *)
(*     type t =  IntSet.t IntMap.t;  *)
(*     let t_2stri (x: t) (dims :(int * int, int) Bi_fun.t): string =  *)
(*       IntMap.fold *)
(*         (fun di set acc -> *)
(*           let (g,f) = Bi_fun.inverse_inj di dims in *)
(*           let oline = *)
(*             Printf.sprintf *)
(*               "\n (%d,%d) <- %s \n" *)
(*               g f (intset_2str set ) in *)
(*           acc ^ oline *)
(*         ) x "Index Relations:\n" *)

(*     let is_le (lres: t) (rres: t): bool =  *)
(*         IntMap.fold *)
(*         (fun var set acc -> *)
(*           acc && ( not (IntMap.mem var lres)  *)
(*                  || IntSet.subset (IntMap.find var lres) set) *)
(*         ) rres true  *)

(*     let join (lres: t) (rres: t) =  *)
(*      let set_join key ls rs = *)
(*         match ls, rs with *)
(*         | None, _ -> None *)
(*         | _, None -> None *)
(*         | Some l, Some r -> Some (IntSet.union l r) in *)
(*      IntMap.merge set_join lres rres *)

(*     let intra_joinrank (x: t) (l_id: int) (r_int: int) (fields: int IntMap.t)  *)
(*         (dims :(int * int, int) Bi_fun.t) : int=  *)
(*         IntMap.fold *)
(*           (fun key off wacc-> *)
(*             let l_dim = Bi_fun.image (l_id,key) dims in *)
(*             let r_dim = Bi_fun.image (r_id,key) dims in *)
(*             let l_set = try IntMap.find l_dim x.t_indexRes with Not_found -> IntSet.empty in *)
(*             let r_set = try IntMap.find r_dim x.t_indexRes with Not_found -> IntSet.empty in *)
(*             let relation_score = if IntSet.equal l_set r_set then 1 else 0 in  *)
(*             relation_score + wacc *)
(*           ) t_fields 0  *)
            
(*     let split (g_id: int) (ng_id: int) (x: t) (fields: int IntMap.t) *)
(*         (dims :(int * int, int) Bi_fun.t): t =  *)
(*       let refreshS elt = *)
(*         if IntSet.mem g_id elt then IntSet.add ng_id elt *)
(*         else elt in *)
(*       let nindexRes = IntMap.map refreshS x.t_indexRes in *)
(*       let nindexRes = *)
(*         IntMap.fold *)
(*           (fun key _ acc -> *)
(*             let ori_fld_dim = Bi_fun.image (g_id, key) dims in *)
(*             if IntMap.mem ori_fld_dim acc then *)
(*               let tSet = IntMap.find ori_fld_dim acc in *)
(*               let new_fld_dim = Bi_fun.image (ng_id, key) dims in *)
(*               IntMap.add new_fld_dim tSet acc *)
(*             else acc *)
(*           ) fields x  *)
(*   end: ARRAY_PREDICATE) *)


module Make_StaticList (Op:DOM_MAYA): ARRAY_PREDICATE with type gd = Op.t =
  struct
    type com_intf =
        { head_index: int;
          tail_index: int;
          tail_succ:  int; }
    type t =
        { t_intf:  com_intf IntMap.t;
          t_apred: apred; }
    type gd = Op.t
         
    let t_2stri (ind: string) (x: t): string =
      IntMap.fold 
        (fun ig dims acc ->
          Printf.sprintf "%s %d : head-> %d ; tail -> %d; tail_succ -> %d "
            acc ig dims.head_index dims.tail_index dims.tail_succ
        ) x.t_intf ind 

    let initialize (ap: apred) = 
      { t_intf  = IntMap.empty;
        t_apred = ap; }

    let is_applicable (ap: apred) = true

    (** Transfer predicates to n_cond or n_expr *)
    let tr_lval (dims: (int * int, int) Bi_fun.t) (alv: alval) (group: int)
        (x: t): n_expr =
      match alv with
      | Avar av ->
          begin
            match av with
            | Rv_var v_id -> Ne_var v_id
            | _ -> Log.fatal_exn "unresolved predicate "
          end
      | Aarray_strut (av, al, ao) ->
          begin
            match ao with
            | Rv_off aoi -> Ne_var (Bi_fun.image (group, aoi) dims)
            | _ -> Log.fatal_exn "unresolved predicate "
          end
      | Aident ide -> Ne_var (Bi_fun.image (group, g_index) dims)
      | _  -> Log.fatal_exn "unresolved predicate"

    let tr_lval_for_cond (alv: alval) (group: int) (x: t): n_expr = 
      match alv with
      | Avar av ->
          begin
            match av with
            | Rv_var v_id -> Ne_var v_id
            | _ -> Log.fatal_exn "unresolved predicate "
          end
      | Aident ide -> 
          begin
            let intf = IntMap.find group x.t_intf in
            match ide with
            | Acur -> Ne_var intf.tail_index
            | Asucc -> Ne_var intf.tail_succ 
          end
      | _  -> Log.fatal_exn "unresolved predicate"

    let tr_arbop (op: a_arbop): Texpr1.binop =
      match op with
      | Abadd -> Texpr1.Add
      | Absub -> Texpr1.Sub
      | Abmul -> Texpr1.Mul
      | Abmod -> Texpr1.Mod

    let tr_compop (op: a_combop):bool * Tcons1.typ = 
      match op with
      | Abne -> true,Tcons1.DISEQ
      | Abeq -> true,Tcons1.EQ
      | Abge -> true,Tcons1.SUPEQ
      | Abgt -> true,Tcons1.SUP
      | Able -> false,Tcons1.SUP
      | Ablt -> false,Tcons1.SUPEQ 
            

    let rec tr_expr (dims: (int * int, int) Bi_fun.t) (aexp: aexpr)
        (group: int) (x: t): n_expr = 
      match aexp with
      | Aelval alv -> tr_lval dims alv group x
      | Aeconst con -> Ne_csti con
      | Aebin (arop, ae1, ae2) -> 
          Ne_bin ((tr_arbop arop),(tr_expr dims ae1 group x),
                  (tr_expr dims ae2 group x))
      | _ -> Log.fatal_exn "Minus operator in tr_expr"

    let rec tr_expr_for_cond (aexp: aexpr) (group: int) (x: t): n_expr =
      match aexp with
      | Aelval alv -> tr_lval_for_cond alv group x
      | Aeconst con -> Ne_csti con
      | _ -> Log.todo_exn "more expression in tr_expr_for_cond"

    let rec tr_cond (acon: acond) (group: int) (x: t) : bool * n_cons =
      match acon with
      | Arith (acomp,ae1,ae2) ->
          let is_true,ntype = tr_compop acomp in
          is_true, Nc_cons (ntype,tr_expr_for_cond ae1 group x,
                            tr_expr_for_cond ae2 group x)
      | Logic (alop,acon1,acon2) ->
          Log.todo_exn "logic operator in tr_cond"

    let materialize (dims: (int * int, int) Bi_fun.t)
        (group: int) (main: Op.t) (x: t): Op.t * t = 
      Log.info "materialize in staticlist is called";
      let comp =
        match x.t_apred with
        | Comp com -> com 
        | _ -> Log.fatal_exn " " in
      let comp = List.hd comp in
      let intf = { head_index = get_new_symbo ();  
                   tail_index = get_new_symbo ();
                   tail_succ  = get_new_symbo (); } in
      let main = Op.add_node intf.head_index false 1 (Some 1) main in
      let main = Op.add_node intf.tail_index false 1 (Some 1) main in
      let main = Op.add_node intf.tail_succ false 1 (Some 1) main in
      let indexexpr =Ne_var (Bi_fun.image (group,g_index) dims) in
      let main = Op.update_subs_elt intf.head_index indexexpr main in
      let main = Op.update_subs_elt intf.tail_index indexexpr main in
      let succexpr = tr_expr dims comp.succ group x in
      let main = Op.update_subs_elt intf.tail_succ succexpr main in
      let x = { x with t_intf = IntMap.add group intf x.t_intf } in
      main,x

    (* Update the parameters of a predicate when the group attached with this
     * predicate has been modified*)
    let assign_simple (dims:(int * int, int) Bi_fun.t)
        (group: int) (main: Op.t) (x: t):  Op.t * t = 
      if IntMap.mem group x.t_intf then
        begin
          Log.info "attach predicate is called";
          let comp =
            match x.t_apred with
            | Comp com -> com 
            | _ -> Log.fatal_exn "numeric predicate in StaticList" in
          let comp = List.hd comp in
          let intf = IntMap.find group x.t_intf in
          let succexpr = tr_expr dims comp.succ group x in
          let main = Op.update_subs_elt intf.tail_succ succexpr main in
          main, x
        end
      else
        Log.fatal_exn "impossible case in update predicate"

     (* Remove the preciate attached to a group *)
    let rem_predicate (group: int) (main: Op.t)  (x: t): Op.t * t= 
      if (IntMap.mem group x.t_intf) then
        let intf = IntMap.find group x.t_intf in
        let main = Op.rem_node intf.head_index main in
        let main = Op.rem_node intf.tail_index main in
        let main = Op.rem_node intf.tail_succ main in
        main,{ x with t_intf = IntMap.remove group x.t_intf }
      else
        main, x
          
      (*Remove predicates attached to all groups *)
    let rem_all_predicates (main: Op.t) (x: t): Op.t * t= 
      let nmain =
        IntMap.fold 
          (fun key intf acc ->
            let ta = Op.rem_node intf.head_index acc in
            let ta = Op.rem_node intf.tail_index ta in
            Op.rem_node intf.tail_succ ta
          ) x.t_intf main in
      nmain,{ x with t_intf = IntMap.empty }

      (* Rearrange the parameters of the predicates of merged groups  *)
    let merge (lg: int) (rg: int) (main: Op.t) (x: t): Op.t * t = 
      match IntMap.mem lg x.t_intf, IntMap.mem rg x.t_intf with
      | false,false -> main, x
      | false,true -> rem_predicate rg main x
      | true,false -> rem_predicate lg main x
      | true,true ->
          let is_connected (tg1: int) (tg2: int): bool = 
            let lintf = IntMap.find tg1 x.t_intf in
            let rintf = IntMap.find tg2 x.t_intf in
            let cond1 = 
              Nc_cons 
                (Tcons1.SUP,Ne_var lintf.tail_succ,Ne_var rintf.head_index) in
            let cond2 = 
              Nc_cons 
                (Tcons1.SUP,Ne_var lintf.head_index,Ne_var rintf.tail_succ) in
            Op.is_bot (Op.guard_s true cond1 main)
              && Op.is_bot (Op.guard_s true cond2 main) in
          let conn_pred (tg1: int) (tg2: int)  (tmain: Op.t) (tx: t)
              : Op.t * t= 
            let tlintf = IntMap.find tg1 x.t_intf in
            let trintf = IntMap.find tg2 x.t_intf in
            let nlintf = { tlintf with
                           tail_succ = trintf.tail_succ;
                           tail_index = trintf.tail_index } in
            let nrintf = { trintf with
                           tail_succ = tlintf.tail_succ;
                           tail_index = tlintf.tail_index } in
            let ncpred = IntMap.add tg1 nlintf tx.t_intf in
            let ncpred = IntMap.add tg2 nrintf ncpred in
            let tx = { tx with t_intf = ncpred } in
            rem_predicate tg2 tmain tx in
          if is_connected lg rg then
            conn_pred lg rg main x 
          else if is_connected rg lg then
            conn_pred rg lg main x 
          else let main,x = rem_predicate lg main x in
          rem_predicate rg main x 

    (* Rename the parameters of predicates, enable to join and widen *)
    let rename (lg: int) (rg: int) (fresh: int) (lm: Op.t) (lx: t)
       (rm: Op.t) (rx: t) :  Op.t * t * Op.t * t = 
      match IntMap.mem lg lx.t_intf, IntMap.mem rg rx.t_intf with
      | false,false ->lm,lx,rm,rx
      | false,true -> let rm,rx = rem_predicate rg rm rx in lm,lx,rm,rx
      | true,false -> let lm,lx = rem_predicate lg lm lx in lm,lx,rm,rx
      | true,true ->
          let lintf = IntMap.find lg lx.t_intf in
          let rintf = IntMap.find rg rx.t_intf in
          let rename_index (li: int) (ri: int) (tlm: Op.t) (trm: Op.t) = 
            if li = ri then
              li,tlm,trm
            else
              let fi = get_new_symbo () in
              let tlm = Op.rename_var li fi tlm in
              let trm = Op.rename_var ri fi trm in
              fi,tlm,trm in
          let fhead_index,lm,rm =
            rename_index lintf.head_index rintf.head_index lm rm in
          let ftail_index,lm,rm =
            rename_index lintf.tail_index rintf.tail_index lm rm in
          let ftail_succ,lm,rm =
            rename_index lintf.tail_succ rintf.tail_succ lm rm in
          let fintf = { head_index = fhead_index;
                        tail_index = ftail_index;
                        tail_succ  = ftail_succ } in
          let lcompred = IntMap.add fresh fintf (IntMap.remove lg lx.t_intf) in
          let rcompred = IntMap.add fresh fintf (IntMap.remove rg rx.t_intf) in
          lm,{ lx with t_intf = lcompred },rm,{ rx with t_intf = rcompred }
  
    let joinrank (l_id: int) (r_id: int) (x: t): int= 
      if (IntMap.mem l_id x.t_intf)
          = IntMap.mem r_id x.t_intf then
        1 else 0
    
    let pred_check (dims: (int * int, int) Bi_fun.t) (main: Op.t) (x: t): bool =
      match x.t_apred with
      | Comp compr ->
          let comp = List.hd compr in
          if IntMap.is_empty x.t_intf then false
          else 
            let group,intf = IntMap.min_binding x.t_intf in
            let typ,tailcons = tr_cond comp.exitcond group x in
            let headcons =
              Nc_cons (Tcons1.EQ,(Ne_var intf.head_index),
                       tr_expr dims comp.head group x) in
            assert typ;
            Op.sat_s main headcons && Op.sat_s main tailcons
      | _ -> Log.todo_exn "numeric pred on array_check"
 
    let is_incl_group (lg: int) (rg: int) (lx: t) (rx: t): bool =
      IntMap.mem lg lx.t_intf || not (IntMap.mem rg rx.t_intf)
  end


