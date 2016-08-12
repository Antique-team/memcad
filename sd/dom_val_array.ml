(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_val_array.ml
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
open Array_pred_impl
open Array_node

(* Apron library needed here *)
open Apron

module Log =
  Logger.Make(struct let section = "dv_array" and level = Log_level.DEBUG end)

(** Node type *)
type node_type =
  | Nt_array_content
  | Nt_array_address
  | Nt_scalar




(* Temp names for array cells in expressions,  *)
let cell_counter: int ref = ref 110000000
let get_cell () =
  cell_counter := !cell_counter + 1;
  !cell_counter
let cell_reset  () =
  cell_counter := 110000000





(** Module construction *)
module Make_Val_Array = functor (Dv: DOM_VALUE)  ->
  (struct
    module Op = Make_Maya( Dv )
    module A = Array_Node( Op )
    type t =
        { (* The main numeric element  *)
          t_main:   Op.t;
          (* Array node information *)
          t_arrays: A.t IntMap.t;
          (* Types of all nodes *)
          t_type:   node_type IntMap.t;
          (* The records of the summary dimensions in expression
           * during the transfer function for assigment and guard *)
          t_cells: (int,onode) Bi_fun.t;
          (* The records of the summary dimeisions in l-value during
           * the transfer function for assigment *)
          t_lval: int option; }


    (** Pretty-printing *)

    let t_2stri (namemap: sv_namer) (ind: string) (x: t) =
      ljc_debug "t_2stri is called\n";
      let p_main =
        (Op.t_2stri
           (IntMap.fold A.get_namer x.t_arrays IntMap.empty) ind x.t_main) in
      let p_array =
        IntMap.fold (fun _ anode acc -> acc ^ (A.t_2stri "" anode))
          x.t_arrays "" in
      p_array ^ "------The main numeric element\n" ^ p_main


   (** Utils **)

   (* Check whehter a node is a summary one *)
   let is_scalar (id: int) (x: t): bool =
     try
       let tp = IntMap.find id x.t_type in
       match tp with
       | Nt_scalar -> true
       | _ -> Log.fatal_exn "invalid node in expression"
     with
     | _ -> false

    (* Remove those groups that contains 0 elements *)
    let cleanup (x: t): t =
      ljc_debug "cleanup is called\n";
      IntMap.fold
        (fun key array acc ->
          let narray,nmain = A.cleanup array x.t_main in
          let narrays = IntMap.add key narray x.t_arrays in
          { acc with
            t_arrays = narrays;
            t_main = nmain; }
        ) x.t_arrays x

    (* Find the group  which the array cell is in, if there are several
     * groups the  array cell might be in, we create disjunctions*)
    let deref_in_expr (expr_l: n_expr list) (x: t)
        : (n_expr list * t) list =
      let replace onum dnum arg = if onum = arg then dnum else arg in
      Bi_fun.fold_dom
        (fun cell nd parceds ->
          let id,off = nd in
          List.fold_left
            (fun acc (texpr_l, tx) ->
              let array = IntMap.find id tx.t_arrays in
              let postdef = A.deref_in_expr off tx.t_main array in
              let postdef =
                List.map
                  (fun (dim, tmain, tarray) ->
                    let arrays = IntMap.add id tarray tx.t_arrays in
                    let nx = {tx with
                              t_arrays = arrays;
                              t_main = tmain} in
                    let nexpr_l =
                      List.map (n_expr_map (replace cell dim)) texpr_l in
                    nexpr_l, nx
                  ) postdef in
              postdef @ acc
            ) [] parceds
        ) x.t_cells [ (expr_l, x) ]


    (** Lattice elements *)

    (* Bottom element *)
    let bot: t =
      { t_main = Op.bot;
        t_arrays = IntMap.empty;
        t_type = IntMap.empty;
        t_cells = Bi_fun.empty_inj;
        t_lval = None ;}

    let is_bot (x: t): bool =
      ljc_debug "is_bot is called\n";
      if Op.is_bot x.t_main then true
      else
        IntMap.fold (fun key anode acc -> acc || A.is_bot x.t_main anode)
          x.t_arrays false

    (* (\* Minix 1.1 global state *\) *)
    (* let minix: t ref = ref bot  *)


    (* Top element *)
    let top: t =
      ljc_debug "top is called\n";
      { t_main = Op.top;
        t_arrays = IntMap.empty;
        t_type = IntMap.empty;
        t_cells = Bi_fun.empty_inj;
        t_lval = None;}


    (** Management of symbolic variables *)

    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (a: Keygen.t) (b: StringSet.t) = a

    (* For sanity check *)
    let check_nodes (s: IntSet.t) (x: t): bool =
      ljc_debug "check_nodes is called\n";
      false

    (* Node addition and removal *)
    let add_node (id: int) (x: t): t =
      ljc_debug "add_node is called \n";
      let m = Op.add_node  id false 1 (Some 1) x.t_main in
      let tp = IntMap.add id Nt_scalar x.t_type in
      let x = { x with
                t_main = m;
                t_type = tp; } in
      x

    let rem_node (id: int) (x: t): t =
      ljc_debug "rem_node is called \n";
      match IntMap.find id x.t_type with
      | Nt_scalar
      | Nt_array_address ->
          { x with
            t_main = Op.rem_node id x.t_main;
            t_type = IntMap.remove id x.t_type }
      | Nt_array_content ->
          let array = IntMap.find id x.t_arrays in
          { x with
            t_main = A.rem_dims array x.t_main;
            t_type = IntMap.remove id x.t_type;
            t_arrays = IntMap.remove id x.t_arrays }

    (* Renaming (e.g., post join) *)
    let symvars_srename
        (a: (Offs.t * int) OffMap.t)
        (b: (int * Offs.t) node_mapping)
        (x: t): t =
      ljc_debug "symvars_srename is called\n";
      x

    (* Synchronization of the SV environment *)
    let sve_sync_top_down (a: svenv_mod) (x: t): t =
      ljc_debug "sve_sync_top_down is called\n";
      x

    (* Check the symbolic vars correspond exactly to given set *)
    let symvars_check (a:IntSet.t) (x:t): bool =
      ljc_debug "symvars_check is called\n";
      false

    (* Removes all symbolic vars that are not in a given set *)
    let symvars_filter (a: IntSet.t) (x: t): t =
      ljc_debug "svyvars_filter is called\n";
      x

    let symvars_merge (a: int) (b: int) (c: int)
        (d: (Bounds.t * onode * Offs.size) list) (e: OffSet.t) (x: t): t =
      ljc_debug "symvars_merge is called\n";
      x


    (** Summarizing dimensions related operations  *)

    (* Copy the constrains on id to nid
     * (nid should not be in the environment before)  *)
    let expand (id: int) (nid: int) (x: t): t =
     Log.fatal_exn "expand"
     (* { x with t_main = Dv.expand id nid x.t_main } *)

    (* Find the upper bound of contraints on lid and rid,
     * give it to lid and remove rid  *)
    let compact (lid: int) (rid: int) (x: t): t =
      Log.fatal_exn "compact"

    let meet (lx: t) (rx: t): t =
      Log.todo_exn "dom_val_array meet"

    (* Forget the constraints on a dimension *)
    let forget (id: int) (x: t): t =
      Log.todo_exn "forget"


    (** Comparison and join operators *)

    (* Comparision for two states with  groups of same names *)
    let flat_is_le (lx: t) (rx: t): bool =
      ljc_debug "flat le is called\n";
      if is_bot lx then true
      else
        if is_bot rx then false
        else
          let arrayle =
            IntMap.fold
              (fun key larray acc ->
                if not acc then acc
                else
                  let rarray = IntMap.find key rx.t_arrays in
                  A.flat_is_le larray rarray
              ) lx.t_arrays true in
          arrayle && (Op.is_le lx.t_main rx.t_main)

    (* Join for two states with  groups of same names *)
    let flat_join (lx: t) (rx: t): t =
      (* Format.printf "flat_join  is called\n"; *)
      (* Format.printf "lx is \n %s\n" (t_2stri IntMap.empty "" lx); *)
      (* Format.printf "rx is \n %s\n" (t_2stri IntMap.empty "" rx); *)
      if is_bot lx then rx
      else
        if is_bot rx then lx
        else
          let narrays =
            IntMap.mapi
              (fun key larray ->
                let rarray = IntMap.find key rx.t_arrays in
                A.flat_join larray rarray
              ) lx.t_arrays in
          let nmain = Op.upper_bnd Jjoin lx.t_main rx.t_main in
          { lx with
            t_main = nmain;
            t_arrays = narrays;
            t_cells = Bi_fun.empty_inj; }

    (* Widen for two states with  groups of same names *)
    let flat_widen (lx: t) (rx: t): t =
      if is_bot lx then rx
      else
        if is_bot rx then lx
        else
          let narrays =
            IntMap.mapi
              (fun key larray ->
                let rarray = IntMap.find key rx.t_arrays in
                A.flat_join larray rarray
              ) lx.t_arrays in
          let nmain = Op.upper_bnd Jwiden lx.t_main rx.t_main in
          let nmain =
            IntMap.fold (fun _ array acc -> A.base_index_cons array acc)
              narrays nmain in
          { lx with
            t_main   = nmain;
            t_arrays = narrays;
            t_cells  = Bi_fun.empty_inj; }




    (* Comparison *)
    let is_le (lx: t) (rx: t) (sat_diseq: int -> int -> bool) =
      ljc_debug "is_le is called\n";
      let rem_pred (x : t) : t =
        IntMap.fold
          ( fun key array acc ->
            let main,array = A.rem_all_predicates  acc.t_main array in
            let arrays = IntMap.add key array acc.t_arrays in
            {acc with t_arrays = arrays;t_main = main}
           ) x.t_arrays x in
      let lx = rem_pred lx in
      let rx = rem_pred rx in
      let lx,rx,jud =
        IntMap.fold
          (fun key larray acc ->
            let ltx, rtx, judge = acc in
            if judge then acc
            else
              let rarray = IntMap.find key rx.t_arrays in
              let map,judge = A.inclmap larray lx.t_main rarray rx.t_main in
              Log.debug "inclmap:\n%s" (ljc_map_2str map);
              if judge then
                ltx, rtx, true
              else
                let nlm,nlarr,nrm,nrarr =
                  A.apply_inclmap map larray ltx.t_main rarray rtx.t_main in
                let nlarrays = IntMap.add key nlarr ltx.t_arrays in
                let nrarrays = IntMap.add key nrarr rtx.t_arrays in
                let nlx = { ltx with
                            t_main   = nlm;
                            t_arrays = nlarrays } in
                let nrx = { rtx with
                            t_main   = nrm;
                            t_arrays = nrarrays } in
                nlx,nrx,false
          ) lx.t_arrays (lx, rx, false) in
      tmp_dim_reset ();
      not jud && (flat_is_le lx rx)

    (* Upper bound: serves as join and widening *)
    let upper_bnd (akind: join_kind) (lx: t) (rx: t) =
    let lx,rx =
        IntMap.fold
          (fun key larray acc ->
            let ltx,rtx = acc in
            let rarray = IntMap.find key rx.t_arrays in
            let rankmap = A.rankscore larray lx.t_main rarray rx.t_main in
            Log.debug "rank score is:\n%s" (ljc_rankscore_2str rankmap);
            let nlm,nlarr,nrm,nrarr =
              match akind with
              | Jjoin ->
                  A.apply_joinmap rankmap larray ltx.t_main rarray rtx.t_main
              | Jwiden ->
                  A.apply_widenmap rankmap larray ltx.t_main rarray rtx.t_main
              | Jdweak -> Log.fatal_exn "weak is not implemented" in
            let nlarrays = IntMap.add key nlarr ltx.t_arrays in
            let nrarrays = IntMap.add key nrarr rtx.t_arrays in
            let nlx = { ltx with
                        t_main = nlm;
                        t_arrays = nlarrays } in
            let nrx = { rtx with
                        t_main = nrm;
                        t_arrays = nrarrays } in
            nlx, nrx
          ) lx.t_arrays (lx, rx) in
      let result =
        match akind with
        | Jjoin -> flat_join lx rx
        | Jwiden -> flat_widen lx rx
        | jdweak -> Log.fatal_exn "weak is not implemented\n" in
      result


    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (x: t) (cons: n_cons) =
      Op.sat_s x.t_main cons

    let print_cells (cells: (int,onode) Bi_fun.t) : string =
      Log.fatal_exn "print_cells is called"
        (* Bi_fun.t_2strf Pervasives.string_of_int onode_2str cells *)


    (** Condition test *)

    (* Specially deal with the case1 mproc[child].parent == child,
     * and child \relmem G_3 *)
    (* This file will be eliminated after new materialization is implemented *)
    let special_guard (cons: n_cons) (x: t): t * bool =
      let special_body (iseq: Tcons1.typ) (v1: int) (v2: int) (x: t): t * bool =
        let id,off = Bi_fun.image v1 x.t_cells in
        let array = IntMap.find id x.t_arrays in
        let array,main,b = A.split_on_guard iseq array x.t_main off v2 in
        if b then
          { x with
            t_main= main;
            t_arrays = IntMap.add id array x.t_arrays;
            t_cells = Bi_fun.empty_inj;
            t_lval = None},true
       else x, false in
      match cons with
      | Nc_cons (Tcons1.EQ as is,Ne_var v1,Ne_var v2)
      | Nc_cons (Tcons1.DISEQ as is,Ne_var v1,Ne_var v2) ->
          begin
            match is_scalar v1 x, is_scalar v2 x with
            | true, false -> special_body is v2 v1 x
            | false, true -> special_body is v1 v2 x
            | _ -> x, false
          end
      | _ -> x, false

    (* The main algorithm of guard*)
    let guard_body (typ: bool) (cons: n_cons) (x: t): t =
      if not typ then
        Log.fatal_exn "unexpected false condition in guard"
      else
        match cons with
        | Nc_rand -> Log.fatal_exn "Nc_rand appears in guard function"
        | Nc_bool true -> x
        | Nc_bool false -> bot
        | Nc_cons (tb, expr1, expr2) ->
            let is_expr1_sum =
              n_expr_fold
                (fun iv acc -> acc ||(not (is_scalar iv x))) expr1 false in
            let is_expr2_sum =
              n_expr_fold
                (fun iv acc -> acc ||(not (is_scalar iv x))) expr2 false in
            match is_expr1_sum, is_expr2_sum with
            | false, false ->
                let tmain =
                  (Op.guard_s typ cons x.t_main) in
                let tmain =
                  Op.narrow_set_vars tmain in
                let arrays =
                  IntMap.map (A.guard typ cons x.t_main) x.t_arrays in
                let x = { x with
                          t_main   = tmain;
                          t_arrays = arrays;
                          t_cells  = Bi_fun.empty_inj; } in
                let x = cleanup x in
                if is_bot x then bot
                else x
            | _,_ ->
                let disjuncts = deref_in_expr [expr1;expr2] x in
                let disjuncts =
                  List.map
                    (fun (expr_l,x) ->
                      tmp_dim_reset ();
                      (* Format.printf "in each case of the guard, x is \n %s\n" *)
                      (*   (t_2stri IntMap.empty "" x); *)
                      let texpr1 = List.hd expr_l in
                      let texpr2 = List.hd (List.tl expr_l) in
                      let ncons = Nc_cons (tb,texpr1,texpr2) in
                      let nmain = Op.guard_w typ ncons x.t_main in
                      let x = { x with
                                t_main = nmain;
                                t_cells = Bi_fun.empty_inj ;
                                t_lval = None } in
                      let x = cleanup x in
                      if is_bot x then bot
                      else x
                    ) disjuncts in
                List.fold_left flat_join bot disjuncts

    (* Guard, before enter guard_body, pre-process "unequal" and the
     * "special_guard" *)
    let guard (typ: bool) (cons: n_cons) (x:t): t =
      Log.debug "guard is called the cons is %s" (n_cons_2str cons) ;
      Log.debug "before guard x is \n %s" (t_2stri IntMap.empty "" x);
      cell_reset ();
      let x,isspecial = special_guard cons x in
      if isspecial then x
      else
        let result =
          match cons with
          | Nc_cons (Tcons1.DISEQ, e1, e2) ->
              let cons1 = Nc_cons (Tcons1.SUP, e1, e2) in
              let cons2 = Nc_cons (Tcons1.SUP, e2, e1) in
              flat_join (guard_body typ cons1 x) (guard_body typ cons2 x)
          | _ -> guard_body typ cons x in
        Log.debug "after guard is \n %s" (t_2stri IntMap.empty "" result);
       result


    (** Assignment *)
    let assign (id: int) (expr: n_expr) (x: t): t =
      (* The general case, not include the specific cases *)
      ljc_debug "assign is called \n";
      cell_reset ();
      let is_dst_sum = not (is_scalar id x) in
      let forget_indexRes dim ar =
        IntMap.map (A.forget_indexRe dim) ar in
      let is_expr_sum =
        n_expr_fold (fun iv acc -> acc || (not (is_scalar iv x))) expr false in
      match is_expr_sum, is_dst_sum with
      | false, false ->
          let arrays = IntMap.map (A.assign id expr) x.t_arrays in
          let nmain  = Op.update_subs_elt id expr x.t_main in
          let arrays = IntMap.map (A.num_2rl nmain id) arrays in
          { x with
            t_main = nmain;
            t_arrays = arrays;
            t_cells = Bi_fun.empty_inj}
      | false, true ->
          let dst =
            match x.t_lval with
            | Some d -> d
            | None -> Log.fatal_exn "array cell as lval but not stored" in
          (* find where the array dst is in *)
          let a_id,a_b =
            IntMap.fold
              (fun key arr acc ->
                let acc_id,acc_b = acc in
                if acc_b then acc
                else
                  if A.is_dimension_in dst arr then key, true
                  else 0, false
              ) x.t_arrays (0, false) in
          let array = IntMap.find a_id x.t_arrays in
          let nmain = Op.update_subs_elt dst expr x.t_main in
          let array = A.num_2rl_sum dst expr nmain array in
          let group = A.get_group_by_dim dst array in
          let array,nmain = A.assign_for_predicate group nmain array in
          { x with
            t_main   = nmain;
            t_arrays = IntMap.add a_id array x.t_arrays;
            t_cells  = Bi_fun.empty_inj ;
            t_lval   = None }
      | true, _ ->
          let disjuncts = deref_in_expr [expr] x in
          let disjuncts =
            List.map
              (fun (expr_l, tx) ->
                let expr = List.hd expr_l in
                if is_dst_sum then
                  let dst =
                    match x.t_lval with
                    | Some d -> d
                    | None ->
                        Log.fatal_exn "array cell as lval but not stored" in
                  let nmain = Op.update_subs_elt dst expr tx.t_main in
                  { tx with
                    t_main   = nmain;
                    t_arrays = forget_indexRes id x.t_arrays;
                    t_cells  = Bi_fun.empty_inj;
                    t_lval   = None }
                else
                  let nmain = Op.update_subs_elt id expr tx.t_main in
                  let arrays = IntMap.map (A.propagate id expr) x.t_arrays in
                  { x with
                    t_main   = nmain;
                    t_arrays = arrays;
                    t_cells  = Bi_fun.empty_inj;
                   t_lval    = None }
              ) disjuncts in
          List.fold_left flat_join bot disjuncts

    (* Assignment inside a sub-memory *)
    let write_sub (a: sub_dest) (b: int) (c: n_rval) (x: t): t =
      ljc_debug "write_sub is called\n";
      x


    (** Utilities for the abstract domain *)
    let simplify_n_expr (x: t) (a: n_expr): n_expr =
      ljc_debug "simplify_n_expr is called\n";
      a


    (** Array-domain specific functions  *)

    (* Add an array address node  *)
    let add_array_address (id: int) (x: t) =
      ljc_debug "add_array_address node is called \n";
      let m = Op.add_node id false 1 (Some 1) x.t_main in
      let tp = IntMap.add id Nt_array_address x.t_type in
      { x with
        t_main = m;
        t_type = tp; }

    (* Add an array content node  *)
    let add_array_node (id:int) (size:int) (fields:int list) (x:t) =
      ljc_debug "add_array_node is called \n";
      (* for now, we just add all variables into the subvar  *)
      let anode,nm =
        A.fresh_array_node id size fields x.t_main  in
      let arrays = IntMap.add id anode x.t_arrays in
      { t_main   = nm;
        t_arrays = arrays;
        t_type   = IntMap.add id Nt_array_content x.t_type ;
        t_cells  = Bi_fun.empty_inj;
        t_lval   = None;}

    (* Checks wheter this node is the address of an array node *)
    let is_array_address (id: int) (x: t): bool =
      let ty = IntMap.find id x.t_type in
      match ty with
      | Nt_array_address -> true
      | _ -> false

    (* Dereference an array cell in experision,
     * this function may cause disjunction *)
    let array_node_deref (id: int) (off: Offs.t) (x: t): (t * int) list =
      if (Bi_fun.mem_inv (id,off) x.t_cells) then
        let cell = Bi_fun.inverse_inj (id,off) x.t_cells in
        [ x, cell ]
      else
        let ncell = get_cell () in
        let ncells = Bi_fun.add ncell (id,off) x.t_cells in
        [ {x with t_cells = ncells}, ncell ]

    (* Dereference an array cell in l-value,
     * no disjunction is created since it merges groups *)
    let array_materialize (id: int) (off: Offs.t) (x: t): t * int =
      Log.debug "array_materialize is called";
      if !is_hint_resolved = false  then
          match !hint_array_pred with
          | None -> ();
          | Some unbinded_pred ->
              begin
                Log.debug "before bind";
                let binded_array_pred =
                  (apred_bind_by_env !varm !deref unbinded_pred) in
                hint_array_pred := Some binded_array_pred;
                is_hint_resolved := true;
                Log.debug "after bind by env is \n %s"
                  (apred_2str binded_array_pred)
              end
      else ();
      let array = IntMap.find id x.t_arrays in
      let array, main, dim = A.materialize  array off x.t_main in
      let arrays = IntMap.add id array x.t_arrays in
      let x =
        { x with
          t_arrays = arrays;
          t_main   = main;
          t_lval   = Some dim} in
      x, dim


    (* The bound of a variable. *)
    let bound_variable (id: int) (x: t): interval =
      Log.fatal_exn "bound_variable in array"


    (** Sub-memory specific functions *)
    (* Checks whether a node is of sub-memory type *)
    let is_submem_address (id: int) (x: t): bool =
      Log.fatal_exn "is_submem_address is called\n"

    let is_submem_content (id: int) (x: t): bool =
      Log.fatal_exn "is_submem_content is called\n"


    (* Read of a value inside a submemory block *)
    let submem_read (a: n_cons -> bool) (b: int) (c: Offs.t) (d: int)
        (x: t): onode =
      Log.fatal_exn "submem_read is called\n"

    let submem_deref
        (a: n_cons -> bool) (b: int) (c: Offs.t) (d: int) (x: t):onode =
      Log.fatal_exn "submem_deref is called\n"

    (* Localization of a node in a sub-memory *)
    let submem_localize (a: int) (x: t) =
      Log.fatal_exn "submem_localize is called\n"

    (* Binding of an offset in a sub-memory *)
    let submem_bind (a: int) (b: int) (c: Offs.t) (x:t) =
      Log.fatal_exn "submem_bind is called\n"

    (* Unfolding *)
    let unfold (a: int) (b: nid) (c: unfold_dir) (x: t) =
      ljc_debug "unfold is called\n";
      []

    (* (\* A temporary specific for array  *\) *)
    (* let minix_check (x: t):  bool = *)
    (*   ljc_debug "minix_check is called\n"; *)
    (*   let result = is_le x !minix in *)
    (*   result *)

    let check (op: Opd0.check_operand) (x: t): bool =
      match op with
      | Opd0.SL_array ->
          IntMap.for_all
            (fun _key array ->
              A.array_check array x.t_main
            ) x.t_arrays
      | Opd0.SL_ind (a, b, c) ->
          ljc_debug "ind_check is called\n";
          false

    let assume (op: Opd0.assume_operand) (x: t): t =
      x

    (* To build a state which serves as a global state in Memory Management
     * part of Mimix 1.1. *)
    (* let minix_start (x: t): t  =  *)
    (*   let array = IntMap.find 1 x.t_arrays in *)
    (*   let array,nmain = A.minix_property array x.t_main in *)
    (*   let p0number = A.get_dimension 0 g_size array in *)
    (*   let p0flag = A.get_dimension 0 1 array in   *)
    (*   let p0parent = A.get_dimension 0 2 array in *)
    (*   let p1number = A.get_dimension 1 g_size array in *)
    (*   let p1flag = A.get_dimension 1 1 array in  *)
    (*   let p1index = A.get_dimension 1 g_index array in  *)
    (*   let nmain = Op.forget p0number nmain in *)
    (*   let cons1 = Nc_cons (Tcons1.SUPEQ,Ne_var p0number,Ne_csti 1) in *)
    (*   let cons2 = Nc_cons (Tcons1.SUPEQ,Ne_csti 24,Ne_var p0number) in *)
    (*   let cons3 = Nc_cons (Tcons1.SUPEQ,Ne_var p0flag,Ne_csti 1) in *)
    (*   let cons4 = Nc_cons (Tcons1.SUPEQ,Ne_csti 63,Ne_var p0flag) in *)
    (*   let cons5 = Nc_cons (Tcons1.SUPEQ,Ne_var p0parent,Ne_csti 0) in *)
    (*   let cons6 = Nc_cons (Tcons1.SUPEQ,Ne_csti 23,Ne_var p0parent) in *)
    (*   let cons7 = Nc_cons (Tcons1.SUPEQ,Ne_var p1number,Ne_csti 0) in *)
    (*   let cons8 = Nc_cons (Tcons1.EQ,Ne_var p1flag,Ne_csti 0) in *)
    (*   let cons9 = Nc_cons (Tcons1.EQ,Ne_csti 24, *)
    (*                        ( Ne_bin (Texpr1.Add,Ne_var p1number,Ne_var 9))) in *)
    (*   let cons_l = [ cons1; cons2; cons3; cons4; cons5; *)
    (*                  cons6; cons7; cons8; cons9 ] in *)
    (*   let nmain = *)
    (*     List.fold_left (fun acc c -> Op.guard_s true c acc) nmain cons_l in *)
    (*   let expr = Ne_bin (Texpr1.Sub,Ne_csti 24,Ne_var 9) in *)
    (*   let nmain = Op.size_assign p1index expr nmain in *)
    (*   let narrays = IntMap.add 1 array x.t_arrays in *)
    (*   let x = { x with *)
    (*             t_arrays = narrays; *)
    (*             t_main = nmain } in *)
    (*   minix := x; *)
    (*   x *)

    (* (\* To build a state which serves as a global state in an anonymous OS  *\) *)
    (* let aos_start (x: t): t = *)
    (*   let array = IntMap.find 9 x.t_arrays in *)
    (*   let array,nmain = A.spo_property array x.t_main in *)
    (*   let p0number = A.get_dimension 0 g_size array in *)
    (*   let p0next = A.get_dimension 0 3 array in *)
    (*   let p0used = A.get_dimension 0 4 array in *)
    (*   let p1number = A.get_dimension 1 g_size array in *)
    (*   let p1used = A.get_dimension 1 4 array in *)
    (*   let nmain = Op.forget p0number nmain in *)
    (*   let cons1 = Nc_cons (Tcons1.SUPEQ,Ne_var p0number,Ne_csti 6) in *)
    (*   let cons2 = Nc_cons (Tcons1.SUPEQ,Ne_csti 16,Ne_var p0number) in *)
    (*   let cons3 = Nc_cons (Tcons1.SUPEQ,Ne_var p0next,Ne_csti 0) in *)
    (*   let cons4 = Nc_cons (Tcons1.SUPEQ,Ne_csti 15,Ne_var p0next) in *)
    (*   let cons5 = Nc_cons (Tcons1.EQ,Ne_var p0used,Ne_csti 1) in *)
    (*   let cons6 = Nc_cons (Tcons1.SUPEQ,Ne_var p1number,Ne_csti 0) in *)
    (*   let cons7 = Nc_cons (Tcons1.SUPEQ,Ne_csti 16,Ne_var  p1number) in *)
    (*   let cons8 = Nc_cons (Tcons1.EQ,Ne_var p1used,Ne_csti 0) in *)
    (*   let cons_l = [ cons1; cons2; cons3; cons4; *)
    (*                  cons5; cons6; cons7; cons8 ] in *)
    (*   let nmain = *)
    (*     List.fold_left (fun acc c -> Op.guard_s true c acc) nmain cons_l in *)
    (*   let narrays = IntMap.add 9 array x.t_arrays in *)
    (*   let x = {x with t_arrays = narrays; *)
    (*            t_main = nmain} in *)
    (*   minix := x; *)
    (*   x *)
  end: DOM_VALUE)
