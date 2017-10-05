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
 ** Jiangchao Liu 2016/06/13 *)
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
open Array_node

open Svenv_sig
open Set_sig

open Set_utils

(* Apron library needed here *)
open Apron

(** Error report *)
module Log =
  Logger.Make(struct let section = "v_array___" and level = Log_level.DEBUG end)

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
module Make_VS_Array = functor (Dv: DOM_VALSET)  ->
  (struct
    let module_name = "dom_valset_array"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name Dv.module_name (Dv.config_2str ())

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


    let get_namer (x: t) =
      IntMap.fold A.get_namer x.t_arrays IntMap.empty

    (** Pretty-printing *)
    let t_2stri (namemap: sv_namer) (ind: string) (x: t) =
      let p_main =
        (Op.t_2stri
           (IntMap.fold A.get_namer x.t_arrays IntMap.empty) ind x.t_main) in
      let p_array =
        IntMap.fold (fun _ anode acc -> acc ^ (A.t_2stri "" anode))
          x.t_arrays "" in
      p_array ^ "------The main numeric element\n" ^ p_main

   (** Utils **)
   (* Check whehter a node is a summary one *)
   let is_scalar (x: t) (id: int): bool =
     try
       let tp = IntMap.find id x.t_type in
       match tp with
       | Nt_scalar -> true
       | _ -> Log.fatal_exn "invalid node in expression"
     with
     | _ -> false

    (* Remove those groups that contains 0 elements *)
    let cleanup (x: t): t =
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
      Op.is_bot x.t_main ||
      (IntMap.fold (fun key anode acc -> acc || A.is_bot x.t_main anode)
         x.t_arrays false)

    (* Top element *)
    let top: t =
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
      false

    (* Node addition and removal *)
    let sv_add ?(mark:bool = true) (id: int) (x: t): t =
      let m = Op.add_node  id false 1 (Some 1) x.t_main in
      let tp = IntMap.add id Nt_scalar x.t_type in
      { x with
        t_main = m;
        t_type = tp; }

    let sv_rem (id: int) (x: t): t =
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
        ?(mark : bool = true)
        (a: (Offs.t * int) OffMap.t)
        (b: (int * Offs.t) node_mapping)
        (opt_setv_map: setv_mapping option)
        (x: t): t =
      Log.todo_exn "symvars_srename in array domain"

    (* Synchronization of the SV environment *)
    let sve_sync_top_down (a: svenv_mod) (x: t): t =
      Log.todo_exn "sve_sync_top_down in array domain"

    (* Check the symbolic vars correspond exactly to given set *)
    let symvars_check (a:IntSet.t) (x:t): bool =
      Log.todo_exn "synvars_check"

    (* Removes all symbolic vars that are not in a given set *)
    let symvars_filter (a: IntSet.t) ?(set_vars: IntSet.t = IntSet.empty) (x: t): t =
      Log.todo_exn "symvars_filter"

    let symvars_merge (a: int) (b: int) (c: int)
        (d: (Bounds.t * onode * Offs.size) list) (e: OffSet.t) (x: t): t =
      Log.todo_exn "symvars_merge"

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

    (* Conjunction  *)
    let meet (lx: t) (rx: t): t =
      Log.todo_exn "dom_val_array meet"

    (* Forget the constraints on a dimension *)
    let sv_forget (id: int) (x: t): t =
      Log.todo_exn "forget"

    (** Comparison and join operators *)
    (* Comparision for two states with  groups of same names *)
    let flat_is_le (lx: t) (rx: t): bool =
      is_bot lx || not (is_bot rx) &&
      (let arrayle =
        IntMap.fold
          (fun key larray acc ->
            if not acc then acc
            else
              let rarray = IntMap.find key rx.t_arrays in
              A.flat_is_le larray rarray
          ) lx.t_arrays true in
      Op.get_namer (get_namer lx) lx.t_main;
      arrayle && (Op.is_le lx.t_main rx.t_main))

    let flat_upper_bnd (akind: join_kind) (lx: t) (rx: t): t =
      if is_bot lx then rx
      else if is_bot rx then lx
      else
        let narrays =
          IntMap.mapi
            (fun key larray ->
              let rarray = IntMap.find key rx.t_arrays in
              A.flat_join larray rarray
            ) lx.t_arrays in
        Op.get_namer (get_namer {lx with t_arrays = narrays}) lx.t_main;
        let nmain = Op.upper_bnd akind lx.t_main rx.t_main in
        { lx with
          t_main = nmain;
          t_arrays = narrays;
          t_cells = Bi_fun.empty_inj; }


    (* Comparison *)
    let is_le (lx: t) (rx: t) (f: int -> int -> bool) =
      let lx,rx,jud =
        IntMap.fold
          (fun key larray acc ->
            let ltx, rtx, judge = acc in
            if judge then acc
            else
              let rarray = IntMap.find key rx.t_arrays in
              let larray, lm, map, judge =
                A.inclmap larray lx.t_main rarray rx.t_main (is_scalar lx) in
              if judge then ltx, rtx, true
              else
                let nlm, nlarr, nrm, nrarr =
                  A.apply_inclmap map larray lm rarray rtx.t_main in
                let nlarrays = IntMap.add key nlarr ltx.t_arrays in
                let nrarrays = IntMap.add key nrarr rtx.t_arrays in
                let nlx = { ltx with
                            t_main   = nlm;
                            t_arrays = nlarrays } in
                let nrx = { rtx with
                            t_main   = nrm;
                            t_arrays = nrarrays } in
                nlx, nrx, false
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
            let is_widen = match akind with Jwiden -> true | _ -> false in
            let larray,lm,rarray,rm,lmap,rmap =
              A.pred_join is_widen larray ltx.t_main rarray rtx.t_main
                (is_scalar lx) in
            let rankmap =
              A.rankscore (is_scalar lx) larray lm rarray rm lmap rmap in
            let nlm,nlarr,nrm,nrarr =
              match akind with
              | Jjoin ->  A.apply_joinmap rankmap larray lm rarray rm
              | Jwiden -> A.apply_widenmap rankmap larray lm rarray rm
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
      match akind with
      | Jjoin
      | Jwiden -> flat_upper_bnd akind lx rx
      | Jdweak -> Log.fatal_exn "weak is not implemented\n"


    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (x: t) (cons: n_cons) =
      Op.sat_s x.t_main cons

    (** Condition test *)

    (* Dereference an array cell in l-value,
     * no disjunction is created since it merges groups *)
    let sv_array_materialize (id: int) (off: Offs.t) (x: t): t * int =
      let array = IntMap.find id x.t_arrays in
      let array, main, dim = A.materialize_on_lv  array off x.t_main in
      let arrays = IntMap.add id array x.t_arrays in
      { x with
        t_arrays = arrays;
        t_main   = main;
        t_lval   = Some dim}, dim

    (* The main algorithm of guard*)
    let guard (typ: bool) (cons: n_cons) (x: t): t =
      assert typ;
      match cons with
      | Nc_rand -> Log.fatal_exn "Nc_rand appears in guard function"
      | Nc_bool true -> x
      | Nc_bool false -> bot
      | Nc_cons (tb, expr1, expr2) ->
          let is_expr1_sum =
            n_expr_fold
              (fun iv acc -> acc ||(not (is_scalar x iv))) expr1 false in
          let is_expr2_sum =
            n_expr_fold
              (fun iv acc -> acc ||(not (is_scalar x iv))) expr2 false in
          match is_expr1_sum, is_expr2_sum with
          | false, false ->
              let tmain =
                (Op.guard_s typ cons x.t_main) in
              let tmain =
                Op.narrow_set_vars tmain in
              let arrays,tmain =
                IntMap.fold
                  (fun key tarray (acc_arrays,acc_m) ->
                    let acc_m, tarray = A.guard typ cons acc_m tarray in
                    (IntMap.add key tarray acc_arrays, acc_m)
                  ) x.t_arrays (x.t_arrays, tmain) in
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
              List.fold_left (flat_upper_bnd Jjoin) bot disjuncts

    (** Assignment *)
    let assign (id: int) (expr: n_expr) (x: t): t =
      cell_reset ();
      let arrays, nmain =
        IntMap.fold
          (fun key array (acc_as,acc_m) ->
            let nm, narray = A.pre_assign id acc_m array in
            (IntMap.add key narray acc_as),nm
          ) x.t_arrays (x.t_arrays, x.t_main) in
      let x = { x with t_arrays = arrays; t_main = nmain } in
      let is_dst_sum = not (is_scalar x id) in
      let is_expr_sum =
        n_expr_fold (fun iv acc -> acc
        || (not (is_scalar x iv))) expr false in
      let find_array (td: int) =
        IntMap.fold
          (fun key arr acc ->
            let acc_id,acc_b = acc in
            if acc_b then acc
            else
              if A.is_dimension_in td arr then key, true
              else 0, false
          ) x.t_arrays (0, false) in
      match is_expr_sum, is_dst_sum with
      | false, false ->
          let nmain  = Op.update_subs_elt id expr x.t_main in
          let arrays = IntMap.map (A.assign_on_sca id expr nmain ) x.t_arrays in
          { x with
            t_main = nmain;
            t_arrays = arrays;
            t_cells = Bi_fun.empty_inj}
      | false, true ->
          let dst =
            match x.t_lval with
            | Some d -> d
            | None -> Log.fatal_exn "array cell as lval but not stored" in
          let nmain = Op.update_subs_elt dst expr x.t_main in
           (* find where the array dst is in *)
          let a_id,a_b = find_array dst in
          let array = IntMap.find a_id x.t_arrays in
          let nmain,array = A.assign_on_sum dst expr nmain array in
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
                  let a_id,_ = find_array dst in
                  let array = IntMap.find a_id x.t_arrays in
                  let nmain,array = A.assign_on_sum dst expr nmain array in
                  { tx with
                    t_main   = nmain;
                    t_arrays = IntMap.add a_id array x.t_arrays;
                    t_cells  = Bi_fun.empty_inj;
                    t_lval   = None }
                else
                  let nmain = Op.update_subs_elt id expr tx.t_main in
                  let arrays =
                    IntMap.map (A.assign_on_sca id expr nmain) x.t_arrays in
                  { x with
                    t_main   = nmain;
                    t_arrays = arrays;
                    t_cells  = Bi_fun.empty_inj;
                   t_lval    = None }
              ) disjuncts in
          List.fold_left (flat_upper_bnd Jjoin) bot disjuncts

    (* Assignment inside a sub-memory *)
    let write_sub (a: sub_dest) (b: int) (c: n_rval) (x: t): t =
      Log.fatal_exn "write_sub called in array domain"

    let  unfold (cont: int) (n: nid) (udir: unfold_dir) (x: t)
        : (int IntMap.t * t) list =
      Log.fatal_exn "write_sub called in array domain"

    (** Utilities for the abstract domain *)
    let simplify_n_expr (x: t) (a: n_expr): n_expr =
      Log.todo_exn "simplify_n_expr called in array domain"


    (** Array-domain specific functions  *)
    (* Add an array address node  *)
    let sv_array_address_add (id: int) (x: t) =
      let m = Op.add_node id false 1 (Some 1) x.t_main in
      let tp = IntMap.add id Nt_array_address x.t_type in
      { x with
        t_main = m;
        t_type = tp; }

    (* Add an array content node  *)
    let sv_array_add (id:int) (size:int) (fields:int list) (x:t) =
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
    let sv_array_deref (id: int) (off: Offs.t) (x: t): (t * int) list =
      if (Bi_fun.mem_inv (id,off) x.t_cells) then
        let cell = Bi_fun.inverse_inj (id,off) x.t_cells in
        [ x, cell ]
      else
        let lv,rv = !Array_node.mater_id in
        let mv = if !mat_left then lv else rv in
        let array = IntMap.find id x.t_arrays in
        let main, array = A.sv_array_deref  mv off x.t_main array in
        let x = {x with t_arrays = IntMap.add id array x.t_arrays;
                 t_main = main;} in
        let ncell = get_cell () in
        let ncells = Bi_fun.add ncell (id,off) x.t_cells in
        [ {x with t_cells = ncells}, ncell ]

    (* The bound of a variable. *)
    let sv_bound (id: int) (x: t): interval =
      Log.fatal_exn "sv_bound in array"

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

    (* Properties check *)
    let check (op: vcheck_op) (x: t): bool =
      match op with
      | VC_array ->
          IntMap.for_all
            (fun _key array ->
              A.array_check array x.t_main
            ) x.t_arrays
      | VC_aseg  (i,off,ic,i_e,off_e,ic_e) ->
          assert (IntMap.cardinal x.t_arrays = 1);
          assert (Offs.is_zero off);
          let _,array = IntMap.min_binding x.t_arrays in
          A.check_seg i ic i_e ic_e x.t_main array
      | VC_aind  (i,off,ic) ->
          assert (IntMap.cardinal x.t_arrays = 1);
          assert (Offs.is_zero off);
          let _,array = IntMap.min_binding x.t_arrays in
          A.check_ind i ic x.t_main array
      | _ -> Log.fatal_exn "unexpected check type"

    (* Properties assumption *)
    let assume (op: vassume_op) (x: t): t =
      match op with
      | VA_aseg  (i,off,ic,i_e,off_e,ic_e) ->
          assert (IntMap.cardinal x.t_arrays = 1);
          assert (Offs.is_zero off);
          let key, array = IntMap.min_binding x.t_arrays in
          let main, array = A.assume_seg i ic i_e ic_e x.t_main array in
          { x with
            t_arrays = IntMap.add key array x.t_arrays;
            t_main = main }
      | VA_aind (i,off,ic) ->
          assert (IntMap.cardinal x.t_arrays = 1);
          assert (Offs.is_zero off);
          assert (Offs.is_zero off);
          let key, array = IntMap.min_binding x.t_arrays in
          let main, array = A.assume_ind i ic x.t_main array in
          { x with
            t_arrays = IntMap.add key array x.t_arrays;
            t_main = main }
      | _ -> Log.fatal_exn "array assume"

    (* Operations on set variables, not used in this domain *)
    let set_guard (sc: set_cons) (x: t): t = x
    let set_sat (sc: set_cons) (t: t) = true
    let setv_col_root (x:t) =  IntSet.empty
    let setv_is_root (id: int) (x:t) = false
    let setv_rem (id: int) (x: t) = x
    let setv_add ?(root: bool = false)
        ?(kind: set_par_type option = None)
        ?(name: string option = None) (id: int) (x: t)= x
    (* get all variables that equal to the current one  *)
    let get_eq_class (id: int) (x: t): IntSet.t =
      Log.todo_exn "get_eq_class in dom_valset_array"
  end: DOM_VALSET)
