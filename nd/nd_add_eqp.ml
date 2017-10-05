(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_add_dyn_svenv.ml
 **       Set of symbolic variables is dealt dynamically:
 **       Variable are added in the underlying numerical domain
 **       only when it is required
 ** Antoine Toubhans, 2013/09/30 *)
open Data_structures
open Lib
open Nd_sig
open Nd_utils
open Apron

module Log =
  Logger.Make(struct let section = "nd_+eqp" and level = Log_level.DEBUG end)




(** Functor *)
module Add_eq_partition = functor (D: DOM_NUM_NB) ->
  (struct
    let module_name = "nd_add_eqp"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name D.module_name (D.config_2str ())
    type t =
        { t_u: D.t;     (* underlying numerical *)
          t_e: int Union_find.t;
          t_const: (int, int) Bi_fun.t; }

    (* Bottom element *)
    let is_bot (x: t): bool = D.is_bot x.t_u

    (* Top element *)
    let top: t =
      { t_u = D.top;
        t_e = Union_find.empty;
        t_const = Bi_fun.empty; }

    (* Pretty-printing *)
    let t_2stri (sn: sv_namer) (ind: string) (x: t): string =
      let seqs = Union_find.t_2stri "" (Pervasives.string_of_int) x.t_e in
      Printf.sprintf "%s%s" seqs (D.t_2stri sn ind x.t_u)

    (* Variables management *)
    let add_node (i: int) (x: t): t =
      { x with t_u = D.add_node i x.t_u }

    let putback (i: int) (x: t) =
      if Union_find.mem i x.t_e then
        let orep = fst (Union_find.find i x.t_e) in
        let ano, te = Union_find.rem i x.t_e in
        let x = { x with t_e = te } in
        match ano with
        | None -> x
        | Some a ->
            let nrep, _ = Union_find.find a te in
            let tu =
              if orep = nrep then D.add_node i x.t_u
              else D.add_node nrep x.t_u in
            let cons = Nc_cons (Tcons1.EQ, Ne_var nrep, Ne_var i) in
            { x with t_u = D.guard true cons tu }
      else x

    let rem_node (i: int) (x: t): t =
      let x = putback i x in
      { x with
        t_u = D.rem_node i x.t_u;
        t_const = Bi_fun.rem_dir i x.t_const }

    let vars_srename (nr: 'a node_mapping) (x: t): t =
      let af_rem = IntSet.fold rem_node nr.nm_rem x in
      IntMap.fold
        (fun key (el,set) acc ->
          let nnr =
            { nr with
              nm_map = IntMap.add key (el, IntSet.empty) IntMap.empty;
              nm_rem = IntSet.empty } in
          let acc =
            if Union_find.mem key acc.t_e then
              let te = Union_find.var_rename key el acc.t_e in
              if Union_find.is_representative key acc.t_e then
                let te = Union_find.var_rename key el acc.t_e in
                { acc with t_e = te; t_u = D.vars_srename nnr acc.t_u }
              else
                { acc with t_e = te }
            else
              let te = Union_find.add el acc.t_e in
              { acc with t_e = te; t_u = D.vars_srename nnr acc.t_u } in
          let te =
            IntSet.fold (fun k iac -> Union_find.add k ~rep:el iac)
              set acc.t_e in
          { acc with t_e = te }
        ) nr.nm_map af_rem

    let check_nodes (s: IntSet.t) (x: t): bool =
      D.check_nodes
        (IntSet.filter (fun key -> not (Union_find.mem key x.t_e)) s) x.t_u

    let nodes_filter (nkeep: IntSet.t) (x: t): t =
      Log.todo_exn "nodes filter"

    let unify (lx: t) (rx: t): t * t =
      let nr = { nm_map = IntMap.empty;
                 nm_rem = IntSet.empty;
                 nm_suboff = fun _ -> false } in
      let lc =
        Bi_fun.fold_dom
          (fun key value acc ->
            if Bi_fun.mem_dir key rx.t_const then
              if Bi_fun.image key rx.t_const = value then
                acc
              else
                Bi_fun.rem_dir key acc
            else
              Bi_fun.rem_dir key acc
          ) lx.t_const lx.t_const in
      let le = Union_find.meet lx.t_e rx.t_e in
      let godown (x: t) =
        let x =
          Union_find.fold
            (fun key acc ->
              if Union_find.mem key le then acc
              else putback key acc
            ) x.t_e x in
        let x =
          Union_find.fold
            (fun key acc ->
              if Union_find.is_representative key le then
                let rep = fst (Union_find.find key x.t_e) in
                if key != rep then
                  if Union_find.is_same_class key rep le then
                    let map = IntMap.add rep (key,IntSet.empty) IntMap.empty in
                    let tnr = { nr with nm_map = map } in
                    { acc with t_u = D.vars_srename tnr acc.t_u }
                  else putback key acc
                else acc
              else acc
            ) le x in
        { x with t_e = le } in
      let lx = godown lx in
      let rx = godown rx in
      { lx with t_const = lc }, { rx with t_const = lc }

    (** Comparison and Join operators *)
    let is_le (x0: t) (x1: t) (sat_diseq: int -> int -> bool): bool =
      let x0, x1 = unify x0 x1 in
      D.is_le x0.t_u x1.t_u sat_diseq

    let join (x0: t) (x1: t): t =
      let x0, x1 = unify x0 x1 in
      { x0 with t_u = D.join x0.t_u x1.t_u }

    let widen (x0: t) (x1: t): t =
      let x0, x1 = unify x0 x1 in
      { x0 with t_u = D.widen x0.t_u x1.t_u }

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let var_map (x: t) (key: int) =
      if Union_find.mem key x.t_e then
        fst (Union_find.find key x.t_e)
      else key

    let sat (c: n_cons) (x: t): bool =
      let c = n_cons_map (var_map x) c in
      match c with
      | Nc_cons (Tcons1.DISEQ, Ne_var v0, Ne_var v1) ->
          not (Union_find.is_same_class  v0  v1 x.t_e) && D.sat c x.t_u
      | _ -> (* send to underlying domain *)
          D.sat c x.t_u

    let add_eq (l: int) (r: int) (x: t): t =
      let lift (i: int) (tx: t) =
        if Union_find.mem i tx.t_e then tx
        else { tx with t_e = Union_find.add i tx.t_e } in
      let x = lift r (lift l x) in
      let lrep = fst (Union_find.find l x.t_e) in
      let rrep = fst (Union_find.find r x.t_e) in
      if lrep = rrep then x
      else { x with
             t_u = D.rem_node rrep x.t_u;
             t_e = Union_find.union lrep rrep x.t_e }

    (** Transfer functions *)
    let assign (dst: int) (expr: n_expr) (x: t): t =
      let x = putback dst x in
      let x = { x with
                t_const = Bi_fun.rem_dir dst x.t_const;
                t_u = D.assign dst (n_expr_map (var_map x) expr) x.t_u } in
      match expr with
      | Ne_var i ->
          add_eq dst i x
      | Ne_csti c ->
          let x =
            if Bi_fun.mem_inv c x.t_const then
              let set = Bi_fun.inverse c x.t_const in
              let elt = Aa_sets.min_elt set in
              add_eq dst elt x
            else x in
          { x with t_const = Bi_fun.add dst c x.t_const }
      |  _ -> x

    let guard (b: bool) (cons: n_cons) (x: t): t =
      (* simplification on offset expressions *)
      assert b;
      match cons with
      | Nc_cons (Tcons1.EQ, Ne_var v0, Ne_var v1) ->
          add_eq v0 v1 x
      | Nc_cons (Tcons1.EQ, Ne_var v0, Ne_csti c0)
      | Nc_cons (Tcons1.EQ, Ne_csti c0, Ne_var v0) ->
          let x = { x with t_const = Bi_fun.add v0 c0 x.t_const } in
          if Bi_fun.mem_inv c0 x.t_const then
            let set = Bi_fun.inverse c0 x.t_const in
            let elt = Aa_sets.min_elt set in
            add_eq elt v0 x
          else
            { x with t_u = D.guard b (n_cons_map (var_map x) cons) x.t_u }
      | _ ->
          { x with t_u = D.guard b (n_cons_map (var_map x) cons) x.t_u }

    (** Utilities for the abstract domain *)
    let simplify_n_expr (x: t) (e: n_expr): n_expr =
      Log.todo_exn "simpeliy n expr"

    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another *)
    let expand (id: int) (nid: int) (x: t): t =
      let x =
        if Bi_fun.mem_dir id x.t_const then
          { x with
            t_const = Bi_fun.add nid (Bi_fun.image id x.t_const) x.t_const }
        else x in
      if Union_find.mem id x.t_e then
        let rep = fst (Union_find.find id x.t_e) in
        { x with t_e = Union_find.add nid ~rep:rep x.t_e }
      else
        { x with t_u = D.expand id nid x.t_u }

    (* Upper bound of the constraits of two dimensions *)
    let compact (lid: int) (rid: int) (x: t): t =
      match Union_find.mem lid x.t_e, Union_find.mem rid x.t_e with
      |  true, true -> { x with t_e = snd (Union_find.rem rid x.t_e) }
      | _, _ ->
          let x = putback lid (putback rid x) in
          { x with
            t_u     = D.compact lid rid x.t_u;
            t_const = Bi_fun.rem_dir lid (Bi_fun.rem_dir rid x.t_const) }

    (* Conjunction *)
    let meet (lx: t) (rx: t): t =
      let lx, rx = unify lx rx in
      { lx with t_u = D.meet lx.t_u rx.t_u }

    (* Forget the information on a dimension *)
    let sv_forget (id: int) (x: t): t =
      let x = putback id x in
      { x with
        t_u = D.sv_forget id x.t_u;
       t_const = Bi_fun.rem_dir id x.t_const }

    (** Export of range information *)
    (* the bound of a variable *)
    let bound_variable (dim: int) (x: t): interval =
      D.bound_variable (var_map x dim) x.t_u

    (** Extract the set of all SVs *)
    let get_svs (x: t): IntSet.t =
      let set =
        Union_find.fold
          (fun key acc ->
            IntSet.add key acc
          ) x.t_e IntSet.empty in
      IntSet.union set (D.get_svs x.t_u)

    (* get all variables that equal to the current one  *)
    let get_eq_class (i: int) (x: t): IntSet.t =
      let set =
        if Union_find.mem i x.t_e then
          let rep = fst (Union_find.find i x.t_e) in
          IntSet.of_list (Union_find.find_class rep x.t_e)
        else IntSet.empty in
      IntSet.union set (D.get_eq_class (var_map x i) x.t_u)
  end: DOM_NUM_NB)
