(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_set.ml
 **       Functor adding a set domain over value properties
 ** Huisong Li, Xavier Rival, 2014/08/12 *)
open Data_structures
open Lib
open Offs

open Dom_sig
open Graph_sig
open Nd_sig
open Svenv_sig
open Set_sig

open Set_utils

(** Error handling *)
module Log =
  Logger.Make(struct let section = "d_set___" and level = Log_level.DEBUG end)

(* Internal sanity check flag (temporary) *)
let do_check = true

module DBuild = 
  functor ( M: DOM_VALUE ) ->
    functor ( S: DOMSET) ->
  (struct
    (** Type of abstract values *)
    (* An abstract element is a conjunction of a value abstraction and of
     * a set abstraction *)
    type t =
        { t_v:       M.t;         (* value information *)
          t_s:       S.t;         (* set information *)
          t_setvs:   IntSet.t     (* set of all valid setvs *) }

    (** Domain initialization *)
    (* Domain initialization to a set of inductive definitions *)
    let init_inductives: Keygen.t -> StringSet.t -> Keygen.t = M.init_inductives

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t =
      { t_v     = M.bot;
        t_s     = S.bot;
        t_setvs = IntSet.empty; }

    (* one of the under domains become bot will result a bot *)
    let is_bot (x: t): bool =
      (M.is_bot x.t_v) || (S.is_bot x.t_s)

    (* Top element *)
    let top: t =
      { t_v     = M.top;
        t_s     = S.top;
        t_setvs = IntSet.empty; }
    (* Pretty-printing *)
    let t_2stri (sn: string IntMap.t) (ind: string) (x: t): string =
      let s_setvs =
        IntSet.fold (fun i -> StringSet.add (Printf.sprintf "S%d" i))
          x.t_setvs StringSet.empty in
      Printf.sprintf "%ssetvs: %s\n%s%s"
        ind (StringSet.t_2str ", " s_setvs)
        (M.t_2stri sn ind x.t_v) (S.t_2stri sn ind x.t_s)

    (** Management of symbolic variables *)
    (* For sanity check *)
    let check_nodes (s: IntSet.t) (t: t): bool =
      (M.check_nodes s t.t_v) && (S.check_nodes s t.t_s)

    (** Symbolic variables **)
    (* Add symbolic variables to num or set domain, mark used to choose *
     * where to add symbolic variable *) 
    let sv_add ?(mark: bool = true) (i: int) (x: t): t =
      if mark then { x with t_v = M.add_node i x.t_v }
      else { x with t_s = snd (S.sv_add i x.t_s) }

    (* Remove symbolic variables *) 
    let sv_rem (i: int) (t: t): t =
      { t with
        t_v = M.rem_node i t.t_v;
        t_s = S.sv_rem i t.t_s; }

    (** Set variables **)
    (* Add a set variable with the given id*)
    let setv_add ?(root: bool = false)
        ?(kind: set_par_type option = None)
        ?(name: string option = None)
        (i: int) (t: t): t =
      if do_check && IntSet.mem i t.t_setvs then
        Log.fatal_exn "setv_add: setv S%d is already present" i;
      let t_s = S.setv_add ~root:root ~kind:kind ~name:name i t.t_s in
      { t with
        t_s     = t_s;
        t_setvs = IntSet.add i t.t_setvs }
    
    (* remove a set variable *)
    let setv_rem (i: int) (t: t): t =
      if not (IntSet.mem i t.t_setvs) then
        Log.warn "setv_rem: setv S%d is not present" i;
      { t with
        t_s     = S.setv_rem i t.t_s;
        t_setvs = IntSet.remove i t.t_setvs }

    (* check if a set variable is root or not *)
    let setv_is_root (i: int) (t: t): bool =
      S.setv_is_root i t.t_s
    (* collect all the root set variables in set domain *)
    let setv_col_root (t: t): IntSet.t =
      S.setv_col_root t.t_s

    (* The signatures of the functions below is likely to change with sets *)

    (* Renaming (e.g., post join), mark is used to decide rename set domain *
     * or rename both num and set domains *)
    let symvars_srename
        ?(mark: bool = true)
        (om: (Offs.t * int) OffMap.t)
        (nm: (int * Offs.t) node_mapping) 
        (opt_setv_map: setv_mapping option)
        (t: t): t =
      match opt_setv_map with
      | None ->
          let setvs = t.t_setvs in
          if mark then
            { t_v     = M.symvars_srename om nm t.t_v;
              t_s     = S.symvars_srename om nm None t.t_s;
              t_setvs = setvs }
          else
            { t with
              t_s     = S.symvars_srename om nm None t.t_s;
              t_setvs = setvs }
      | Some setv_map ->
          let setvs =
            IntSet.fold
              (fun i acc ->
                try
                  let x, y = IntMap.find i setv_map.sm_map in
                  IntSet.add x (IntSet.union y acc)
                with Not_found ->
                  if do_check then Log.warn "unmapped setv: %d" i;
                  acc
              ) t.t_setvs IntSet.empty in
          if mark then
            { t_v     = M.symvars_srename om nm t.t_v;
              t_s     = S.symvars_srename om nm (Some setv_map) t.t_s;
              t_setvs = setvs }
          else
            { t with
              t_s     = S.symvars_srename om nm (Some setv_map) t.t_s;
              t_setvs = setvs }


    (* Synchronization of the SV environment *)
    let sve_sync_top_down (svm: svenv_mod) (t: t): t =
      { t with
        t_v = M.sve_sync_top_down svm t.t_v;
        t_s = S.sve_sync_top_down svm t.t_s; }

    (* Check the symbolic vars correspond exactly to given set *)
    let symvars_check (s: IntSet.t) (x: t): bool =
      M.symvars_check s x.t_v && true

    (* Removes all symbolic vars and set variables 
     * that are not in a given set *)
    let symvars_filter (s: IntSet.t) ?(set_vars: IntSet.t = IntSet.empty)
        (t: t): t =
      { t_v     = M.symvars_filter s t.t_v;
        t_s     = S.symvars_filter s set_vars t.t_s;
        t_setvs = IntSet.inter set_vars t.t_setvs }

    (* Merging into a new variable, arguments:
     *  . the stride of the structure being treated
     *  . node serving as a base address of a block;
     *  . node serving as a new block abstraction (as a sequence of bits)
     *  . old contents of the block, that is getting merged
     *  . offsets of external pointers into the block to build an
     *    environment *)
    let symvars_merge (stride: int) (base: int) (sv: int)
        (block_desc: (Bounds.t * onode * Offs.size) list)
        (extptrs: OffSet.t) (x: t): t =
      { x with t_v = M.symvars_merge stride base sv block_desc extptrs x.t_v }

    (** Comparison and join operators *)

    (* Comparison *)
    let is_le (x0: t) (x1: t) (sat_diseq: int -> int -> bool): bool =
      (M.is_le x0.t_v x1.t_v sat_diseq) && (S.is_le x0.t_s x1.t_s)

    (* Upper bound: serves as join and widening *)
    let upper_bnd (jk: join_kind) (t0: t) (t1: t): t =
      if do_check && not (IntSet.equal t0.t_setvs t1.t_setvs) then
        Log.fatal_exn "upper_bnd: distinct sets of setvs";
      let s = 
        match jk with
        | Jjoin -> S.upper_bnd t0.t_s t1.t_s
        | Jwiden -> S.weak_bnd t0.t_s t1.t_s
        | _ -> Log.fatal_exn "join kind not implemented" in
      { t_v     = M.upper_bnd jk t0.t_v t1.t_v;
        t_s     = s;
        t_setvs = t0.t_setvs}

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (x: t) (c: n_cons): bool =
      (* maybe some reduction will be eventually needed *)
      M.sat x.t_v c

    (** Set satisfiability *)
    let set_sat (sc: set_cons) (t: t): bool =
      if do_check then
        begin
          let setvs = set_cons_setvs sc in
          if not (IntSet.subset setvs t.t_setvs) then
            Log.fatal_exn "set_sat: unbound setvs %s | %s"
              (intset_2str setvs) (intset_2str t.t_setvs);
        end;
      S.set_sat sc t.t_s

    (** Condition test *)
    let guard (b: bool) (c: n_cons) (t: t): t =
      (* maybe some reduction will be eventually needed *)
      { t with t_v = M.guard b c t.t_v }

    (** Set condition test *)
    let set_guard (sc: set_cons) (t: t): t =
      if do_check then
        begin
          let setvs = set_cons_setvs sc in
          if not (IntSet.subset setvs t.t_setvs) then
            Log.fatal_exn "set_guard: unbound setvs %s | %s"
              (intset_2str setvs) (intset_2str t.t_setvs);
        end;
      { t with t_s = S.set_guard sc t.t_s; }

    (** Assignment *)
    let assign (i: int) (e: n_expr) (t: t): t =
      (* remove any information known about i *)
      { t with
        t_v = M.assign i e t.t_v;
        t_s = S.sv_rem i t.t_s }

    (* Assignment inside a sub-memory *)
    let write_sub (sd: sub_dest) (size: int) (rv: n_rval) (t: t): t =
      { t with
        t_v = M.write_sub sd size rv t.t_v ;
        t_s = Log.todo_exn "write_sub" }

    (** Utilities for the abstract domain *)
    let simplify_n_expr (t: t) (e: n_expr): n_expr =
      M.simplify_n_expr t.t_v e
    
    (** Array domain specific functions *)
    (* Add an array content node *)
    let sv_array_add (i:int) (size: int) (fields: int list) (t:t): t =
      { t with
        t_v = M.add_array_node i size fields t.t_v;
        t_s = Log.todo_exn "sv_array_add" }
    (* Add an array address node *)
    let sv_array_address_add (id: int) (t: t): t =
      { t with
        t_v = M.add_array_address id t.t_v;
        t_s = Log.todo_exn "sv_array_add" }
    (* Checks wheter this node is the address of an array node *)
    let is_array_address (id: int) (t: t): bool =
      M.is_array_address id t.t_v
    (* Dereference an array cell in experision,
     * this function may cause disjunction *)
    let sv_array_deref (id: int) (off: Offs.t) (t: t): (t * int) list =
      let vlist = M.array_node_deref id off t.t_v in
      List.map
        (fun (v,i) ->
          { t_v = v;
            t_s = Log.todo_exn "sv_array_deref";
            t_setvs = Log.todo_exn "sv_array_deref"; }, i
        ) vlist
    (* Dereference an array cell in l-value,
     * no disjunction is created since it merges groups *)
    let sv_array_materialize (id: int) (off: Offs.t) (t: t): t * int =
      let v,i = M.array_materialize id off t.t_v in
      { t with
        t_v = v;
        t_s = Log.todo_exn "sv_array_materialize" }, i

    (** Sub-memory specific functions *)
    (* Checks whether a node is of sub-memory type *)
    let is_submem_address (i: int) (x: t): bool =
      M.is_submem_address i x.t_v
    let is_submem_content (i: int) (x: t): bool =
      M.is_submem_content i x.t_v

    (* Read of a value inside a submemory block *)
    let submem_read (sat: n_cons -> bool) (addr: int) (off: Offs.t) (sz: int)
        (x: t): onode =
      M.submem_read sat addr off sz x.t_v
    let submem_deref (sat: n_cons -> bool) (addr: int) (off: Offs.t) (sz: int)
        (x: t): onode =
      M.submem_deref sat addr off sz x.t_v

    (* Localization of a node in a sub-memory *)
    let submem_localize (ig: int) (x: t): sub_localize =
      M.submem_localize ig x.t_v

    (* Binding of an offset in a sub-memory *)
    let submem_bind (isub: int) (iglo: int) (off: Offs.t) (x: t): t * onode =
      let v, o = M.submem_bind isub iglo off x.t_v in
      { x with t_v = v }, o

    (* Unfolding *)
    let unfold (cont: int) (n: nid) (udir: unfold_dir) (x: t)
        : (int IntMap.t * t) list =
      let l = M.unfold cont n udir x.t_v in
      List.map (fun (m, v) -> m, { x with t_v = v }) l

    (* Check predicates on array *)
    let check (op: Opd0.check_operand) (x: t): bool =
      M.check op x.t_v

    (* Assumptions on array *)
    let assume (op: Opd0.assume_operand) (x: t): t =
      { x with t_v = M.assume op x.t_v }
  end: DOM_VALSET)
