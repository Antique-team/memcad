(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_subm_graph.ml
 **       implementation of submemory based on graphs
 ** Xavier Rival, 2016/07/16 *)
open Data_structures
open Flags
open Lib
open Offs

open Dom_subm_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig
open Svenv_sig

open Dom_utils
open Graph_utils

open Apron

(** Error report *)
module Log =
  Logger.Make(struct let section = "d_submg_" and level = Log_level.DEBUG end)

(* whether or not to print full debug information *)
let full_debug = true


(** Submemory layer *)
(* A sub-memory encloses
 *  - a graph
 *  - a local name space;
 *  - a local environment *)
module Submem =
  (struct
    (* A sub-memory encloses:
     *  - a graph to describe the sub-memory contents
     *  - a bi-directional index binding global keys and local ones
     *  - an environment mapping offsets in the sub-memory space into
     *    nodes representing their addresses in the sub-memory
     *  - a map of offsets known to be in the submem, with the length of
     *    blocks known to start from them
     *  - information about the placement in the memory:
     *    SVs standing for address and value, begin offset, end offset:
     *    t_addr+[t_min,t_max[ => t_val
     *  - refcount information, on dependencies on global SVs
     *)
    type t =
        { (* graph *)
          t_graph:  graph; (* sub-memory graph *)
          (* indexes *)
          t_index:  (int, int) Bi_fun.t; (* bi-directional index *)
          t_env:    (Offs.t, int) Bi_fun.t; (* environment *)
          t_off_ds: int OffMap.t; (* deltas between env offsets and stride *)
          (* placement information *)
          t_stride: int; (* value on which offsets are aligned *)
          t_addr:   int; (* main mem SV for base address       *)
          t_val:    int; (* main mem SV for content            *)
          t_min:    Bounds.t; (* min offset (included) *)
          t_max:    Bounds.t; (* max offset (not included) *)
          (* refcount information *)
          t_rc:     int Refcount.t; (* global SVs refcount *) }

    (** Dom ID *)
    let dom_id: mod_id ref = ref (-1, "subm")

    (** Utilities *)
    (* index conversions *)
    let glo_to_loc (x: t) (iglo: int): int = Bi_fun.image iglo x.t_index
    let loc_to_glo (x: t) (iloc: int): int = Bi_fun.inverse_inj iloc x.t_index
    (* index conversion across a constraint *)
    let up_n_cons (x: t) (c: n_cons): n_cons =
      Nd_utils.n_cons_map (loc_to_glo x) c
    (* map lift to global indexes *)
    let up_renaming (x: t) (r: int IntMap.t): int IntMap.t =
      let f = loc_to_glo x in
      IntMap.fold (fun i j acc -> IntMap.add (f i) (f j) acc) r IntMap.empty

    (** Temporary utilities: specific to current abstraction of sub-memories *)
    (* Exporting of keys of local graph *)
    let get_keys (x: t): IntSet.t =
      Aa_sets.fold IntSet.add (Bi_fun.whole_image x.t_index) IntSet.empty

    (** Sanity checks *)
    (* Sanity property:
     *  - t_index should be well-formed
     *  - nodes in the sub graph should correspond to indexes
     *)
    let sanity_check (ctx: string) (x: t): unit =
      let _, svem = Graph_utils.sve_sync_bot_up x.t_graph in
      if not (Dom_utils.svenv_is_empty svem) then
        Log.fatal_exn
          "sanity_check<%s> fails (submem): non empty svenv mod" ctx;
      Bi_fun.sanity_check ctx x.t_index;
      let indexes = get_keys x in
      let snodes = Graph_utils.get_all_nodes x.t_graph in
      if not (IntSet.equal indexes snodes) then
        begin
          Log.error "indexes: %s\nsnodes: %s" (intset_2str indexes)
            (intset_2str snodes);
          Log.fatal_exn
            "sanity_check<%s> fails (submem): indexes and snodes matching" ctx;
        end

    (** Valid inductive definitions *)
    let valid_inductives: StringSet.t ref = ref StringSet.empty
    let init_inductives (g: Keygen.t) (s: StringSet.t): Keygen.t =
      let g, k = Keygen.gen_key g in (* this domain generates keys *)
      let inds =
        if !submem_inds = StringSet.empty then s else !submem_inds in
      valid_inductives := inds;
      if sv_upg then dom_id := k, snd !dom_id;
      g

    (** Construction of an (empty) abstract value *)
    (* A general value for reconstruction of elements *)
    let recompute_refcount (x: t): t =
      let f b =
        IntSet.fold Refcount.incr (Bounds.t_sym_var_ids_add IntSet.empty b) in
      let rc = Refcount.incr x.t_addr (Refcount.incr x.t_val Refcount.empty) in
      let rc = f x.t_min (f x.t_max rc) in
      { x with t_rc = rc }
    (* Creation of an empty sub-memory (cells are not there yet
     *  args give address SV, content SV, stride, low and high bounds *)
    let empty (loc: int) (cont: int)
        (stride: int) (blo: Bounds.t) (bhi: Bounds.t): t =
      recompute_refcount { t_graph  = graph_empty !valid_inductives;
                           t_index  = Bi_fun.empty_inj;
                           t_env    = Bi_fun.empty;
                           t_off_ds = OffMap.empty;
                           t_stride = stride;
                           t_addr   = loc;
                           t_val    = cont;
                           t_min    = blo;
                           t_max    = bhi;
                           t_rc     = Refcount.empty }
    (* Computation of a lower bound on the size of a block in sub-memory *)
    let env_get_block_size_option (i: int) (x: t): int option =
      try
        match (node_find i x.t_graph).n_e with
        | Hemp | Hind _ | Hseg _ -> None
        | Hpt pte ->
            Some (Block_frag.fold_base
                    (fun _ pe m ->
                      match Offs.size_to_int_opt pe.pe_size with
                      | Some i -> i + m
                      | _ -> m
                    ) pte 0)
      with Not_found -> None
    let strengthen_off_delta (oknown: Offs.t) (onew: Offs.t) (i: int) (x: t)
        (off_ds: int OffMap.t): int OffMap.t =
      try OffMap.add onew (OffMap.find oknown x.t_off_ds) off_ds
      with Not_found ->
        Log.info "offset was not found!";
        match env_get_block_size_option i x with
        | None -> off_ds
        | Some d -> OffMap.add onew d off_ds
    (* Post-build: reduces / recomputes the delta-offsets *)
    let post_build (x: t): t =
      let off_ds =
        Bi_fun.fold_dom
          (fun o i acc ->
            match env_get_block_size_option i x with
            | None -> acc
            | Some d -> OffMap.add o d acc
          ) x.t_env x.t_off_ds in
      { x with t_off_ds = off_ds }

    (** Filling fields *)
    let update_max (b: Bounds.t) (stride: int) (x: t): t =
      Log.info "updating the max to: %s" (Bounds.t_2str b);
      { x with t_max = (Bounds.add_int b stride) }
    let get_addr (x: t): int      = x.t_addr
    let get_cont (x: t): int      = x.t_val
    let get_omin (x: t): Bounds.t = x.t_min
    let get_omax (x: t): Bounds.t = x.t_max
    let get_env (x: t): (Offs.t, int) Bi_fun.t = x.t_env
    let get_off_ds (x: t): int OffMap.t = x.t_off_ds

    (** Check if it may be impacted by a glo SV numeric write/removal *)
    let may_impact_sv_mod (i: int) (x: t): bool =
      Refcount.hasref i x.t_rc

    (** Temporary utilities: specific to current abstraction of sub-memories *)
    (* Discarding of the add and rem fields of the local graph *)
    let discard_addrem (x: t): t =
      let g, _ = Graph_utils.sve_sync_bot_up x.t_graph in
      { x with t_graph = g }
    (* Synchronization of add_rem fields:
     *  - exports locally removed nodes (g)
     *  - exports locally added nodes (l) *)
    let sync_addrem (x: t): t * IntSet.t * IntSet.t =
      let g, svm = Graph_utils.sve_sync_bot_up x.t_graph in
      let add = PMap.fold (fun i _ -> IntSet.add i) svm.svm_add IntSet.empty in
      (* local sanity check, regarding to the local indexes *)
      PSet.iter
        (fun i -> assert (not (Bi_fun.mem_dir i x.t_index))) svm.svm_rem;
      (* fixing the env index *)
      let env =
        Bi_fun.fold_dom
          (fun off i acc ->
            if PSet.mem i svm.svm_rem then Bi_fun.rem_dir off acc
            else acc
          ) x.t_env x.t_env in
      (* (g) removed nodes *)
      let rem, index =
        PSet.fold
          (fun iloc (accr, accb) ->
            let iglo = loc_to_glo x iloc in
            IntSet.add iglo accr, Bi_fun.rem_dir iglo accb
          ) svm.svm_rem (IntSet.empty, x.t_index) in
      { t_graph  = g;
        t_index  = index;
        t_env    = env;
        t_off_ds = x.t_off_ds;
        t_stride = x.t_stride;
        t_addr   = x.t_addr;
        t_val    = x.t_val;
        t_min    = x.t_min;
        t_max    = x.t_max;
        t_rc     = x.t_rc }, add, rem

    (** Pretty-printing *)
    let t_2stri (ind: string) (x: t): string =
      let nind = "  "^ind in
      let s_env =
        let f_off o =
          let s = Offs.t_2str o in
          try Printf.sprintf "%s (++%d)" s (OffMap.find o x.t_off_ds)
          with Not_found -> Printf.sprintf "%s (++?)" s in
        if Bi_fun.is_empty x.t_env then ""
        else Bi_fun.t_2str nind f_off string_of_int x.t_env in
      let fi = Printf.sprintf "%d" in
      Printf.sprintf "%s%d [%s - %s[ => %d <(%d)>\n%s{{\n%s%s%s%s%s}}\n" ind
        x.t_addr (Bounds.t_2str x.t_min) (Bounds.t_2str x.t_max) x.t_val
        x.t_stride ind (Refcount.t_2stri string_of_int nind x.t_rc)
        (if full_debug then Bi_fun.t_2str nind fi fi x.t_index else "")
        s_env (graph_2stri nind x.t_graph) ind

    (** Environment *)
    (* Computation of a lower bound on the size of a block in sub-memory *)
    let env_get_block_size_lower_bound (i: int) (x: t): int =
      match env_get_block_size_option i x with None -> 0 | Some n -> n
    (* Check if an offset is in the env, add it, find it*)
    let env_mem (o: Offs.t) (x: t): bool = Bi_fun.mem_dir o x.t_env
    let env_add (o: Offs.t) (i: int) (x: t): t =
      Log.info "adding-to-env: %s < %s [%b]" (Offs.t_2str o)
        (Bounds.t_2str x.t_max) (Offs.is_on_stride x.t_stride o);
      let rc =
        if env_mem o x then x.t_rc
        else
          IntSet.fold Refcount.incr (Offs.t_sym_var_ids_add IntSet.empty o)
            x.t_rc in
      let off_ds =
        match env_get_block_size_option i x with
        | None -> x.t_off_ds
        | Some n -> OffMap.add o n x.t_off_ds in
      { x with
        t_env    = Bi_fun.add o i x.t_env;
        t_rc     = rc;
        t_off_ds = off_ds }
    let env_find (o: Offs.t) (x: t): int =
      try Bi_fun.image o x.t_env
      with
      | Not_found ->
          Log.info "Not found in env_find: %s\n%s" (Offs.t_2str o)
            (t_2stri "  " x);
          Log.fatal_exn "not_found in env_find"
    (* looks for a decomposition of an offset as off(in env)+k where
     * k is smaller than the stride (i.e., search of a block field) *)
    let env_localize (osimplifier: Offs.t -> Offs.t) (o: Offs.t) (x: t)
        : (int * Offs.t) option =
      Bi_fun.fold_dom
        (fun off i acc ->
          match acc with
          | Some _ -> acc
          | None ->
              let delta = osimplifier (Offs.sub_t o off) in
              match Offs.to_int_opt delta with
              | None -> None
              | Some idelta ->
                  if idelta >= 0 then Some (i, delta)
                  else None
        ) x.t_env None

    (** Temporary creation implementation *)
    let sv_add_gen (a: nalloc) (gl_i: int) (x: t): nid * t =
      let i, g = sv_add_fresh Ntaddr a x.t_graph in
      let svm = { g.g_svemod with
                  svm_add = PMap.remove i g.g_svemod.svm_add } in
      let g = { g with g_svemod = svm } in
      i, { x with
           t_graph = g;
           t_index = Bi_fun.add gl_i i x.t_index }
    let sv_add_address:  int -> t -> nid * t = sv_add_gen (Nheap (Some 0))
    let sv_add_contents: int -> t -> nid * t = sv_add_gen Nnone
    let add_cell (addr: nid) (bnd: Bounds.t) (size: Offs.size)
        (cont: nid) (x: t): t =
      if !flag_debug_submem then
        Log.force "add cell:\n%s" (graph_2stri "   " x.t_graph);
      let pe = { pe_size = size;
                 pe_dest = cont, Offs.zero } in
      { x with
        t_graph = pt_edge_block_append (addr, bnd) pe x.t_graph }
    let register_node (iloc: int) (iglo: int) (x: t): t =
      { x with t_index = Bi_fun.add iglo iloc x.t_index }
    let node_assume_placed (iloc: int) (x: t): t =
      { x with t_graph = node_assume_placed iloc x.t_graph }
        
    (** Constraints satisfaction *)
    let make_sat (main_sat: n_cons -> bool) (x: t) (nc: n_cons): bool =
      if !flag_debug_submem then
        Log.force "submem_sat: %s" (Nd_utils.n_cons_2str nc);
      let aux (): bool =
        main_sat (up_n_cons x nc) in
      (* First, attempts to solve on the graph *)
      let b_graph =
        match nc with
        | Nc_cons (Tcons1.DISEQ, Ne_csti 0, Ne_var i)
        | Nc_cons (Tcons1.DISEQ, Ne_var i, Ne_csti 0) ->
            pt_edge_mem (i, Offs.zero) x.t_graph
        | _ -> false in
      (* Second, attempts to verify on the numeric value *)
      b_graph || aux ()

    (** Reading functions *)
    let underlying_sat (c: n_cons): bool =
      Log.warn "calling unimplemented underlying sat function";
      false
    let read_sub_base_off
        (osimplifier: Offs.t -> Offs.t)
        (o: Offs.t) (sz: int) (x: t): onode =
      (* - localize in the environment an offset such that the delta is
       *   a positive integer
       * - walk from that point to search
       * - dereference edge in the graph
       *)
      Log.info "call   read_sub_base_off %s" (Offs.t_2str o);
      let o = osimplifier o in
      match env_localize osimplifier o x with
      | None -> Log.todo_exn "offset not found in environment"
      | Some on ->
          Log.info "\tFound sub-cell: %s" (onode_2str on);
          let g, pe = pt_edge_extract underlying_sat on sz x.t_graph in
          (* for now, we do not account for graph update *)
          assert (g == x.t_graph);
          loc_to_glo x (fst pe.pe_dest), snd pe.pe_dest
    let read_sub_internal
        (isrc: nid) (o: Offs.t) (sz: int) (x: t): onode =
      let g, pe = pt_edge_extract underlying_sat (isrc, o) sz x.t_graph in
      (* for now, we do not account for graph update *)
      assert (g == x.t_graph);
      loc_to_glo x (fst pe.pe_dest), snd pe.pe_dest

    (** Localization of a node as an address *)
    (* Finds an offset mapping to a node *)
    let localize_offset_of_node (i: int) (x: t): Offs.t option =
      let s = Bi_fun.inverse i x.t_env in
      if Aa_sets.is_empty s then None
      else Some (Aa_sets.min_elt s)
    (* Decides whether a node is *definetely* allocated in the sub-memory *)
    let localize_node_in_block (i: int) (x: t): bool =
      match (node_find (glo_to_loc x i) x.t_graph).n_e with
      | Hemp -> false
      | Hpt _ | Hind _ | Hseg _ -> true

    (** Delegated unfolding *)
    let unfold
        (main_sat: n_cons -> bool)
        (n: nid) (udir: unfold_dir) (x: t)
        : (t
             * int IntMap.t (* renaming *)
             * n_cons list) list =
      let l = Graph_materialize.unfold ~submem:true n udir x.t_graph in
      List.map
        (fun ur ->
          (* unfolded sub-memory *)
          let x = { x with
                    t_graph = ur.ur_g; } in
          (* reduction of equalities inferred in the unfolding *)
          let x, renaming =
            if ur.ur_eqs = PairSet.empty then x, IntMap.empty
            else
              let ng, renaming =
                let sat = make_sat main_sat x in
                graph_merge_eq_nodes sat ur.ur_eqs x.t_graph in
              let nenv =
                Bi_fun.fold_dom
                  (fun off i acc ->
                    let j = try IntMap.find i renaming with Not_found -> i in
                    Bi_fun.add off j acc
                  ) x.t_env Bi_fun.empty in
              { x with
                t_graph = ng;
                t_env   = nenv }, up_renaming x renaming in
          (* experimental (trying to solve equality propagation issue) *)
          (* - check whether a capture occurs in the env *)
          let add_cons =
            (* propagate equalities on nodes that should be merged
             * (it often indirectly causes _|_ reduction later on) *)
            Bi_fun.fold_inverse
              (fun i s acc ->
                let rec aux acc l =
                  match l with
                  | [ ] | [ _ ] -> acc
                  | o0 :: o1 :: l2 ->
                      let e0 = Offs.to_n_expr o0 and e1 = Offs.to_n_expr o1 in
                      aux (Nc_cons (Tcons1.EQ, e0, e1) :: acc) (o1 :: l2) in
                aux acc (Aa_sets.fold (fun a b -> a :: b) s [ ])
              ) x.t_env [ ] in
          (* Equality constraints *)
          let constraints =
            PairSet.fold
              (fun (i, j) acc ->
                Nc_cons (Tcons1.EQ, Ne_var i, Ne_var j) :: acc
              ) ur.ur_eqs ur.ur_cons in
          (* All constraints *)
          let cons = add_cons @ List.map (up_n_cons x) constraints in
          if false then
            begin
              Log.info "UPconstraints: %d" (List.length cons);
              List.iter
                (fun c -> Log.info "- %s" (Nd_utils.n_cons_2str c)) cons
            end;
          x, renaming, cons
        ) l

    (** Renaming using a node mapping *)
    let symvars_srename (om: (Offs.t * int) OffMap.t) (nm: Offs.t node_mapping)
        (x: t): t * n_cons list =
      if !flag_debug_submem then
        Log.force "SUB.symvars_srename, BEFORE:\n%s" (t_2stri "  " x);
      let renamer: int IntMap.t list =
        IntMap.fold
          (fun old (n0, nl1) acc ->
            List.fold_left
              (fun acc map ->
                IntSet.fold (fun n acc -> IntMap.add old n map :: acc)
                  nl1 (IntMap.add old n0 map :: acc)
              ) [ ] acc
          ) nm.nm_map [ IntMap.empty ] in
      (* compute all possible ways to rename a given offset *)
      let f_off (o: Offs.t): OffSet.t =
        List.fold_left
          (fun acc r ->
            match Offs.t_rename_opt r o with
            | None -> acc
            | Some off -> OffSet.add off acc
          ) OffSet.empty renamer in
      let f_bound (b: Bounds.t): Bounds.t =
        if false then Log.info "Trying to rename: %s" (Bounds.t_2str b);
        let ol = Bounds.to_off_list b in
        let os =
          List.fold_left
            (fun acc o -> OffSet.union acc (f_off o)) OffSet.empty ol in
        let bopt =
          OffSet.fold
            (fun o acc ->
              match acc with
              | None -> Some (Bounds.of_offs o)
              | Some bacc -> Some (Bounds.merge bacc (Bounds.of_offs o))
            ) os None in
        if false then Log.info "Renamed %s into" (Bounds.t_2str b);
        match bopt with
        | None -> Log.fatal_exn "no conversion"
        | Some b -> if false then Log.info "%s" (Bounds.t_2str b); b in
      if !flag_debug_submem then
        begin
          Log.force "renamers: %d" (List.length renamer);
          List.iter
            (fun r ->
              Log.force "%s" (IntMap.t_2str ";" string_of_int r)) renamer;
        end;
      (* renaming in the environment
       * ->>> filter acceptable submem offsets *)
      let env, off_ds =
        Bi_fun.fold_dom
          (fun osub i ->
            OffSet.fold
              (fun ogr (acce, accd) ->
                let keep = nm.nm_suboff ogr in
                if !flag_debug_submem then
                  Log.force "sub-off %s [%s] kept: %b" (Offs.t_2str ogr)
                    (Offs.t_2str osub) keep;
                let e = if keep then Bi_fun.add ogr i acce else acce in
                let d = strengthen_off_delta osub ogr i x accd in
                e, d
              ) (f_off osub)
          ) x.t_env (Bi_fun.empty, OffMap.empty) in
      (* augmenting environment with additional offsets if needed after
       * a join where new offsets were synthesized (unification failure) *)
      let env, off_ds, eqs =
        Bi_fun.fold_dom
          (fun o_osub i (acc_env, acc_od, acc_eqs) ->
            try
              let n_osub, _ = OffMap.find o_osub om in
              let eo = Offs.to_n_expr o_osub and en = Offs.to_n_expr n_osub in
              let eq = Nc_cons (Tcons1.EQ, eo, en) in
              let n_od = strengthen_off_delta o_osub n_osub i x acc_od in
              Bi_fun.add n_osub i acc_env, n_od, eq :: acc_eqs
            with Not_found -> acc_env, acc_od, acc_eqs
          ) x.t_env (env, off_ds, [ ]) in
      let x = { x with
                t_env    = env;
                t_off_ds = off_ds;
                t_min    = f_bound x.t_min;
                t_max    = f_bound x.t_max; } in
      if !flag_debug_submem then
        Log.force "SUB.symvars_srename, AFTER:\n%s" (t_2stri "  " x);
      recompute_refcount x, eqs

    (** Upper bounds *)

    (* Implementation of upper bounds *)
    let upper_bnd
        (acci: int) (* negative int allocator, main mem *)
        (accrel: node_relation) (* relation accumulator, main mem *)
        (accsn: (int * int) IntMap.t) (* localization accumulator, main mem *)
        ((iaddr, icont): int * int) (* base and content SVs *)
        (nsat0: n_cons -> bool) (x0: t)
        (nsat1: n_cons -> bool) (x1: t)
        : t * node_relation * (int * int) IntMap.t * int =
      if !flag_debug_submem then
        Log.force "Submem join:\nLL:\n%s\nRR:\n%s"
          (t_2stri "     " x0) (t_2stri "    " x1);
      (* Computation of roots... *)
      let nrel, _, nenv, nds =
        Bi_fun.fold_dom
          (fun off i0 (accr, acci, acce, accd) ->
            try
              let ds =
                try
                  let d0 = OffMap.find off x0.t_off_ds
                  and d1 = OffMap.find off x1.t_off_ds in
                  if d0 = d1 then OffMap.add off d0 accd else accd
                with Not_found -> accd in
              let i1 = Bi_fun.image off x1.t_env in
              let r  = Nrel.add accr (i0, i1) acci in
              r, acci + 1, Bi_fun.add off acci acce, ds
            with
            | Not_found -> (* we discard that element from the environment *)
                if !flag_debug_submem then
                  Log.force "Dropping offset %s" (Offs.t_2str off);
                accr, acci, acce, accd
          ) x0.t_env (Nrel.empty, 0, Bi_fun.empty, OffMap.empty) in
      let g_init = init_graph_from_roots true nrel.n_pi x0.t_graph x1.t_graph in
      let sat0, sat1 = make_sat nsat0 x0, make_sat nsat1 x1 in
      (* Trigger the join in the underlying *)
      let g, rel, inst0, inst1 =
        Graph_join.join true
          (tr_join_arg sat0 (x0.t_graph, ext_graph None None)) sat0  
          (tr_join_arg sat1 (x1.t_graph, ext_graph None None)) sat1 
          None None nrel true g_init in
      (* Compute a new index and a new relation *)
      let index, accrel, accsn, acci = (* also add max int *)
        Nrel.fold
          (fun ires (il, ir) (accx, accrel, accsn, acci) ->
            if !flag_debug_submem then
              Log.force "adding %d = (%d,%d) => %d" ires il ir acci;
            let pre_l = loc_to_glo x0 il in
            let pre_r = loc_to_glo x1 ir in
            if !flag_debug_submem then
              Log.force "       %d = (%d,%d)" acci pre_l pre_r;
            ( Bi_fun.add acci ires accx,
              Nrel.add accrel (pre_l, pre_r) acci,
              IntMap.add acci (icont, ires) accsn,
              acci - 1 )
          ) rel (Bi_fun.empty_inj, accrel, accsn, acci) in
      (* Produce a result, assuming no instantiation to do *)
      let f_check ins =
        assert (ins.ins_expr = IntMap.empty
                  && ins.ins_fold = IntMap.empty) in
      f_check inst0; f_check inst1;
      let x =
        let stride =
          if x0.t_stride = x1.t_stride then x0.t_stride
          else Log.fatal_exn "joining two submem on different strides" in
        { t_graph  = g;
          t_index  = index;
          t_env    = nenv;
          t_off_ds = nds;
          t_stride = stride;
          t_addr   = iaddr;
          t_val    = icont;
          t_min    = Bounds.inter x0.t_min x1.t_min;
          t_max    = Bounds.inter x0.t_max x1.t_max;
          t_rc     = Refcount.empty } in
      recompute_refcount (discard_addrem x), accrel, accsn, acci

    (** Inclusion check *)
    let is_le (main_sat0: n_cons -> bool) (x0: t) (x1: t): bool =
      if Bi_fun.size x0.t_env != Bi_fun.size x1.t_env then
        Log.fatal_exn "incompatible envs (2)";
      (* Environment *)
      let env =
        Bi_fun.fold_dom
          (fun o i0 acc ->
            try Aa_maps.add (Bi_fun.image o x1.t_env) i0 acc
            with Not_found ->
              (* crashing here is probably avoidable
               * => we should simply drop singular entries of only one side *)
              Log.fatal_exn "incompatible envs (1)"
          ) x0.t_env Aa_maps.empty in
      let le_res =
        Graph_is_le.is_le ~submem: true x0.t_graph
          None (make_sat main_sat0 x0) x1.t_graph env in
      match le_res with
      | None -> false
      | Some _ -> true (* should we forward any information ??? *)

    (** Regression testing *)
    let ind_check
        (usat: n_cons -> bool) (* underlying domain sat function *)
        (off: Offs.t) (iname: string) (x: t): bool =
      (* construction of the inductive edge, assuming no parameter (for now) *)
      let ind = Ind_utils.ind_find iname in
      assert (ind.i_ppars = 0 && ind.i_ipars = 0 && ind.i_spars = 0);
      let ie = { ie_ind  = ind;
                 ie_args = { ia_ptr = [];
                             ia_int = [] } } in
      (* retrieving offset, and building injection and graph to compare *)
      let src =
        try Bi_fun.image off x.t_env
        with Not_found -> Log.fatal_exn "ind_check, offset not found" in
      let inj = Aa_maps.singleton src src in
      let g =
        let g = graph_empty x.t_graph.g_inds in
        let g = sv_add src Ntaddr Nnone g in
        ind_edge_add src ie g in
      (* constraint satisfaction check *)
      let sat (c: n_cons): bool =
        make_sat usat x c in
      (* comparison and extraction of the result *)
      let r =
        Graph_is_le.is_le_partial None false ~submem:true x.t_graph None
          IntSet.empty sat g inj in
      match r with
      | Ilr_not_le | Ilr_le_seg _ | Ilr_le_ind _ -> false
      | Ilr_le_rem (_, _, emb, inst) ->
          assert (inst = IntMap.empty);
          true

    (** Write inside the sub-memory *)
    let write (sat: n_cons -> bool) (dst: int * Offs.t) (ex: n_expr) (x: t): t =
      match ex with
      | Ne_var iglo -> (* this is a mutation *)
          let iloc = glo_to_loc x iglo in
          Log.info "Mutation inside sub-mem (%d => %d)" iloc iglo;
          Log.info "sub-mutation: %s ::= %d" (onode_2str dst) iloc;
          let e = { pe_size = Offs.size_of_int 4; (* temporary, to fix *)
                    pe_dest = iloc, Offs.zero } in
          { x with
            t_graph = pt_edge_replace sat dst e x.t_graph }
      | _ -> Log.todo_exn "submem_write, complex expression"

    (** Guard inside the sub-memory *)
    let guard (c: n_cons) (x: t): t =
      match graph_guard true c x.t_graph with
      | Gr_bot -> Log.todo_exn "bottom found in submem-guard"
      | Gr_no_info -> x
      | _ -> (* might be possible to do something here to improve precision *)
          Log.info "submem-guard: other result"; x
  end: SUBMEM_SIG)
