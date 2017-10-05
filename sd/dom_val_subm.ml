(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_val_subm.ml
 **       lifting of a numerical domain into a submemory abstraction
 **       (together with a main memory)
 ** Xavier Rival, Pascal Sotin, 2012/05/11 *)
open Data_structures
open Flags
open Lib
open Offs

open Dom_sig
open Dom_subm_sig
open Graph_sig
open Nd_sig
open Svenv_sig

open Dom_utils
open Graph_utils
open Nd_utils

open Apron

(** TODO:
 **  0. counting:
 **     - support the modulo with respect to the stride in the submem
 **     - eventually, move this support in the graph, with modulo information
 **       on SV values, when they denote addresses
 **     - add the guards on the environment
 **
 **  1. uniformize the treatment of the add_rem, and synchronization
 **
 **  - localization function
 **  - sanity check questions
 **  - finish function symvars_merge
 **  - delegation in transfer functions
 **)


(** Error report *)
module Log =
  Logger.Make(struct let section = "dv_subm_" and level = Log_level.DEBUG end)
(* whether or not to print full debug information *)
let full_debug = true
let show_sanity_check = true


(** Node kind *)
type node_kind =
  | Nk_address
  | Nk_contents


(** Module construction *)
module Make_Val_Subm = functor (Dv: DOM_VALUE) -> functor (S: SUBMEM_SIG) ->
  (struct
    let module_name = "dom_val_subm"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s -> %s\n%s%s"
        module_name Dv.module_name
        module_name S.module_name
        (Dv.config_2str ())
        (S.config_2str ())
    module S = Dom_subm_graph.Submem

    (** Dom ID *)
    let dom_id = ref (-1, "msubm")
    (** Type of abstract values *)
    (* each sub-memory is attached to a base address and a content node
     * (abbr c-node)
     *  - snodes maps each id for a node living in a sub-memory
     *    to the sub-memory and sub-node
     *  - sub-node indexes are negative integers
     *)
    type t =
        { (* main memory: underlying domain *)
          t_main:   Dv.t;
          (* base address node -> content node *)
          t_bases:  (int, int) Bi_fun.t;
          (* content node -> sub-memory *)
          t_subs:   S.t IntMap.t;
          (* sub-nodes localization: global -> (sub-memory, sub-node) *)
          t_snodes: (int * int) IntMap.t;
          (* next subnode index *)
          t_snxt:   int }

    (** Internal utilities *)
    (* Error report (probably temporary) *)
    let inner_warn (rst: bool) (s: string): unit =
      Log.warn "submem layer<%s>%s"
        s (if rst then "RESET LOSING INFO." else ".")

    (** Conversions functions *)
    (* Checks whether it is a sub-node *)
    let is_subnode (x: t) (i: int): bool = IntMap.mem i x.t_snodes
    (* From addresses to contents and sub-memories *)
    let addr_2cont (x: t) (addr: int): int =
      try Bi_fun.image addr x.t_bases
      with Not_found -> Log.fatal_exn "submem addr %d not found" addr
    let cont_2submem (x: t) (cont: int): S.t =
      try IntMap.find cont x.t_subs
      with Not_found -> Log.fatal_exn "submem val %d not found" cont
    let addr_2submem (x: t) (addr: int): S.t =
      cont_2submem x (addr_2cont x addr)
    let glo_2subnode (ctx: string) (x: t) (i: int): int * int =
      try IntMap.find i x.t_snodes
      with Not_found -> Log.fatal_exn "%s failed to retrieve %d" ctx i
    let cont_2addr (x: t) (cont: int): int =
      try Bi_fun.inverse_inj cont x.t_bases
      with Not_found -> Log.fatal_exn "submem cont %d not found" cont
    (* Offsets simplification *)
    let make_osimplifier (x: t) (o: Offs.t): Offs.t =
      Offs.of_n_expr (Dv.simplify_n_expr x.t_main (Offs.to_n_expr o))
    (* Simplification of expressions *)
    let simplify_n_expr (x: t) (ex: n_expr): n_expr =
      inner_warn false "simplify_n_expr";
      Dv.simplify_n_expr x.t_main ex
    (** Management of underlying domains symbolic variables *)
    let subnode_bind (ig: int) (loc: int * int) (x: t): t =
      if !flag_debug_submem then
        Log.force "subnode_bind %d -> %d" ig (snd loc);
      { x with t_snodes = IntMap.add ig loc x.t_snodes }
    let add_subnode (sub: int) (sn: int) (x: t): t * int =
      assert (x.t_snxt < 0);
      let n = x.t_snxt in
      { x with
        t_main   = Dv.add_node n x.t_main;
        t_snodes = IntMap.add n (sub, sn) x.t_snodes;
        t_snxt   = n - 1; }, n
    (* Adding a node to a sub-memory *)
    let add_node_submem (nk: node_kind) (x: t) (cont: int) (sub: S.t)
        : t * int * int * S.t =
      (* global key for the address *)
      let x, nglo =
        let n = x.t_snxt in
        let nn = n - 1 in
        assert (n < 0);
        { x with
          t_main   = Dv.add_node n x.t_main;
          t_snxt   = nn; }, n in
      (* local addition of the address *)
      let nloc, sub =
        match nk with
        | Nk_address  -> S.sv_add_address nglo sub
        | Nk_contents -> S.sv_add_contents nglo sub in
      (* binding of the global key *)
      let x = subnode_bind nglo (cont, nloc) x in
      x, nglo, nloc, sub
    (** Unfolding support *)
    let tag_unfold_exn (cont: int) (f: 'a -> 'b) (x: 'a): 'b =
      try f x
      with
      | Unfold_request (Uloc_main n, d) ->
          raise (Unfold_request (Uloc_sub (cont, n), d))
    (** Check no impact if modif on global SV *)
    let may_impact_sv_mod (i: int) (x: t): bool =
      try
        IntMap.iter
          (fun _ sub ->
            if S.may_impact_sv_mod i sub then raise Stop
          ) x.t_subs;
        false
      with Stop -> true

    (** Domain initialization *)
    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (g: Keygen.t) (s: StringSet.t): Keygen.t =
      let g, k = Keygen.gen_key g in (* this domain generates keys *)
      if sv_upg then dom_id := k, snd !dom_id;
      S.init_inductives g s

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t =
      { t_main   = Dv.bot;
        t_bases  = Bi_fun.empty_inj;
        t_subs   = IntMap.empty;
        t_snodes = IntMap.empty;
        t_snxt   = -1; }
    let is_bot (x: t): bool =
      Dv.is_bot x.t_main
    (* Top element *)
    let top: t =
      { t_main   = Dv.top;
        t_bases  = Bi_fun.empty_inj;
        t_subs   = IntMap.empty;
        t_snodes = IntMap.empty;
        t_snxt   = -1; }
    (* Pretty-printing *)
    let t_2stri (sn: sv_namer) (ind: string) (x: t): string =
      let s = Dv.t_2stri sn ind x.t_main in
      let s =
        if full_debug then
          Printf.sprintf "%s%sglobal dict (%d): <|%s|>\n" s ind x.t_snxt
            (IntMap.t_2str ";" (fun (i,j) -> Printf.sprintf "(%d,%d)" i j)
               x.t_snodes)
        else s in
      if x.t_subs = IntMap.empty then s
      else
        let nind = "  "^ind in
        (* printing of base addresses *)
        let s =
          if full_debug then
            Bi_fun.fold_dom
              (fun i j acc -> Printf.sprintf "%s%s    %d => %d\n" acc ind i j)
              x.t_bases (Printf.sprintf "%s%sbases:\n" s ind)
          else s in
        (* printing of sub-memories contents *)
        IntMap.fold
          (fun i sub acc ->
            Printf.sprintf "%s%s%d:\n%s" acc ind i (S.t_2stri nind sub)
          ) x.t_subs s

    (** Utilities for environment addition and reduction *)
    (* reduction of the whole environment *)
    let sub_env_reduce (x: t): t =
      let m =
        IntMap.fold
          (fun _ sub m ->
            let olmin = Bounds.to_off_list (S.get_omin sub)
            and olmax = Bounds.to_off_list (S.get_omax sub) in
            OffMap.fold
              (fun o delta m ->
                let m =
                  List.fold_left
                    (fun m omax ->
                      Log.info "@@@r: %s < %s     [%d]"
                        (Offs.t_2str o) (Offs.t_2str omax) delta;
                      let ne = Offs.size_to_n_expr (Offs.sub omax o) in
                      let nc = Nc_cons (Tcons1.SUPEQ, ne, Ne_csti delta) in
                      Dv.guard true nc m
                    ) m olmax in
                List.fold_left
                  (fun m omin ->
                    Log.info "@@@l: %s <= %s"
                      (Offs.t_2str omin) (Offs.t_2str o);
                    let ne = Offs.size_to_n_expr (Offs.sub o omin) in
                    let nc = Nc_cons (Tcons1.SUPEQ, ne, Ne_csti 0) in
                    Dv.guard true nc m
                  ) m olmin
              ) (S.get_off_ds sub) m
          ) x.t_subs x.t_main in
      { x with t_main = m }
    (* addition functions with and without reduction *)
    let sub_env_add (o: Offs.t) (i: int) (sub: S.t): S.t =
      let omaxl = Bounds.to_off_list (S.get_omax sub) in
      List.iter
        (fun om ->
          Log.info "@@@nnn: %s <= %s" (Offs.t_2str o) (Offs.t_2str om);
        ) omaxl ;
      S.env_add o i sub
    let sub_env_add_reduce (o: Offs.t) (i: int) (sub: S.t) (x: t): S.t * t =
      let omaxl = Bounds.to_off_list (S.get_omax sub) in
      let x =
        List.fold_left
          (fun accx omax ->
            Log.info "@@@y: %s <= %s" (Offs.t_2str o) (Offs.t_2str omax);
            let ne = Offs.size_to_n_expr (Offs.sub omax o) in
            let nc = Nc_cons (Tcons1.SUPEQ, ne, Ne_csti 0) in
            { x with t_main = Dv.guard true nc x.t_main }
          ) x omaxl in
      Log.info "after additions:\n%s" (t_2stri IntMap.empty "   " x);
      S.env_add o i sub, x

    (** Sanity checks *)

    (* Sanity properties:
     *  - all sub-memories should be sane
     * (other properties to add)
     * TODO: sanity check
     *  - global nodes referring to a sub-memory should be negative
     *  - snodes should map keys to each sub-memory according to its
     *    actual contents
     *  - snodes should belong to [t_snxt+1, -1]
     *)
    let sanity_check (ctx: string) (x: t): unit =
      let error (msg: string) =
        Log.fatal_exn "sanity_check<%s> fails (domsub): %s" ctx msg in
      try
        IntMap.iter (fun _ s -> S.sanity_check ctx s) x.t_subs;
        let submem_nodes =
          IntMap.fold
            (fun glo (sub, loc) acc ->
              if glo >= 0 then
                error "found positive global key for submem"
              else if glo <= x.t_snxt then
                error "too low sub index"
              else
                let ksub =
                  try IntMap.find sub acc with Not_found -> IntSet.empty in
                IntMap.add sub (IntSet.add loc ksub) acc
            ) x.t_snodes IntMap.empty in
        IntMap.iter
          (fun sub set ->
            try
              let smem = IntMap.find sub x.t_subs in
              (* ??? are the local or global keys ??? *)
              let smemkeys = S.get_keys smem in
              if !flag_debug_submem then
                begin
                  Log.force "Check, %s, looking for submem %d" ctx sub;
                  Log.force " - computed keys: %s" (intset_2str set);
                  Log.force " - actual keys: %s" (intset_2str smemkeys);
                end;
              if not (IntSet.equal set smemkeys) then
                error "submem nodes do not correspond to index"
            with Not_found -> error "unbound submem number"
          ) submem_nodes;
      with e ->
        Log.info "Before sanity check:\n%s" (t_2stri IntMap.empty "  " x);
        raise e


    (** Management of symbolic variables *)

    (* For sanity check *)
    let check_nodes (s: IntSet.t) (x: t): bool =
      Dv.check_nodes s x.t_main

    (* Node addition and removal *)
    let add_node (id: int) (x: t): t =
      { x with t_main = Dv.add_node id x.t_main }
    let rem_node (id: int) (x: t): t =
      let rem_submem_contents (id: int) (x: t): t =
        (* Removal of a sub-memory contents
         *  - unlink its base address
         *  - unlink its index entries *)
        let nbases = Bi_fun.rem_inv id x.t_bases in
        let nsubs = IntMap.remove id x.t_subs in
        let nsnodes, nnum =
          IntMap.fold
            (fun i (cont, _) acc ->
              if cont = id then
                IntMap.remove i (fst acc), Dv.rem_node i (snd acc)
              else acc
            ) x.t_snodes (x.t_snodes, x.t_main) in
        { x with
          t_main   = Dv.rem_node id nnum;
          t_bases  = nbases;
          t_subs   = nsubs;
          t_snodes = nsnodes; } in
      (* TODO:
       * - the first case does not seem to occur
       * - in the last case, there is one occurence of a deleted offset in
       *   the environment; it should just be processed as such...
       *)
      if Bi_fun.mem_dir id x.t_bases then
        (* we drop all info about the sub-memory itself first,
         * and then remove the base afterwards *)
        (* though, we keep the contents, node, with no info about it
         * (this case is rather unsatisfactory: contents should always
         *  be removed first; to INVESTIGATE) *)
        let cont = Bi_fun.image id x.t_bases in
        Log.warn "REM_NODE: removes sub-memory address before contents!";
        let x = rem_submem_contents cont x in
        { x with t_main = Dv.add_node cont (Dv.rem_node id x.t_main) }
      else if IntMap.mem id x.t_subs then
        rem_submem_contents id x
      else
        begin
          if may_impact_sv_mod id x then
            begin
              Log.info "disposing %d in\n%s" id
                (t_2stri IntMap.empty "   " x);
              Log.warn "rem_sv, should drop sub-mem";
            end;
          { x with t_main = Dv.rem_node id x.t_main }
        end
    (* Synchronization of the SV environment *)
    let sve_sync_top_down (svm: svenv_mod) (t: t): t =
      svenv_mod_doit (fun i _ -> add_node i) rem_node
        (fun i -> Log.fatal_exn "mod: %d" i) svm t
    (* Renaming (e.g., post join) *)
    let symvars_srename (om: (Offs.t * int) OffMap.t)
        (nm: (int * Offs.t) node_mapping) (x: t): t =
      if !flag_debug_submem then
        Log.force "S.symvars_srename, BEFORE:\n%s"
          (t_2stri IntMap.empty "  " x);
      (* for now, only singletons supported for addresses and contents nodes *)
      let f_one (i: int): int = (* works iff *one* image *)
        try
          let (ni, s) = IntMap.find i nm.nm_map in
          if s = IntSet.empty then ni
          else Log.fatal_exn "symvars_srename several images: %d" i
        with
        | Not_found ->
            Log.fatal_exn "symvars_srename no image: %d" i in
      let nbases =
        Bi_fun.fold_dom
          (fun base content acc ->
            let nbase = f_one base in
            let ncontent = f_one content in
            assert (not (Bi_fun.mem_dir nbase acc));
            Bi_fun.add nbase ncontent acc
          ) x.t_bases Bi_fun.empty_inj in
      (* - renaming inside the underlying value abstraction *)
      let main = Dv.symvars_srename om nm x.t_main in
      (* - add nodes corresponding to "new offsets" (added in the join when
       *   offsets could not be unified *)
      let main = OffMap.fold (fun _ (_, i) -> Dv.add_node i) om main in
      (* - renaming in sub-memories and add equalities synthesized
       *   when new offsets generated *)
      let nsubs, eqs =
        IntMap.fold
          (fun icont sub (acc_s, acc_e) ->
            let iaddr = S.get_addr sub in
            let nicont = f_one icont in
            assert (not (IntMap.mem nicont acc_s));
            let nm = { nm with
                       nm_suboff = fun o -> nm.nm_suboff (iaddr, o) } in
            let sub, eqs = S.symvars_srename om nm sub in
            IntMap.add nicont sub acc_s, eqs @ acc_e
          ) x.t_subs (IntMap.empty, [ ]) in
      let main = List.fold_left (fun acc e -> Dv.guard true e acc) main eqs in
      (* - renaming inside the snodes field *)
      let nsnodes =
        IntMap.fold
          (fun mid (sub, lid) acc ->
            IntMap.add mid (f_one sub, lid) acc
          ) x.t_snodes IntMap.empty in
      if !flag_debug_submem then
        Log.force "srename:\n%s\nmapping:\n%s"
          (t_2stri IntMap.empty "   " x)
          (Nd_utils.node_mapping_2str nm);
      let x =
        { t_main   = main;
          t_bases  = nbases;
          t_subs   = nsubs;
          t_snodes = nsnodes;
          t_snxt   = x.t_snxt; } in
      if !flag_debug_submem then
        Log.force "S.symvars_srename, AFTER:\n%s"
          (t_2stri IntMap.empty "  " x);
      sanity_check "symvars_srename, after" x;
      x
    (* Check the symbolic vars correspond exactly to given set *)
    let symvars_check (s: IntSet.t) (x: t): bool =
      sanity_check "symvars_check" x;
      let sub_keys = IntMap.fold (fun i _ -> IntSet.add i) x.t_snodes s in
      Dv.symvars_check sub_keys x.t_main
    (* Removes all symbolic vars that are not in a given set *)
    let symvars_filter (s: IntSet.t) (x: t): t =
      inner_warn (not (Bi_fun.is_empty x.t_bases)) "symvars_filter";
      { t_main   = Dv.symvars_filter s x.t_main;
        t_bases  = Bi_fun.empty_inj;
        t_subs   = IntMap.empty;
        t_snodes = IntMap.empty;
        t_snxt   = -1; }

    (* Maintaining consistency with the symbolic names in the sub-memory:
     *  - gets set of locally removed nodes (g), and perform global removal;
     *  - gets set of locally added nodes (l), and perform global addition *)
    let sync_addrem (x: t): t =
      IntMap.fold
        (fun isub sub x ->
          let sub, add, rem = S.sync_addrem sub in
          (* treat removal of local nodes *)
          IntSet.iter (fun irem -> assert (irem < 0)) rem;
          let x =
            IntSet.fold
              (fun iglo x ->
                { x with
                  t_snodes = IntMap.remove iglo x.t_snodes;
                  t_main   = Dv.rem_node iglo x.t_main }
              ) rem { x with t_subs = IntMap.add isub sub x.t_subs } in
          (* treat additions *)
          IntSet.fold
            (fun iloc x ->
              let x, iglo = add_subnode isub iloc x in
              let sub = IntMap.find isub x.t_subs in
              let sub = S.register_node iloc iglo sub in
              { x with t_subs = IntMap.add isub sub x.t_subs }
            ) add x
        ) x.t_subs x

    (* Merging into a new variable *)
    let symvars_merge
        (stride: int) (* stride of the structure being treated *)
        (base: int)   (* node serving as a base address of a block (gen mem) *)
        (sv: int)     (* node serving as a new block content *)
        (block_desc: (Bounds.t * onode * Offs.size) list) (* merged contents *)
        (extptrs: OffSet.t)  (* offsets of external pointers into the block *)
        (x: t)
        : t =
      if !flag_debug_submem then
        begin
          Log.force ("\n\nCall to symvars_merge:\n" ^^
                     "  - stride: %d\n" ^^
                     "  - base: %d\n  - sv: %d\n" ^^
                     "  - block:")
            stride base sv;
          List.iter
            (fun (b, (i, o), _) ->
              Log.force "       %s => (%d,%s)%s" (Bounds.t_2str b) i
                (Offs.t_2str o) (if i = base then "   [submem entry]" else "")
            ) block_desc;
          Log.force "  - ext ptrs to: %s" (OffSet.t_2str "; " extptrs);
          let bs =
            Bi_fun.fold_dom (fun i _ -> IntSet.add i) x.t_bases IntSet.empty in
          let nbs = IntSet.cardinal bs in
          Log.force "  - other bases: %d" nbs;
          Bi_fun.iter_dir
            (fun i _ -> Log.force "      %d => ." i) x.t_bases;
        end;
      (* pre-filtering of the block description
       *  -> to see whether we are merging into a pre-existing sub-memory:
       *     i.e., we distinguish two cases;
       *     - either there is no sub-memory at all
       *     - or there is one sub-memory at the beginning of the block;
       *  -> we should expand this with more possibilities *)
      let expanding, block_desc =
        match block_desc with
        | [ ] -> false, [ ]
        | (bnd0, on0, _) :: block_desc1 ->
            (* block_desc1 should not contain any sub-memory *)
            List.iter
              (fun (_, (i1, _), _) ->
                if IntMap.mem i1 x.t_subs then
                  Log.fatal_exn "sub-memories beyond beg"
              ) block_desc1;
            if IntMap.mem (fst on0) x.t_subs then
              (* first block element is a sub-memory *)
              true, block_desc1
            else
              (* no sub-memory in the first item *)
              false, block_desc in
      (* pre-sorting of the block description, along the stride *)
      let block_decomp =
        let rec aux accu ongoing bd =
          match bd with
          | [] ->
              Log.info " . remaining elts: %d" (List.length ongoing);
              List.iter
                (fun (b, on, _) ->
                  Log.info "    %s: %s" (Bounds.t_2str b) (onode_2str on)
                ) ongoing;
              accu
          | (bnd, dst, sz) :: bd0 ->
              let b0, b1 = Bounds.modulo_split stride bnd in
              if Bounds.is_zero b1 then (* aligned on stride *)
                aux ((b0, ((b1, dst, sz) :: ongoing)) :: accu) [] bd0
              else (* not aligned on stride; push and continue *)
                aux accu ((b1, dst, sz) :: ongoing) bd0 in
        aux [] [] (List.rev block_desc) in
      (* if there is no sub-memory, create one *)
      (* Extraction of the existing sub-memory or creation of a new one *)
      let x, sub =
        if Bi_fun.mem_dir base x.t_bases then
          (* there is already a sub-memory here; we should extend it *)
          let cont = Bi_fun.image base x.t_bases in
          assert expanding;
          assert (IntMap.mem cont x.t_subs);
          let sub  = IntMap.find cont x.t_subs in
          if !flag_debug_submem then
            Log.force "  - old submem:\n%s" (S.t_2stri "      " sub);
          (* - removal of the pre-existing sub-memory that is being merged
           * - renaming of all references to the previous sub-memory *)
          let snodes =
            IntMap.fold
              (fun sn old_binding ->
                let p =
                  if fst old_binding = cont then sv, snd old_binding
                  else old_binding in
                IntMap.add sn p
              ) x.t_snodes IntMap.empty in
          { x with
            t_bases  = Bi_fun.rem_dir base x.t_bases;
            t_subs   = IntMap.remove cont x.t_subs;
            t_snodes = snodes; }, sub
        else
          (* we attempt to create a sub-memory *)
          let sub = S.empty base sv stride Bounds.zero Bounds.zero in
          assert (not expanding);
          x, sub in
      (* Addition of address nodes into the sub-memory *)
      let x, sub, block_decomp =
        List.fold_left
          (fun (x, sub, acc_block) (bnd_stride, sub_block) ->
            if !flag_debug_submem then
              Log.force "Phase 1, Sub-block: %s (%d)"
                (Bounds.t_2str bnd_stride) (List.length sub_block);
            (* this first method for searching for the local address is
             * a bit unclear to me *)
            let offs_list = Bounds.to_off_list bnd_stride in
            let offs =
              List.fold_left
                (fun acc o ->
                  if OffSet.mem o extptrs then OffSet.add o acc else acc
                ) OffSet.empty offs_list in
            let b_already_there =
              List.fold_left
                (fun acc o -> acc || S.env_mem o sub) false offs_list in
            if b_already_there then
              let oloc_addr =
                OffSet.fold
                  (fun o acc ->
                    match acc with
                    | Some _ -> acc
                    | None -> try Some (S.env_find o sub) with Not_found -> acc
                  ) offs None in
              let loc_addr =
                match oloc_addr with
                | Some a -> a
                | None ->
                    (* no offset found as part of ext pointers:
                     * we search internal pointers from inside the sub-memory
                     * (2nd method to search for the local address) *)
                    let i =
                      List.fold_left
                        (fun acc o ->
                          match acc with
                          | Some _ -> acc
                          | None ->
                              if S.env_mem o sub then Some (S.env_find o sub)
                              else None
                        ) None offs_list in
                    match i with
                    | Some a -> a
                    | None ->
                        Log.fatal_exn "symvars_merge: found no local address" in
              let sub = S.node_assume_placed loc_addr sub in
              if !flag_debug_submem then
                Log.force "Existing offset @ node %d" loc_addr;
              x, sub, (loc_addr, bnd_stride, sub_block) :: acc_block
            else
              (* TODO: extend the sub-memory scope here *)
              let x, glo_addr, loc_addr, sub =
                add_node_submem Nk_address x sv sub in
              (* addition of the environment if needed *)
              let sub =
                if offs != OffSet.empty && !flag_debug_submem then
                  begin
                    Log.force "Adding %d offset" (OffSet.cardinal offs);
                    OffSet.iter
                      (fun o -> Log.info "  - %s" (Offs.t_2str o)) offs;
                  end;
                OffSet.fold (fun o -> sub_env_add o loc_addr) offs sub in
              x, sub, (loc_addr, bnd_stride, sub_block) :: acc_block
          ) (x, sub, []) block_decomp in
      (* Update the max offset of the sub-memory *)
      let sub =
        match block_decomp with
        | [ ] -> sub
        | (_, b, _) :: _ -> S.update_max b stride sub in
      (* Addition of edges into the sub-memory *)
      let x, sub, eqs =
        List.fold_left
          (fun (x, sub, eqs) (addr, bnd_stride, sub_block) ->
            if !flag_debug_submem then
              Log.force "Ph2,Sub-block: %s" (Bounds.t_2str bnd_stride);
            (* construction of the sub-block *)
            List.fold_left
              (fun (x, sub, eqs) (bnd_off, (idst, odst), sz) ->
                let x, sub, cont, eqs =
                  if idst = base then
                    x, sub, S.env_find odst sub, eqs
                  else
                    (* same operations for the contents key as for addr key
                     * (we may factor those) *)
                    let x, glo_cont, cont, sub =
                      add_node_submem Nk_contents x sv sub in
                    let eqs =
                      if Offs.is_zero odst then (glo_cont, idst) :: eqs
                      else eqs in
                    x, sub, cont, eqs in
                (* addition of th ecell in the sub heap *)
                if !flag_debug_submem then
                  Log.force "Addition in sub-block: %d + %s -> %d + %s"
                    addr (Bounds.t_2str bnd_off) cont (Offs.t_2str odst);
                x, S.add_cell addr bnd_off sz cont sub, eqs
              ) (x, sub, eqs) sub_block
          ) (x, sub, [ ]) (List.rev block_decomp) in
      (* reduction into the sub-memory *)
      let sub = S.post_build sub in
      (* feeding the environment *)
      (* for now, we only carry out the node addition *)
      let x = add_node sv x in
      if !flag_debug_submem then
        Log.force "Adding submem (addr: %d; cont: %d)" base sv;
      (* taking equalities into the global env *)
      let num =
        List.fold_left
          (fun num (glo, loc) ->
            if !flag_debug_submem then
              Log.force "Equality: %d = %d" glo loc;
            Dv.guard true (Nc_cons (Tcons1.EQ, Ne_var glo, Ne_var loc)) num
          ) x.t_main eqs in
      let r =
        { x with
          t_main  = num;
          t_bases = Bi_fun.add base sv x.t_bases;
          t_subs  = IntMap.add sv sub x.t_subs; } in
      if !flag_debug_submem then
        Log.force "after add:\n%s" (t_2stri IntMap.empty "  " r);
      sanity_check "symvars_merge, after" r;
      r


    (** Comparison and join operators *)

    (* Comparison *)
    let is_le (x0: t) (x1: t) (sat_diseq: int -> int -> bool): bool =
      if Dv.is_le x0.t_main x1.t_main sat_diseq then
        try
          IntMap.iter
            (fun cont sub0 ->
              let sub1 =
                try IntMap.find cont x1.t_subs
                with Not_found -> raise Stop in
              if !flag_debug_submem then
                Log.force "Is_le status:\n - left:\n%s - right:\n %s"
                  (t_2stri IntMap.empty "    " x0)
                  (t_2stri IntMap.empty "    " x1);
              let b = S.is_le (Dv.sat x0.t_main) sub0 sub1 in
              if not b then raise Stop
            ) x0.t_subs;
          true
        with Stop -> false
      else false

    (* Upper bound: serves as join and widening *)
    let upper_bnd (k: join_kind) (x0: t) (x1: t): t =
      if !flag_debug_submem then
        Log.force "JOIN:\n-left:\n%s-right:\n%s"
          (t_2stri IntMap.empty "  " x0) (t_2stri IntMap.empty "  " x1);
      (* Make both elements compatible:
       *  - if sub-memory only in one side, then downgrade it to raw node *)
      let drop_incompat (xa: t) (xb: t): t =
        Bi_fun.fold_dom
          (fun basea suba x ->
            if Bi_fun.mem_dir basea xb.t_bases then x
            else
              (* sub-memory information about suba should be dropped:
               *  - add suba to main memory, as a node with no information;
               *  - remove entries about suba and maina
               *  - filter out nodes in the sub-graph *)
              let snodes =
                let img =
                  try S.get_keys (IntMap.find suba x.t_subs)
                  with Not_found -> Log.fatal_exn "sanity issue" in
                Log.info "ffound keys: %s" (intset_2str img);
                IntSet.fold IntMap.remove img x.t_snodes in
              Log.warn "Submem: about to drop a sub-memory";
              { t_main   = Dv.add_node suba x.t_main;
                t_bases  = Bi_fun.rem_dir basea x.t_bases;
                t_subs   = IntMap.remove suba x.t_subs;
                t_snodes = snodes;
                t_snxt   = x.t_snxt }
          ) xa.t_bases xa in
      let x0 = drop_incompat x0 x1 in
      let x1 = drop_incompat x1 x0 in
      let sat0 = Dv.sat x0.t_main and sat1 = Dv.sat x1.t_main in
      (* Initialization of a relation for remapping:
       *  identity function over positive indexes *)
      let init_rel = Nrel.empty in
      (* Compute joins of sub-memories *)
      let subs, snodes, nrel, snxt =
        Bi_fun.fold_dom
          (fun base cont (accsubs, accsn, accrel, acci) ->
            assert
              (try Bi_fun.image base x1.t_bases = cont with Not_found -> false);
            let sub0 =
              try IntMap.find cont x0.t_subs
              with Not_found -> Log.fatal_exn "join, submem not found, l" in
            let sub1 =
              try IntMap.find cont x1.t_subs
              with Not_found -> Log.fatal_exn "join, submem not found, r" in
            (* computation of roots, and launch of the join *)
            let jsub, rel, snodes, acci =
              S.upper_bnd acci accrel accsn (base, cont) sat0 sub0 sat1 sub1 in
            IntMap.add cont jsub accsubs, snodes, rel, acci
          ) x0.t_bases (IntMap.empty, IntMap.empty, init_rel, -1) in
      sanity_check "join,compat,l" x0;
      sanity_check "join,compat,r" x1;
      let map0, map1 =
        let extract_init (snodes: (int * int) IntMap.t)
            : (int * Offs.t) node_mapping =
          let s = IntMap.fold (fun i _ -> IntSet.add i) snodes IntSet.empty in
          { nm_map = IntMap.empty;
            nm_rem = s;
            nm_suboff = fun _ -> (Log.info "nmap(1)"; true) } in
        let init0 = extract_init x0.t_snodes
        and init1 = extract_init x1.t_snodes in
        IntMap.fold
          (fun i (i0, i1) (acc0, acc1) ->
            Nd_utils.add_to_mapping i0 i acc0,
            Nd_utils.add_to_mapping i1 i acc1
          ) nrel.n_pi (init0, init1) in
      let main0 = Dv.symvars_srename OffMap.empty map0 x0.t_main in
      let main1 = Dv.symvars_srename OffMap.empty map1 x1.t_main in
      let main  = Dv.upper_bnd k main0 main1 in
      sub_env_reduce { t_main   = main;
                       t_bases  = x0.t_bases;
                       t_subs   = subs;
                       t_snodes = snodes;
                       t_snxt   = snxt }


    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (x: t) (c: n_cons): bool =
      (* Note: we should delegate this to the sub-memory if needed *)
      Dv.sat x.t_main c


    (** Condition test *)
    let guard (b: bool) (c: n_cons) (x: t): t =
      (* additional constraints synthesis, when constraints related to
       *  => if the constraint is of the form b+o0=b+o1,
       *  => if there is a sub-memory at base b,
       *     and b+o0=>n0, b+o1=>n1 in the sub-memory, then guard n0=n1 *)
      let x =
        match c with
        | Nc_cons (Tcons1.EQ | Tcons1.DISEQ as rel, e, Ne_csti 0)
        | Nc_cons (Tcons1.EQ | Tcons1.DISEQ as rel, Ne_csti 0, e) ->
            begin
              match Nd_utils.n_expr_decomp_base_off e with
              | None -> x
              | Some (eb, eoff) ->
                  if Bi_fun.mem_dir eb x.t_bases then
                    let sub = addr_2submem x eb in
                    try
                      let n = S.env_find (Offs.of_n_expr eoff) sub in
                      let cc =
                        S.up_n_cons sub (Nc_cons (rel, Ne_var n, Ne_csti 0)) in
                      { x with t_main = Dv.guard b cc x.t_main }
                    with Not_found -> x
                  else x
            end
        | Nc_cons (Tcons1.EQ | Tcons1.DISEQ as rel, e0, e1) ->
            begin
              let d0 = Nd_utils.n_expr_decomp_base_off e0
              and d1 = Nd_utils.n_expr_decomp_base_off e1 in
              match d0, d1 with
              | None, _ | _, None -> x
              | Some (b0, off0), Some (b1, off1) ->
                  if b0 = b1 && Bi_fun.mem_dir b0 x.t_bases then
                    let sub = addr_2submem x b0 in
                    try
                      let f (off: n_expr): int =
                        S.env_find (Offs.of_n_expr off) sub in
                      let n0 = f off0 and n1 = f off1 in
                      let cc =
                        S.up_n_cons sub
                          (Nc_cons (rel, Ne_var n0, Ne_var n1)) in
                      { x with t_main = Dv.guard b cc x.t_main }
                    with Not_found -> x
                  else x
            end
        | _ -> x in
      (* evaluate the guard in the main value abstraction (always doable) *)
      let x = { x with t_main = Dv.guard b c x.t_main } in
      (* if localizable in a single sub-memory, propagate down *)
      Log.info "locating constraint: %s" (n_cons_2str c);
      let _, osubmem =
        Nd_utils.n_cons_fold
          (fun i ((is_sub, osub) as acc) ->
            if is_sub && i < 0 then
              let mem, _ = glo_2subnode "guard-0" x i in
              if osub = None || osub = Some mem then true, Some mem
              else false, None
            else acc
          ) c (true, None) in
      match osubmem with
      | None -> x
      | Some isub ->
          if false then Log.info "located submem %d" isub;
          (* TODO: if there are global nodes, we should give up here !!! *)
          let f i = (* computes if local node; if not, global *)
            if is_subnode x i then snd (glo_2subnode "guard-1" x i) (* local *)
            else i (* global *) in
          let c = Nd_utils.n_cons_map f c in
          let sub = cont_2submem x isub in
          let submem = S.guard c sub in
          { x with t_subs = IntMap.add isub submem x.t_subs }


    (** Assignment *)
    let assign (dst: int) (ex: n_expr) (x: t): t =
      if may_impact_sv_mod dst x then Log.todo_exn "assign, submem drop"
      else if IntMap.mem dst x.t_subs then
        Log.todo_exn "delegate assign"
      else { x with t_main = Dv.assign dst ex x.t_main }
    let write_sub (sd: sub_dest) (size: int) (rv: n_rval) (x: t): t =
      (* extract the sub-memory and the location *)
      let base, cont, off, sub, l_loc =
        match sd with
        | Sd_env (base, off) ->
            let sub = addr_2submem x base in
            let l_loc = (* extraction of the submem node to modify *)
              let osimp = make_osimplifier x in
              match S.env_localize osimp off sub with
              | None -> Log.fatal_exn "write_sub, offset not found in submem"
              | Some l_loc -> l_loc in
            base, S.get_cont sub, off, sub, l_loc
        | Sd_int (inode, o) ->
            let i, j = glo_2subnode "write_sub" x inode in
            let sub = cont_2submem x i in
            Log.info "found %d, %d" i j;
            S.get_addr sub, S.get_cont sub, o, sub, (j, o) in
      let f_debug = false in
      if f_debug then
        Log.info "write called: %d @ {{{%s}}} ::== []"
          base (Offs.t_2str off);
      (* prepare the sub-memory, by adding a node for the new value *)
      let prepare_submem (): t * int * S.t =
        let x, glo, _, sub = add_node_submem Nk_contents x cont sub in
        x, glo, sub in
      (* perform a mutation inside the sub-memory
       *  - do the write in the sub-memory
       *  - update the sub-memory table *)
      let perform_mutation lloc (x, nex, sub, main) =
        let nsub = tag_unfold_exn cont (S.write (sat x) lloc nex) sub in
        { x with
          t_subs = IntMap.add cont nsub x.t_subs;
          t_main = main } in
      (* case split on the right hand side *)
      match rv with
      | Rv_addr (n, o) ->
          if f_debug then
            Log.info "write_sub:\n - offset found: %s\n - rv-addr: %d,%s"
              (onode_2str l_loc) n (Offs.t_2str o);
          if S.env_mem o sub then Log.fatal_exn "already there"
          else if n = base then
            (* assignment of an address inside the same sub-memory *)
            (* - add a local node for the offset *)
            let x, r_glo, r_loc, sub = add_node_submem Nk_contents x cont sub in
            let sub, x = sub_env_add_reduce o r_loc sub x in
            if f_debug then
              Log.info "sub-mem, stage 1:\n%s" (S.t_2stri "  " sub);
            (* does not work for relative offsets ?
             *  ex: 8*i+4  *)
            perform_mutation l_loc (x, Ne_var r_glo, sub, x.t_main)
          else Log.fatal_exn "write_sub: pointer to other external node"
      | Rv_expr ex ->
          if f_debug then
            Log.info "write_sub:\n - offset found: %s\n - expr: %s"
              (onode_2str l_loc) (Nd_utils.n_expr_2str ex);
          (* - add a node in the sub-memory if needed
           * - perform numeric assignment if needed *)
          let x, nex, sub, main =
            match ex with
            | Ne_var rglo ->
                if rglo < 0 then
                  (* the mutation is internal to the sub-memory *)
                  x, ex, sub, x.t_main
                else (* the mutation points to outside the sub-memory *)
                  let x, nglo, sub = prepare_submem () in
                  x, Ne_var nglo, sub, Dv.assign nglo ex x.t_main
            | _ ->
                (* proceed to a node creation, and assign in the numerics
                 * with a trivial write in the submemory ? *)
                let x, nglo, sub = prepare_submem () in
                x, Ne_var nglo, sub, Dv.assign nglo ex x.t_main in
          (* perform the mutation *)
          perform_mutation l_loc (x, nex, sub, main)

    (** Sub-memory specific functions *)
    (* Checks whether a node is of sub-memory type *)
    let is_submem_address (i: int) (x: t): bool =
      Bi_fun.mem_dir i x.t_bases
    let is_submem_content (i: int) (x: t): bool =
      IntMap.mem i x.t_subs

    (* Read of a value inside a submemory block *)
    let submem_read (sat: n_cons -> bool)
        (addr: int) (* symbolic variable denoting the sub-memory address *)
        (off: Offs.t) (sz: int) (* offset and size *)
        (x: t): onode =
      let cont = addr_2cont x addr in
      let sub = addr_2submem x addr in
      let osimplifier = make_osimplifier x in
      tag_unfold_exn cont (S.read_sub_base_off osimplifier off sz) sub
    let submem_deref (sat: n_cons -> bool)
        (src: int) (* symbolic variable denoting the sub-node address *)
        (off: Offs.t) (sz: int) (* offset and size *)
        (x: t): onode =
      let cont, iintern = glo_2subnode "submem_deref" x src in
      Log.info "deref in submemory of cont (%d,%d) [%s,%d]\n%s"
        cont iintern (Offs.t_2str off) sz (t_2stri IntMap.empty "   " x);
      let sub = cont_2submem x cont in
      tag_unfold_exn cont (S.read_sub_internal iintern off sz) sub

    (* Localization of a node in a sub-memory *)
    let submem_localize (iglo: int) (x: t): sub_localize =
      let isub, iloc = glo_2subnode "submem_localize" x iglo in
      let sub = cont_2submem x isub in
      match S.localize_offset_of_node iloc sub with
      | Some off -> (* offset found *)
          let ibasis = cont_2addr x isub in
          Log.warn "SUBMEM_LOCALIZE";
          Sl_found (ibasis, off)
      | None ->
          (* If the node corresponds to an address in the sub-memory,
           * allocate an offset for it and bind it *)
          if S.localize_node_in_block iglo sub then Sl_inblock isub
          else Sl_unk (* fail to provide a localization *)
    let submem_bind (isub: int) (iglo: int) (o: Offs.t) (x: t): t * onode =
      let addr = cont_2addr x isub in
      let _, iloc = glo_2subnode "submem_bind" x iglo in
      let sub, x = sub_env_add_reduce o iloc (cont_2submem x isub) x in
      Log.info "@@@@@binding";
      { x with t_subs = IntMap.add isub sub x.t_subs }, (addr, o)
    (* Unfolding *)
    let unfold (cont: int) (n: nid) (udir: unfold_dir) (x: t)
        : (int IntMap.t * t) list =
      sanity_check "unfold,in" x;
      let sub = cont_2submem x cont in
      let l = S.unfold (Dv.sat x.t_main) n udir sub in
      List.map
        (fun (nsub, renaming, lcons) ->
          let main =
            List.fold_left (fun acc cons -> Dv.guard true cons acc)
              x.t_main lcons in
          let x =
            sync_addrem { x with
                          t_subs   = IntMap.add cont nsub x.t_subs;
                          t_main   = main } in
          sanity_check "unfold,out" x;
          renaming, x
        ) l

    (** Array domain specific functions *)
    let add_array_node (id: int) (size: int) (fld: int list) (x: t): t =
      { x with t_main = Dv.add_array_node id size fld x.t_main }
    let add_array_address (id: int) (x: t): t =
      { x with t_main = Dv.add_array_address id x.t_main }
    let is_array_address (id: int) (x: t): bool =
       Dv.is_array_address id x.t_main
    let array_node_deref (id: int) (off: Offs.t) (x: t): (t * int) list =
      let vlist = Dv.array_node_deref id off x.t_main in
      List.map (fun (v,i) -> { x with t_main = v }, i) vlist
    let array_materialize (id: int) (off: Offs.t) (x: t): t * int =
      let m, v = Dv.array_materialize id off x.t_main in
      { x with t_main = m },v
    let expand (id: int) (nid: int) (x: t): t =
      { x with t_main = Dv.expand id nid x.t_main}
    let compact (lid: int) (rid: int) (x: t): t =
      { x with t_main = Dv.compact lid rid x.t_main}
    let meet (lx: t) (rx: t): t =
      Log.todo_exn "meet in subm"

    (* Forget the information about an SV *)
    let sv_forget (id: int) (x: t): t =
      Log.todo_exn "forget in subm"

    (** Export of range information *)
    let bound_variable (dim: int) (x: t): interval =
      Log.todo_exn "bound_variable in subdom"

    (** Temporaries specific for array *)
    let check (op: vcheck_op) (x: t): bool =
      match op with
      | VC_ind (i, off, iname) ->
          (* retrieval of the sub-memory, and underlying ind_check *)
          let sub = addr_2submem x i in
          S.ind_check (Dv.sat x.t_main) off iname sub
      | _ -> Log.fatal_exn "array check in submem"

    let assume (op: vassume_op) (x: t): t =
      match op with
      | VA_array -> Log.fatal_exn "array assume in submem"
      | _ -> Log.fatal_exn "unexpected assume"

    (** Extract all SVs that are equal to a given SV *)
    let get_eq_class (i: int) (x: t): IntSet.t =
      Log.fatal_exn "get_eq_class in submem"
  end: DOM_VALUE)
