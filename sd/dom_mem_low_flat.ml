(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_mem_low_flat.ml
 **       Flat, summarization-less memory abstract domain
 ** Xavier Rival, 2013/05/10 *)
open Data_structures
open Flags
open Lib
open Timer

open Ast_sig
open Dom_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig
open Svenv_sig

open Ast_utils
open Dom_utils
open Graph_utils
open Nd_utils


(** Improvements to consider:
 **  - consider interface change for cell_read (see comments in the function
 **    definition)
 **  - consider interface change for cell_write, by doing a value join of all
 **    the disjuncts: the only reason why this function creates disjuncts is
 **    to accomodate the cases where a set of pointer addresses needs to be
 **    considered; it would be more efficient to do a value join at that
 **    point, and not to produce disjuncts
 **)


(** Error report *)
module Log =
  Logger.Make(struct let section = "dm_flat_" and level = Log_level.DEBUG end)


(** Set of nodes *)
module NodeOrd =
  struct
    type t = int * Offs.t
    let compare (n0, o0) (n1, o1) =
      let c = n0 - n1 in
      if c = 0 then Offs.compare o0 o1
      else c
    let t_2str (n, o) = Printf.sprintf "(%d,%s)" n (Offs.t_2str o)
  end
module NodeSet = SetMake( NodeOrd )


module DBuild = functor (Dv: DOM_VALSET) ->
  (struct
    (** Module name *)
    let module_name = "[flat]"
    (** Dom ID *)
    let dom_id: mod_id ref = ref (-1, "flat")
        
    (** Type definition *)
    (* Cell contents, defined by a SV name and a size *)
    type cell_contents =
        { cc_val:   int;      (* name of the SV representing it *)
          cc_size:  Offs.size (* size of the cell *) }
    (* Flat block *)
    type f_block = cell_contents Block_frag.t
    (* Flat node:
     *  - each SV explicitely denotes either a numeric value or an address *)
    type f_node =
        { f_id:      int;        (* id *)
          (* memory attached to the node:
           *  - None if it is a basic value    (explicit value node)
           *  - Some block if contiguous block (explicit address node) *)
          f_block:   f_block option;
          (* references in other f_ndoes *)
          (*f_precs:   IntSet.t;*)
          (* type of the value represented *)
          f_typ:     ntyp; }
    (* Flat abstract memory
     *  - this structure is intended to remain quite stable during most
     *    basic operations, so as to keep cost down (in particular for
     *    join operation --in case of physical equality, it is in O(1)) *)
    type f_mem = (int, f_block) Aa_maps.t
    (* Pointer information *)
    type ptr_info = (int, NodeSet.t) Aa_maps.t
    (* An abstract value encloses
     *  - a memory, which resembles a graph, without ind/seg
     *  - a value abstraction
     *)
    type t =
        { (* allocator for names *)
          t_nkey:   Keygen.t;
          (* memory contents *)
          t_mem:    (int, f_node) Aa_maps.t;
          (* pointer information:
           *  - either not present: may be anything
           *  - or present: may be only one of the pointers in the set
           * note: all nodes referred to in this set should be explicit
           *       address nodes *)
          t_ptreqs: (int, NodeSet.t) Aa_maps.t;
          (* predecessor information (reverse map for t_ptreqs) *)
          t_preds:  (int, IntSet.t) Aa_maps.t;
          (* abstraction of values *)
          t_num:    Dv.t;
          (* environment modifications *)
          t_envmod: svenv_mod; }


    (** Domain initialization to a set of inductive definitions *)

    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (g: Keygen.t) (s: StringSet.t): Keygen.t =
      if s != StringSet.empty then Log.fatal_exn "init_inductives not allowed";
      let g = Dv.init_inductives g s in
      let g, k = Keygen.gen_key g in (* this domain generates keys *)
      if sv_upg then dom_id := k, snd !dom_id;
      g
    let inductive_is_allowed (_: string): bool = false


    (** Fixing sets of keys *)

    let sve_sync_bot_up (x: t): t * svenv_mod =
      { x with t_envmod = svenv_empty }, x.t_envmod
      

    (** Lattice elements *)

    (* Bottom element *)
    let bot: t =
      { t_nkey   = Keygen.empty;
        t_mem    = Aa_maps.empty;
        t_ptreqs = Aa_maps.empty;
        t_preds  = Aa_maps.empty;
        t_num    = Dv.bot;
        t_envmod = svenv_empty; }
    let is_bot (x: t): bool = Dv.is_bot x.t_num

    (* Top element, with empty set of roots *)
    let top (): t =
      { t_nkey   = Keygen.empty;
        t_mem    = Aa_maps.empty;
        t_ptreqs = Aa_maps.empty;
        t_preds  = Aa_maps.empty;
        t_num    = Dv.top;
        t_envmod = svenv_empty; }

    (* Pretty-printing *)
    let t_2stri (ind: string) (x: t): string =
      let s0 =
        Aa_maps.fold_left
          (fun (is: int) (n: f_node) acc ->
            match n.f_block with
            | None -> acc
            | Some b ->
                Block_frag.fold_list_base
                  (fun bnd cc acc ->
                    let bndstr =
                      if Bounds.is_zero bnd then ""
                      else Printf.sprintf "@%s" (Bounds.t_2str bnd) in
                    Printf.sprintf "%s%s%d%s -%s-> %d\n" acc ind is bndstr
                      (Offs.size_2str cc.cc_size) cc.cc_val
                  ) b acc
          ) x.t_mem "" in
      let s1 =
        Aa_maps.fold_left
          (fun (is: int) (ptrs: NodeSet.t) acc ->
            Printf.sprintf "%s%s%d in {%s}\n" acc ind is
              (NodeSet.t_2str "; " ptrs)
          ) x.t_ptreqs "" in
      let s2 =
        Aa_maps.fold_left
          (fun i s acc ->
            Printf.sprintf "%s%s%d <= {%s}\n" acc ind i (IntSet.t_2str "," s)
          ) x.t_preds "" in
      let sve =
        if !Flags.flag_debug_symvars then
          Printf.sprintf "%sSVE-Dom-flat:\n%s" ind
            (svenv_2stri (ind^"  ") x.t_envmod)
        else "" in
      Printf.sprintf "%s%s%s%s%s" s0 s1 s2
        (Dv.t_2stri IntMap.empty ind x.t_num) sve

    let t_2str: t -> string = t_2stri ""

    (* External output *)
    let ext_output (o: output_format) (base: string) (namer: namer) (x: t)
        : unit =
      Log.todo_exn "ext output"


    (** Utilities *)

    (* Get functions *)
    let get_f_node (msg: string) (i: int) (x: t): f_node =
      try Aa_maps.find i x.t_mem
      with Not_found -> Log.fatal_exn "get_f_node(%s): %d" msg i
    let get_ptrs (msg: string) (i: int) (x: t): NodeSet.t =
      try Aa_maps.find i x.t_ptreqs
      with Not_found -> Log.fatal_exn "get_ptrs(%s): %d" msg i

    (* Updating the pointer equalities sets *)
    (* Removal of all may-aliases corresponding to node n *)
    let rem_ptr_equalities_node (n: int) (x: t): t =
      if !flag_debug_domfshape then
        Log.force "rem_ptr_eqs called on %d" n;
      let oalias =
        try Aa_maps.find n x.t_ptreqs with Not_found -> NodeSet.empty in
      let opreds =
        NodeSet.fold (fun (i, _) -> IntSet.add i) oalias IntSet.empty in
      let x =
        IntSet.fold
          (fun i x ->
            let opreds =
              try Aa_maps.find i x.t_preds with Not_found -> IntSet.empty in
            let npreds = IntSet.remove n opreds in
            { x with t_preds = Aa_maps.add i npreds x.t_preds }
          ) opreds x in
      { x with t_ptreqs = Aa_maps.remove n x.t_ptreqs }
    (* Addition of one may-alias to node n *)
    let add_ptr_equality (n: int) ((aa, ao) as a: int * Offs.t) (x: t): t =
      (* new aliasing *)
      let oalias =
        try Aa_maps.find n x.t_ptreqs with Not_found -> NodeSet.empty in
      let nalias = NodeSet.add a oalias in
      (* new predecessor situation *)
      let op = try Aa_maps.find aa x.t_preds with Not_found -> IntSet.empty in
      let np = IntSet.add n op in
      (* result *)
      { x with
        t_ptreqs = Aa_maps.add n nalias x.t_ptreqs;
        t_preds  = Aa_maps.add aa np x.t_preds; }
    (* Addition of several may-aliases to node n *)
    let add_ptr_equalities (n: int) (aliases: NodeSet.t) (x: t): t =
      NodeSet.fold (add_ptr_equality n) aliases x

    (* Join of pointer equalities *)
    let join_ptr_info (ptrsl: ptr_info) (ptrsr: ptr_info)
        : ptr_info * IntSet.t (* drop left *) * IntSet.t (* drop right *) =
      let f_drop side p0 p1 =
        Aa_maps.fold
          (fun i _ acc ->
            if Aa_maps.mem i p1 then acc else IntSet.add i acc
          ) p0 IntSet.empty in
      let dl = f_drop "R" ptrsl ptrsr in
      let dr = f_drop "L" ptrsr ptrsl in
      Aa_maps.fold
        (fun i p0 acc ->
          try
            let p1 = Aa_maps.find i ptrsr in
            Aa_maps.add i (NodeSet.union p0 p1) acc
          with Not_found -> acc
        ) ptrsl Aa_maps.empty, dl, dr
    (* Trivial join, e.g., after assignment or guard;
     * assumes that only t_num and t_ptreqs may differ *)
    let gen_join_flatten (j: join_kind) (xl: t) (xr: t): t =
      if not (xl.t_nkey == xr.t_nkey) || not (xl.t_mem == xr.t_mem) then
        Log.fatal_exn "gen_join_flatten, arguments inconsistent";
      (* since gen_join_flatten can be called internally
       * e.g. by internal_join avec cell_write, the sven_mod
       * are not necessarely empty, though we need to return
       * the join of the two svenv_mod instead of empty svenv_mod *)
      if !Flags.flag_debug_domfshape then
        Log.force "join_flatten:\n%s\n%s"
          (t_2stri "  " xl) (t_2stri "  " xr);
      let eqs, dl, dr = join_ptr_info xl.t_ptreqs xr.t_ptreqs in
      let f_drop d m = IntSet.fold Aa_maps.remove d m in
      let predl = f_drop dl xl.t_preds in
      let predr = f_drop dr xr.t_preds in
      let pred =
        Aa_maps.fold
          (fun i pl acc ->
            let pr = try Aa_maps.find i predr with Not_found -> IntSet.empty in
            let p = IntSet.union pl pr in
            Aa_maps.add i p acc
          ) predl predr in
      let sve = svenv_join xl.t_envmod xr.t_envmod in
      { xl with
        t_ptreqs = eqs;
        t_preds  = pred;
        t_num    = Dv.upper_bnd j xl.t_num xr.t_num;
        t_envmod = sve; }
    let join_flatten: t -> t -> t = gen_join_flatten Jjoin
    (* Flatten to a list of length at most one *)
    let join_flatten_list (l: t list): t list =
      match l with
      | [ ] | [ _ ] -> l
      | x0 :: l1 -> [ List.fold_left join_flatten x0 l1 ]
 

    (** Management of symbolic variables *)
    (* Will that symb. var. creation be allowed by the domain? *)
    let sv_is_allowed ?(attr: node_attribute = Attr_none) (nt: ntyp)
        (na: nalloc) (x: t): bool =
      match attr, na with
      | Attr_ind _, _ | Attr_array _, _
      | _, Nheap _ | _, Nsubmem -> false
      | _ -> true
    (* Add a fresh symbolic variable, and generates an id *)
    let sv_add_fresh 
        ?(attr: node_attribute = Attr_none) ?(root: bool = false)
        (t: ntyp) (na: nalloc) (x: t): int * t =
      let k, i = Keygen.gen_key x.t_nkey in
      assert (not (Aa_maps.mem i x.t_mem));
      assert (not (Aa_maps.mem i x.t_ptreqs));
      let bo, is_heap =
        match na with
        | Nnone -> None, false
        | Nstack | Nstatic -> (* Stack space creation *)
            Some (Block_frag.create_empty Bounds.zero), false
        | Nheap _ -> (* Heap space creation *)
            (* do the creation; flag the block as 'heap' *)
            Some (Block_frag.create_empty Bounds.zero), true
        | Nsubmem -> Log.fatal_exn "sv_add_fresh: submem" in
      if is_heap then Log.info "creation in the heap";
      let f = { f_id    = i;
                f_block = bo;
                f_typ   = t } in
      let num =
        match attr, t with
        | Attr_array (size, Some fields), Ntraw ->
            (* For now the address node is also in the value domain
             * is it possible to eliminate them from the value domain *)
            if !enable_array_domain then Dv.sv_array_add i size fields x.t_num 
            else Dv.sv_add i x.t_num 
        | Attr_array (_,None), Ntaddr ->
            if !enable_array_domain then Dv.sv_array_address_add i x.t_num 
            else Dv.sv_add i x.t_num 
        | _ -> Dv.sv_add i x.t_num in
      i, { x with
           t_nkey   = k;
           t_mem    = Aa_maps.add i f x.t_mem;
           t_num    = num;
           t_envmod = { x.t_envmod with
                        svm_add = PMap.add i t x.t_envmod.svm_add } }
    (* Recover information about a symbolic variable *)
    let sv_get_info (i: int) (x: t): nalloc option * ntyp option = 
      let f_i = get_f_node "sv_get_info" i x in
      let onalloc = 
        match f_i.f_block with
        | None -> Some Nnone
        | Some _ -> None (* flat domain keep no info about allocation zone *) in
      onalloc, Some f_i.f_typ


    (** Sanity checks *)

    (* Gathering all sanity checks in a same function *)
    let do_sanity_check (ctxt: string) (x: t): unit =
      (* extraction of the nodes *)
      let nodes, nodes_a =
        Aa_maps.fold
          (fun i n (accn, acca) ->
            IntSet.add i accn,
            if n.f_block = None then acca else IntSet.add i acca
          ) x.t_mem (IntSet.empty, IntSet.empty) in
      (* local custom Log.fatal_exn report *)
      let error (msg: string) =
        let fset = IntSet.t_2str ", " in
        Log.info "Mem was:\n%sNodes: {%s}\nAddresses: {%s}"
          (t_2stri "   " x) (fset nodes) (fset nodes_a);
        Log.fatal_exn "sanity_check <%s> failed: %s" ctxt msg in
      (* consistency inside the graph part *)
      Aa_maps.iter
        (fun i f ->
          match f.f_block with
          | None -> ()
          | Some b ->
              Block_frag.fold_list_base
                (fun _ cc () ->
                  if not (IntSet.mem cc.cc_val nodes) then
                    error (Printf.sprintf "edges: %d" cc.cc_val);
                ) b ()
        ) x.t_mem;
      (* checking the pointer information part *)
      Aa_maps.iter
        (fun i ptrs ->
          if not (IntSet.mem i nodes) then
            error " pointer info (val)";
          NodeSet.iter
            (fun (j, _) ->
              if not (IntSet.mem j nodes_a) then
                Log.warn "pointer info, addr (img:%d,%d)" i j;
              if not (IntSet.mem j nodes) then
                error (Printf.sprintf "pointer info (img:%d,%d)" i j);
            ) ptrs
        ) x.t_ptreqs;
      (* checking of the predecessors part *)
      let real_preds =
        Aa_maps.fold
          (fun i ptrs acc ->
            NodeSet.fold
              (fun (j, _) acc ->
                let o =
                  try Aa_maps.find j acc
                  with Not_found -> IntSet.empty in
                Aa_maps.add j (IntSet.add i o) acc
              ) ptrs acc
          ) x.t_ptreqs Aa_maps.empty in
      Aa_maps.iter
        (fun i _ ->
          let pred =
            try Aa_maps.find i x.t_preds
            with Not_found -> IntSet.empty in
          let real_pred =
            try Aa_maps.find i real_preds
            with Not_found -> IntSet.empty in
          if not (IntSet.equal pred real_pred) then
            Log.fatal_exn "predecessors do not match for %d" i
        ) x.t_mem;
      (* checking of the allocator *)
      Keygen.sanity_check "dom-mem-flat" nodes x.t_nkey;
      (* checking of the underlying numerical domain *)
      if not (Dv.check_nodes nodes x.t_num) then
        Log.fatal_exn "underlying domain nodes"
    let sanity_check (ctxt: string) (x: t): unit =
      if flag_sanity_fshape then do_sanity_check ctxt x

    (* Garbage collection *)
    let gc (roots: int uni_table) (x: t): t =
      x (* nothing to do for GC in this module *)

    (** Graph encoding (used for guiding join) *)
    let encode (disj: int) (n: namer) (x: t)
        : renamed_path list * PairSetSet.t * int =
      Log.todo_exn "encode"

    (** Comparison and Join operators *)

    (* Checks if the left argument is included in the right one *)
    let is_le (roots_rel: int bin_table) (_: int bin_table)
        (xl: t) (xr: t): svenv_upd option =
      sanity_check "is_le,before,l" xl;
      sanity_check "is_le,before,r" xr;
      if xl.t_nkey = xr.t_nkey && xl.t_mem == xr.t_mem then
        if Dv.is_le xl.t_num xr.t_num (fun i j -> false) then
          try
            Aa_maps.iter
              (fun i o1 ->
                let o0 =
                  try Aa_maps.find i xl.t_ptreqs
                  with Not_found -> raise Stop in
                if not (NodeSet.subset o0 o1) then raise Stop
              ) xr.t_ptreqs;
            Some svenv_upd_identity
          with Stop -> None
        else None
      else Log.fatal_exn "is_le: roots not physically equal"

    (* Generic join:
     *  It assumes all svenv modifications were already synchronized,
     *  and returns with an empty svenv modification record *)
    let internal_join (j: join_kind) (xl: t) (xr: t): t =
      sanity_check "join-l,before" xl;
      sanity_check "join-r,before" xr;
      let res =
        if xl.t_nkey = xr.t_nkey && xl.t_mem == xr.t_mem then
          gen_join_flatten j xl xr
        else if Keygen.equal xl.t_nkey xr.t_nkey then
          begin
            (* for now, we treat only the case where mems are equal *)
            if Aa_maps.size xl.t_mem != Aa_maps.size xr.t_mem then
              Log.fatal_exn "join: inconsistent states (size)";
            Aa_maps.iter
              (fun i fl ->
                let fr =
                  try Aa_maps.find i xr.t_mem
                  with Not_found ->
                    Log.fatal_exn "join: inconsistent states (mem)" in
                if fl.f_id != fr.f_id then
                  Log.fatal_exn "join: inconsistent ids";
                if fl.f_typ != fr.f_typ then
                  Log.fatal_exn "join: inconsistent types";
                match fl.f_block, fr.f_block with
                | None, None -> ( )
                | None, Some _ | Some _, None ->
                    Log.fatal_exn "join: inconsistent opts"
                | Some bl, Some br ->
                    if Block_frag.cardinal bl != Block_frag.cardinal br then
                      Log.fatal_exn "join: inconsistent block sizes";
                    Block_frag.fold_list2_base
                      (fun bndl bndr cl cr () ->
                        if not (Bounds.eq bndl bndr) then
                          Log.fatal_exn "join: inconsistent block bounds";
                        if cl.cc_val != cr.cc_val then
                          Log.fatal_exn
                            "join: inconsistent block content values";
                        if not (Offs.size_eq cl.cc_size cr.cc_size) then
                          Log.fatal_exn "join: inconsistent block content sizes"
                      ) bl br ()
              ) xl.t_mem;
            gen_join_flatten j xl { xr with
                                    t_nkey   = xl.t_nkey;
                                    t_mem    = xl.t_mem;
                                    t_envmod = svenv_empty; }
          end
        else Log.fatal_exn "join: roots not physically eq" in
      sanity_check "join,after" res;
      res
    let join (j: join_kind) (_: int hint_bs option) (_: (onode lint_bs) option)
        (_: int tri_table) (_: int tri_table)
        ((xl, _): t * join_ele) ((xr, _): t * join_ele)
        : t * svenv_upd * svenv_upd =
      internal_join j xl xr, svenv_upd_identity, svenv_upd_identity

    (* Directed weakening; over-approximates only the right element *)
    let directed_weakening (_: int hint_bs option)
        (_: int tri_table) (_: int tri_table) (xl: t) (xr: t)
        : t * svenv_upd =
      (* for now, simply returns the right argument;
       * directed weakening is supposed to act on shape only *)
      xr, svenv_upd_identity

    (* Unary abstraction, a kind of relaxed canonicalization operator *)
    let local_abstract (ho: int hint_us option) (x: t): t =
      x (* no local_abstract operator needed here *)


    (** Cell operations *)

    (* Dereference of a cell *)
    let extract (vo: Offs.t) (sz: int) (b: cell_contents Block_frag.t): int =
      let c = Block_frag.find_addr (Bounds.of_offs vo) b in
      if Offs.size_eq (Offs.size_of_int sz) c.cc_size then
        c.cc_val
      else Log.fatal_exn "size mismatch"
    let deref_tlv_opt (x: t) ((vi, vo): int * Offs.t) (sz: int): int option =
      let f = Aa_maps.find vi x.t_mem in
      match f.f_block with
      | None -> None
      | Some b ->
          if !enable_array_domain && Dv.is_array_address vi x.t_num then
            let j = (Block_frag.find_addr Bounds.zero b).cc_val in
            let xilist = Dv.sv_array_deref j vo x.t_num in
            assert (List.length xilist = 1);
            let num, i = List.hd xilist in
            Some i
          else Some (extract vo sz b)
    let deref_tlv (x: t) ((ovi,ovo):int * Offs.t) ((vi, vo): int * Offs.t)
        (sz: int) =
      let f = Aa_maps.find vi x.t_mem in
      match f.f_block with
      | None -> Log.fatal_exn "deref_tlv @ %d, no block found" vi
      | Some b ->
          (* when there are more than than alias,disjunctions are
           * introduced not only by alias but also by undermined
           * relation between variable and array group. However
           * both kinds of disjuncts are mixed in one list *)
          if !enable_array_domain && Dv.is_array_address vi x.t_num then
            let j = (Block_frag.find_addr Bounds.zero b).cc_val in
            let xilist = Dv.sv_array_deref j vo x.t_num in
            List.map
              (fun (num, i) -> 
                { x with t_num = num }, (ovi, ovo) , Some (i, Offs.zero)
              ) xilist
          else
            let j = extract vo sz b in
            [ x, (ovi, ovo), Some (j, Offs.zero) ]
    let deref_array_id  (x:t) (vi: int) =
      let f = get_f_node "deref_array_id" vi x in
      match f.f_block with
      | None -> Log.fatal_exn "deref_array_id @ %d, no block found" vi
      | Some b -> (Block_frag.find_addr (Bounds.zero) b).cc_val

    (* Creation of a cell *)
    let cell_create ?(attr:node_attribute = Attr_none) ((si, so): onode)
        (size: Offs.size) (nt: ntyp) (x: t): t =
      sanity_check "cell_create,before" x;
      let sbnd = Bounds.of_offs so in
      let f = get_f_node "cell_create" si x in
      (* creates destination node *)
      let dst, x = 
        if !enable_array_domain then
          sv_add_fresh ~attr:attr ~root:false nt Nnone x 
        else
          sv_add_fresh nt Nnone x in
      if !Flags.flag_debug_domfshape then
        Log.force "add flat cell (%d,%s) => %d" si (Offs.t_2str so) dst;
      let f =
        let cc = { cc_size = size;
                   cc_val  = dst } in
        match f.f_block with
        | None -> Log.fatal_exn "cell_create: not applied to a block"
        | Some b ->
            let b =
              Block_frag.append_tail sbnd
                (Bounds.add_size sbnd cc.cc_size) cc b in
            { f with f_block = Some b } in
      let x = { x with t_mem = Aa_maps.add si f x.t_mem } in
      Array_pred_utils.deref := IntMap.add si dst !Array_pred_utils.deref; 
      sanity_check "cell_create,after" x;
      x

    (* Deletion of a cell *)
    let cell_delete ?(free: bool = true) ?(root:bool = false)
        (i: int) (x: t): t =
      sanity_check "cell_delete,before" x;
      if free then
        Log.todo_exn "cell_delete: deallocation!"; (* it is a deallocation *)
      (* removal of a value node *)
      let rem_valnode (acc: IntSet.t) (x: t) (i: int): IntSet.t * t =
        let nv = get_f_node "cell_delete(v)" i x in
        assert (nv.f_block = None);
        (* remove pointer equalities related to i, if any *)
        let x = rem_ptr_equalities_node i x in
        (* as a value node, i should not have any predecessors *)
        if Aa_maps.mem i x.t_preds then
          Log.fatal_exn "rem_valnode, has predecessors";
        IntSet.add i acc,
        { x with
          t_nkey   = Keygen.release_key x.t_nkey i;
          t_mem    = Aa_maps.remove i x.t_mem;
          t_envmod = { x.t_envmod with
                       svm_rem = PSet.add i x.t_envmod.svm_rem }; } in
      let n = get_f_node "cell_delete(a)" i x in
      (* removal of a flat block *)
      let s, x =
        match n.f_block with
        | None -> Log.fatal_exn "cell_delete; not an address"
        | Some b ->
            Block_frag.fold_base
              (fun _ cc (acc, x) ->
                  rem_valnode acc x cc.cc_val
              ) b (IntSet.singleton i, x) in
      let x = { x with t_mem = Aa_maps.remove i x.t_mem; } in
      (* removal of lost pointer information:
       *   if pred may point to some offset from i, thus its alias information
       *   should be abstracted to top altogether *)
      let preds =
        try Aa_maps.find i x.t_preds with Not_found -> IntSet.empty in
      let x = IntSet.fold rem_ptr_equalities_node preds x in
      (* result, release of the key, and removal in the num domain *)
      let x =
        { x with
          t_nkey   = Keygen.release_key x.t_nkey i;
          t_num    = IntSet.fold Dv.sv_rem s x.t_num;
          t_envmod = { x.t_envmod with
                       svm_rem = PSet.add i x.t_envmod.svm_rem }; } in
      sanity_check (Printf.sprintf "cell_delete,after,%d" i) x;
      x

    (* Read *)
    let cell_read 
        (is_resolve: bool)(* is from cell-resolve*)
        ((vi,vo): onode)  (* address of the cell *)
        (sz: int)         (* size of the cell *) 
        (x: t)            (* input abstract memory *)
        : (t              (* output, unchanged in this module *) 
           * onode        (* address of the cell, unchanged in this module *)
           * onode option (* Some content if successful, None otherwise *)
          ) list =        (* list of disjuncts *)
      let f = get_f_node "cell_read" vi x in
      match f.f_block with
      | Some b -> (* f is an address *)
          begin
            try 
              if !enable_array_domain 
                  && Dv.is_array_address vi x.t_num then
                let j = (Block_frag.find_addr (Bounds.zero) b).cc_val in
                let xilist = Dv.sv_array_deref j vo x.t_num in
                List.map
                  (fun (num,i) -> 
                    { x with t_num = num }, (vi, vo), Some (i, Offs.zero)
                  ) xilist
              else
                let j = (Block_frag.find_addr (Bounds.of_offs vo) b).cc_val in
                [ x, (vi, vo), Some (j, Offs.zero) ]
            with
            | Not_found ->
                if !flag_debug_domfshape then
                  Log.force "cell_read: block, not found";
                [ x, (vi, vo), None ]
          end
      | None -> (* f is a val, try pointers *)
          let opt_ns =
            try Some (Aa_maps.find vi x.t_ptreqs)
            with Not_found -> None in
          match opt_ns with
          | None -> 
              if !flag_debug_domfshape then
                Log.force "cell_read: %d ptreqs, not found" vi;
              [ x, (vi, vo), None ]
          | Some ns ->
              NodeSet.fold
                (fun (i0, o0) acc -> (* treat alias (i0,o0) *)
                  let v = i0, Offs.add vo o0 in
                  let j =
                    try deref_tlv x (vi,vo) v sz
                    with
                    | Not_found ->
                        Log.fatal_exn "cell_read, alias not mapped" in
                  (* Possible performance gain:
                   *  -> we could gain in performance by grouping elements in
                   *     the list below all together with the same "x"
                   *  -> we currently duplicate references to x, and this will
                   *     cause unnecessary duplications later in the evaluation
                   *  This makes pointer assign. less efficient than
                   *  it could be.
                   *  Also:
                   *  -> the old assign uses Ne_rand for numerical assignment
                   *     instead of doing many precise numerical assignments
                   *     and then one join afterwards
                   *)
                  List.append j acc
                ) ns [ ]

    (* Resolving a cell *)
    let cell_resolve
        ((vi,vo): onode) (* address of the cell *)
        (sz: int)        (* size of the cell *)
        (x: t)           (* input abstract memory *)
        : (t             (* output, unchanged in this module *) 
           * onode       (* address of the cell, unchanged in this module *)
           * bool        (* whether cell resolution was successful *)
          ) list =       (* list of disjuncts *)
      let is_cell_resolved ((vi, vo): onode): bool =
        let f = get_f_node "cell_resolve" vi x in
        match f.f_block with
        | Some b ->
            (!enable_array_domain && Dv.is_array_address vi x.t_num
           || Block_frag.mem (Bounds.of_offs vo) b)
        | None   -> false in
      if is_cell_resolved (vi, vo) then
        if !enable_array_domain && (Dv.is_array_address vi x.t_num) then
          let array_id = deref_array_id x vi in
          let num,i = Dv.sv_array_materialize array_id vo x.t_num in
          [ { x with t_num = num }, (vi, vo), true ]
        else [ x, (vi, vo), true ]
      else
        try
          let ns = Aa_maps.find vi x.t_ptreqs in
          if NodeSet.for_all is_cell_resolved ns then
            if !enable_array_domain && (Dv.is_array_address vi x.t_num) then
              let array_id = deref_array_id x vi in
              let num,i = Dv.sv_array_materialize array_id vo x.t_num in
              [ { x with t_num = num }, (vi, vo), true ]
            else
              [ x, (vi, vo), true ]
          else [ x, (vi, vo), false ]
        with Not_found -> [ x, (vi, vo), false ]

    (* Write into a cell *)
    let cell_write: ntyp -> onode -> int -> n_expr -> t -> t =
      let rec aux_write
          (is_rec: bool) (* bound on number of recursion steps *)
          (ntyp: ntyp) (dst: onode) (size: int) (nex: n_expr) (x: t): t list =
        if !flag_debug_domfshape then
          Log.force "flat_write:\n - dst:  %s\n - size: %d\n - expr: %s"
            (onode_2str dst) size (n_expr_2str nex);
        (* write into a cell, that has been found writable *)
        match deref_tlv_opt x dst size with
        | None ->
            (* we need to look at pointer aliases *)
            let ptrs = get_ptrs "cell_write,1" (fst dst) x in
            (* apply aux to each element *)
            (* => can improve this code, by making a fast join
             *    (i.e., at the level of data only *)
            NodeSet.fold
              (fun (i,o) acc ->
                let u =
                  if is_rec then
                    Log.fatal_exn
                      "cell_write: recursion while exploring aliases"
                  else
                    aux_write true ntyp
                      (i, Offs.add o (snd dst)) size nex x in
                  u @ acc
              ) ptrs [ ]
        | Some dsti ->
            (* forget old pointer equalities attached to contents *)
            let x =
              if !enable_array_domain 
                  && Dv.is_array_address (fst dst) x.t_num then x
              else rem_ptr_equalities_node dsti x in
            (* numerical assignment *)
            let x = { x with t_num = Dv.assign dsti nex x.t_num } in
            (* pointer assignment if applicable *)
            let x =
              if ntyp = Ntaddr then
                let ndec = decomp_lin_opt nex in
                match ndec with
                | Some (i, exoff) -> (* then, we add an alias to (i,@exoff) *)
                    let off = Offs.of_n_expr exoff in
                    let iptrs =
                      try Aa_maps.find i x.t_ptreqs
                      with Not_found -> NodeSet.empty (* no known alias *) in
                    let iptrs =
                      if Offs.is_zero off then iptrs
                      else
                        NodeSet.fold
                          (fun (i,o) acc ->
                            NodeSet.add (i,Offs.add o off) acc
                          ) iptrs NodeSet.empty in
                    let ptrs =
                      if (get_f_node "cell_write,p" i x).f_block = None then
                        iptrs
                      else
                        NodeSet.add (i, off) iptrs in
                    if !flag_debug_domfshape then
                      Log.force "Aliases: {%s}, %d @ %s"
                        (NodeSet.t_2str ";" iptrs) i (n_expr_2str exoff);
                    if !enable_array_domain
                        && Dv.is_array_address (fst dst) x.t_num then x
                    else add_ptr_equalities dsti ptrs x
                | None -> x
              else x in
            (* dsti is modified: add it to svenv_mod *)
            let sve = { x.t_envmod with
                        svm_mod = Aa_sets.add dsti x.t_envmod.svm_mod } in
            let x = { x with t_envmod = sve } in
            [ x ] in
      fun (nt: ntyp) (d: onode) (s: int) (nex: n_expr) (x: t) ->
        let l = aux_write false nt d s nex x in
        match l with
        | [ ] -> Log.fatal_exn "aux_write returns empty list"
        | a :: b -> List.fold_left (internal_join Jjoin) a b


    (** Transfer functions for the analysis *)

    (* Evaluation result *)
    type expr_res =
      | Er_expr of n_expr list
      | Er_ptrs of NodeSet.t
          
    (* Condition test *)
    let guard (c: n_cons) (x: t): t =
      sanity_check "guard,before" x;
      let x = { x with t_num = Dv.guard true c x.t_num } in
      sanity_check "guard,after" x;
      x

    (* Checking that a constraint is satisfied *)
    let sat (c: n_cons) (x: t): bool =
      sanity_check "sat,before" x;
      Dv.sat x.t_num c


    (** Set domain *)
    let setv_add_fresh _ = Log.fatal_exn "set domain unsupported"
    let setv_delete _ = Log.fatal_exn "set domain unsupported"
    let set_sat _ = Log.fatal_exn "set domain unsupported"


    (** Unfolding, assuming and checking inductive edges *)

    (* Unfold *)
    let ind_unfold (u: unfold_dir) (lv: onode) (t: t): t list =
      Log.fatal_exn "ind_unfold (no support for inductives)"

    (* Assume construction *)
    let assume (op: meml_log_form) (t: t): t =
      match op with
      | SL_set _ -> Log.fatal_exn "set domain unsupported"
      | SL_ind _ -> Log.fatal_exn "ind_assume (no support for inductives)"
      | SL_seg _ -> Log.todo_exn "seg_assume"
      | SL_array -> { t with t_num = Dv.assume Opd0.SL_array t.t_num }

    (* Check construction, that an inductive be there *)
    let check (op: meml_log_form) (t: t): bool =
      match op with
      | SL_set _ -> Log.fatal_exn "set domain unsupported"
      | SL_ind _ -> Log.fatal_exn "ind_check (no support for inductives)"
      | SL_seg _ -> Log.todo_exn "seg_check"
      | SL_array -> Dv.check Opd0.SL_array t.t_num
  end: DOM_MEM_LOW)
