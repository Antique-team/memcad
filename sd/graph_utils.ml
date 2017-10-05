(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: graph_utils.ml
 **       utility functions on graphs
 ** Xavier Rival, 2011/05/21 *)
open Data_structures
open Flags
open Lib
open Offs
open Apron

open Graph_sig
open Ind_sig
open Nd_sig
open Sv_sig
open Svenv_sig
open Set_sig
open Dom_sig
open Inst_sig

open Gen_dom

open Ind_utils


(** Possible improvements:
 **  - efficiency gain in graph_rename_ids: do not traverse the whole graph,
 **    but use the "prev" parameters instead
 **)


(** Error report *)
module Log =
  Logger.Make(struct let section = "g_uts___" and level = Log_level.DEBUG end)


(** Creation *)
(* Takes a set of inductive definitions *)
let graph_empty (inds: StringSet.t): graph =
  { g_inds   = inds;
    g_nkey   = Keygen.empty;
    g_g      = IntMap.empty;
    g_svemod = Dom_utils.svenv_empty;
    g_roots  = IntSet.empty;
    g_setvkey   = Keygen.empty;
    g_setvroots = IntSet.empty;
    g_setvkind  = IntMap.empty; }


(** Pretty-printing *)
let nid_2str (ni: nid): string =
  Printf.sprintf "%d" ni
let onode_2str ((ni,off): onode): string =
  if Flags.flag_pp_off0 || not (Offs.is_zero off) then
    Printf.sprintf "%s%s" (nid_2str ni) (Offs.t_2str off)
  else nid_2str ni
let bnode_2str ((ni,bnd): bnode): string =
  if Flags.flag_pp_off0 || not (Bounds.is_zero bnd) then
    Printf.sprintf "%s%s" (nid_2str ni) (Bounds.t_2str bnd)
  else nid_2str ni
let nalloc_2str: nalloc -> string = function
  | Nheap None      -> "[?? bytes, in heap]"
  | Nheap (Some sz) -> Printf.sprintf "[%d bytes, in heap]" sz
  | Nstack   -> "[stack]"
  | Nstatic  -> "[static]"
  | Nnone    -> "[none]"
  | Nsubmem  -> "[submem]"
let nalloc_2str_short: nalloc -> string = function
  | Nheap None      -> "h(?B)"
  | Nheap (Some sz) -> Printf.sprintf "h(%dB)" sz
  | Nstack   -> "sk"
  | Nstatic  -> "sc"
  | Nnone    -> ""
  | Nsubmem  -> "su"
let node_attribute_2str (a: node_attribute): string =
  match a with
  | Attr_none -> "(noattr)"
  | Attr_ind attr -> Printf.sprintf "(attr: %s)" attr
  | Attr_array (st, None) -> Printf.sprintf "(array stride: %d)" st
  | Attr_array (st, Some _) -> Printf.sprintf "(array stride: %d + fields)" st
let pt_edge_2str (src: bnode) (pe: pt_edge): string =
  let s_arrow =
    if Flags.flag_pp_size4 || Offs.size_to_int_opt pe.pe_size != Some 4 then
      Printf.sprintf "-%s->" (Offs.size_2str pe.pe_size)
    else "->" in
  Printf.sprintf "%s %s %s" (bnode_2str src) s_arrow (onode_2str pe.pe_dest)
let ind_args_2str (ia: ind_args): string =
  let l_2str = gen_list_2str "" (Printf.sprintf "<%d>") "," in
  let lset_2str = gen_list_2str "" (Printf.sprintf "S[%d]") "," in
  Printf.sprintf "%s|%s|%s" (l_2str ia.ia_ptr) (l_2str ia.ia_int)
    (lset_2str ia.ia_set)
let ind_edge_2str (ie: ind_edge): string =
  Printf.sprintf "==%s(%s)==>" ie.ie_ind.i_name (ind_args_2str ie.ie_args)
let block_2stria (ind: string) (is: int) (mc: pt_edge Block_frag.t)
    (acc: string): string =
  Block_frag.fold_list_base
    (fun bnd (pe: pt_edge) (acc: string) ->
      Printf.sprintf "%s%s%s\n" acc ind (pt_edge_2str (is,bnd) pe)
    ) mc acc
let heap_frag_2stri (ind: string) (is: nid) (e: heap_frag): string =
  match e with
  | Hemp -> ""
  | Hpt mc -> block_2stria ind is mc ""
  | Hind ie ->
      Printf.sprintf "%s%s %s\n" ind (nid_2str is) (ind_edge_2str ie)
  | Hseg se ->
      Printf.sprintf "%s%s =%s(%s)===%s(%s)=> %s\n" ind (nid_2str is)
        se.se_ind.i_name (ind_args_2str se.se_sargs)
        se.se_ind.i_name (ind_args_2str se.se_dargs)
        (nid_2str se.se_dnode)
let node_2stri (indent: string) (n: node): string =
  let s_attr =
    if Flags.flag_pp_nodeattr then
      Printf.sprintf " %s" (node_attribute_2str n.n_attr)
    else "" in
  let s_alloc =
    if Flags.flag_pp_nodealloc then nalloc_2str n.n_alloc
    else "" in
  let s_back =
    if Flags.flag_back_index && !Flags.flag_debug_back_index then
      Printf.sprintf "%s%d preds: %s\n" indent n.n_i (intset_2str n.n_preds)
    else "" in
  if !flag_pp_nodeinfos then
    (* default: print all infos about nodes *)
    Printf.sprintf "%s%d: %s%s%s\n%s%s" indent n.n_i (ntyp_2str n.n_t)
      s_attr s_alloc (heap_frag_2stri indent n.n_i n.n_e) s_back
  else (* otherwise, print only edges *)
    heap_frag_2stri indent n.n_i n.n_e
let node_2str: node -> string = node_2stri ""
let graph_2stri (ind: string) (g: graph): string =
  let roots =
    if !Flags.flag_debug_symvars then
      Printf.sprintf "%sroots: { %s }\n" ind (IntSet.t_2str ", " g.g_roots)
    else "" in
  let gr =
    IntMap.fold
      (fun _ (n: node) (acc: string) ->
        Printf.sprintf "%s%s" acc (node_2stri ind n)
      ) g.g_g "" in
  let sve =
    if !Flags.flag_debug_symvars then
      Printf.sprintf "%sSVE-Mod-graph:\n%s" ind
        (Dom_utils.svenv_2stri (ind^"  ") g.g_svemod)
    else "" in
  Printf.sprintf "%s%s%s" roots gr sve
let graph_2str: graph -> string = graph_2stri ""
(* Compact node output *)
let heap_frag_2strc: heap_frag -> string = function
  | Hemp -> "[emp]"
  | Hpt _ -> "[pt]"
  | Hind _ -> "[ind]"
  | Hseg _ -> "[seg]"
(* Algorithms results *)
let is_le_res_2str: is_le_res -> string = function
  | Ilr_not_le -> "not_le"
  | Ilr_le_rem _ -> "le_rem [..]"
  | Ilr_le_ind _ -> "le_ind [..]"
  | Ilr_le_seg _ -> "le_seg [..]"
(* Hints pretty-printing *)
let hint_ug_2str (h: hint_ug): string =
  Printf.sprintf "live: %s"
    (Aa_sets.t_2str "; " string_of_int h.hug_live)
let hint_bg_2str (h: hint_bg): string =
  Printf.sprintf "live: %s"
    (Aa_maps.t_2str "" "\n"
       (fun i j -> Printf.sprintf "%d => %d" j i) h.hbg_live)
(* Node embedding pretty-printing *)
let node_emb_2str (ni: node_emb): string =
  Aa_maps.t_2str "" "\n" (fun i j -> Printf.sprintf "%d => %d" i j) ni


(** Reachability from a node *)
let pt_edge_reach_acc (acc: IntSet.t) (pte: pt_edge): IntSet.t =
  let s = Offs.size_sym_var_ids_add acc pte.pe_size in
  let s = Offs.t_sym_var_ids_add s (snd pte.pe_dest) in
  IntSet.add (fst pte.pe_dest) s
let pt_edge_reach (pte: pt_edge): IntSet.t = pt_edge_reach_acc IntSet.empty pte
let pt_edge_block_frag_reach (m: pt_edge Block_frag.t): IntSet.t =
  Block_frag.reach pt_edge_reach_acc m
let ind_args_reach_acc (acc: IntSet.t) (ia: ind_args): IntSet.t =
  let f = List.fold_left (fun a i -> IntSet.add i a) in
  f (f acc ia.ia_ptr) ia.ia_int
let ind_args_reach (ia: ind_args): IntSet.t =
  ind_args_reach_acc IntSet.empty ia
let ind_edge_reach (ie: ind_edge): IntSet.t = ind_args_reach ie.ie_args
let seg_edge_reach (se: seg_edge): IntSet.t =
  ind_args_reach_acc
    (ind_args_reach_acc (IntSet.singleton se.se_dnode) se.se_sargs) se.se_dargs
(* Main reachability function for a node *)
let node_reach (n: node): IntSet.t =
  match n.n_e with
  | Hemp -> IntSet.empty
  | Hpt pt -> pt_edge_block_frag_reach pt
  | Hind ie -> ind_edge_reach ie
  | Hseg se -> seg_edge_reach se


(** Sanity checks *)
let graph_sanity_check (loc: string) (g: graph): unit =
  (* auxilliary functions *)
  let error (s: string): unit =
    Log.fatal_exn "Graph sanity check fails (%s): %s\n%s"
      loc s (graph_2str g) in
  let m_back: IntSet.t IntMap.t ref = ref IntMap.empty in
  let add_backs (pre: int) (posts: IntSet.t): unit =
    IntSet.iter
      (fun post ->
        let o = try IntMap.find post !m_back with Not_found -> IntSet.empty in
        let n = IntSet.add pre o in
        m_back := IntMap.add post n !m_back
      ) posts in
  (* soundness of the key-gen *)
  let nodes = IntMap.fold (fun i _ -> IntSet.add i) g.g_g IntSet.empty in
  Keygen.sanity_check ("graph:"^loc) nodes g.g_nkey;
  (* table of nodes *)
  IntMap.iter
    (fun i n ->
      (* node index should be consistent *)
      if i != n.n_i then error (Printf.sprintf "node name: %d" i);
      (* nodes pointed to should belong to the graph *)
      let r = node_reach n in
      IntSet.iter
        (fun j ->
          if not (IntMap.mem j g.g_g) then
            error (Printf.sprintf "node %d pointed to by %d" j i)
        ) r;
      add_backs i r
    ) g.g_g;
  (* back indexes should be consistent *)
  if Flags.flag_back_index then
    IntMap.iter
      (fun i n ->
        let found_pres =
          try IntMap.find i !m_back with Not_found -> IntSet.empty in
        if not (IntSet.equal found_pres n.n_preds) then
          error (Printf.sprintf "prevs do not mach for node %d" i)
      ) g.g_g;
  (* nodes in g_add should belong to the graph *)
  PMap.iter
    (fun i _ ->
      if not (IntMap.mem i g.g_g) then
        error (Printf.sprintf "g_add; node %d" i)
    ) g.g_svemod.svm_add;
  (* nodes in g_rem should not belong to the graph *)
  PSet.iter
    (fun i ->
      if IntMap.mem i g.g_g then
        error (Printf.sprintf "g_rem; node %d" i)
    ) g.g_svemod.svm_rem


(** Management of back pointers *)
(* addition of a back index *)
let add_bindex (san: bool) (* sanity check after ? *)
    (c: string) (pre: nid) (post: nid) (t: graph): graph =
  if !Flags.flag_debug_back_index then
    Log.force "add_bindex<%s>: %d->%d\n" c pre post;
  let pnode =
    try IntMap.find post t.g_g
    with Not_found ->
      Log.fatal_exn "add_bindex:\n%s\nnf <%s>: %d"
        (graph_2stri "  " t) c post in
  let npnode = { pnode with
                 n_preds = IntSet.add pre pnode.n_preds } in
  let tt = { t with g_g = IntMap.add post npnode t.g_g } in
  if san then
    graph_sanity_check (Printf.sprintf "add_bindex,after<%s>" c) tt;
  tt
let add_bindexes (san: bool) (* sanity check after ? *)
    (c: string) (pre: nid) (posts: IntSet.t) (t: graph): graph =
  let tt = IntSet.fold (add_bindex false c pre) posts t in
  if san then
    graph_sanity_check (Printf.sprintf "add_bindexes,after<%s>" c) tt;
  tt
(* removal of a back index,
 * with a check function, which may inhibit the removal,
 * used for points-to edges modification that may not kill
 * a back index due to multiple occurrences *)
let rem_bindex_chk (f: nid -> bool)
    (san: bool) (* sanity check after ? *)
    (c: string) (* context *)
    (pre: nid)  (post: nid) (t: graph): graph =
  if not (f post) then
    let pnode =
      try IntMap.find post t.g_g
      with Not_found -> Log.fatal_exn "rem_bindex, nf: %d" post in
    if !Flags.flag_debug_back_index then
      Log.force "rem_bindex<%s>: %d->%d" c pre post ;
    let npnode = { pnode with
                   n_preds = IntSet.remove pre pnode.n_preds } in
    let tt = { t with g_g = IntMap.add post npnode t.g_g } in
    if san then
      graph_sanity_check (Printf.sprintf "rem_bindex_chk[%s],after" c) tt;
    tt
  else t
let rem_bindex = rem_bindex_chk (fun _ -> false)
let rem_bindexes san c pre posts t =
  let tt = IntSet.fold (rem_bindex false c pre) posts t in
  if san then
    graph_sanity_check (Printf.sprintf "rem_bindexes[%s],after" c) tt;
  tt
let rem_bindexes_chk f san c pre posts t =
  let tt = IntSet.fold (rem_bindex_chk f false c pre) posts t in
  if san then
    graph_sanity_check (Printf.sprintf "rem_bindexes_chk[%s],after" c) tt;
  tt


(** Number of edges (serves as a weak emptiness test) *)
let num_edges (t: graph): int =
  IntMap.fold
    (fun _ n acc ->
      match n.n_e with
      | Hemp -> acc
      | Hpt cells -> Block_frag.fold_base (fun _ _ -> (+) 1) cells acc
      | Hind _ | Hseg _ -> acc + 1
    ) t.g_g 0


(** Management of SVs *)

(* Node membership *)
let node_mem (id: nid) (t: graph): bool = IntMap.mem id t.g_g
(* Node accessor *)
let node_find (id: nid) (t: graph): node =
  try IntMap.find id t.g_g
  with Not_found ->
    Log.fatal_exn "node_find: node %d not found:\n%s" id (graph_2stri "  " t)
(* Kind of the memory region attached to an SV *)
let sv_kind (i: int) (t: graph): region_kind =
  match (node_find i t).n_e with
  | Hemp   -> Kemp
  | Hpt _  -> Kpt
  | Hind _ -> Kind
  | Hseg _ -> Kseg

(* Addition of a new node with known id (crashes if already exists) *)
let sv_add ?(attr: node_attribute = Attr_none) ?(root: bool = false) (id: nid)
    (nt: ntyp) (na: nalloc) (t: graph): graph =
  assert (not (IntMap.mem id t.g_g));
  assert (not (PSet.mem id t.g_svemod.svm_rem));
  let node_empty = { n_i     = id ;
                     n_t     = nt ;
                     n_e     = Hemp ;
                     n_alloc = na ;
                     n_preds = IntSet.empty ;
                     n_attr  = attr } in
  let svm = { t.g_svemod with svm_add = PMap.add id nt t.g_svemod.svm_add } in
  (* adds a fresh node with known id *)
  { t with
    g_nkey   = Keygen.use_key t.g_nkey id ;
    g_g      = IntMap.add id node_empty t.g_g ;
    g_svemod = svm;
    g_roots  = if root then IntSet.add id t.g_roots else t.g_roots }
(* Addition of a new, fresh node *)
let sv_add_fresh ?(attr: node_attribute = Attr_none) ?(root: bool = false)
    (nt: ntyp) (na: nalloc) (t: graph): nid * graph =
  let _, i = Keygen.gen_key t.g_nkey in
  i, sv_add ~attr:attr ~root:root i nt na t
(* Releasing a root *)
let sv_unroot (id: int) (t: graph): graph =
  if not (IntSet.mem id t.g_roots) then
    Log.fatal_exn "sv_unroot not called on root";
  { t with g_roots = IntSet.remove id t.g_roots }
(* Removal of a node *)
let sv_rem (id: int) (t: graph): graph =
  if IntSet.mem id t.g_roots then Log.fatal_exn "sv_rem called on root node";
  let gadd, grem =
    if PMap.mem id t.g_svemod.svm_add then
      begin
        (* this may happen in the presence of inductive parameters *)
        Log.warn "removing node that was just added";
        PMap.remove id t.g_svemod.svm_add, t.g_svemod.svm_rem
      end
    else t.g_svemod.svm_add, PSet.add id t.g_svemod.svm_rem in
  if not (IntMap.mem id t.g_g) then
    Log.fatal_exn "sv_rem: node %d does not exist" id;
  let posts = node_reach (IntMap.find id t.g_g) in
  let t =
    rem_bindexes false "sv_rem" id posts
      { t with
        g_g      = IntMap.remove id t.g_g ;
        g_svemod = { t.g_svemod with
                     svm_add = gadd;
                     svm_rem = grem } } in
  { t with g_nkey = Keygen.release_key t.g_nkey id }


(** Management of SETVs *)

let setv_add_fresh (root: bool) (ko: set_par_type option) (x: graph)
    : int * graph =
  let kg, setv = Keygen.gen_key x.g_setvkey in
  let x = { x with g_setvkey = kg } in
  let x =
    if root then { x with g_setvroots = IntSet.add setv x.g_setvroots }
    else x in
  let x =
    match ko with
    | None -> x
    | Some k -> { x with g_setvkind = IntMap.add setv k x.g_setvkind } in
  setv, x
let setv_add (root: bool) (setv: int) (x: graph): graph =
  let x =
    if root then { x with g_setvroots = IntSet.add setv x.g_setvroots }
    else x in
  { x with g_setvkey = Keygen.use_key x.g_setvkey setv }

(* generate the guard constraint that an inductive edge being empty *)
let cons_emp_ind (n: int) (ie: ind_edge): n_cons option =
  (* functions that return a node *)
  let fetch_ptr_par (i: int): int =
    try List.nth ie.ie_args.ia_ptr i
    with Failure _ ->
      Log.fatal_exn "emp_ind: ptr par out of range" in
  let fetch_int_par (i: int): int =
    try List.nth ie.ie_args.ia_int i
    with Failure _ ->
      Log.fatal_exn "emp_ind: int par out of range" in
  let map_formal_arith_arg: formal_arith_arg -> int = function
    | `Fa_this      -> n
    | `Fa_var_new i -> Log.fatal_exn "emp_ind: unexpected new var"
    | `Fa_par_int i -> fetch_int_par i
    | `Fa_par_ptr i -> fetch_ptr_par i in
  (* compute predicates *)
  let rec map_aexpr (ae: aexpr) : n_expr =
    match ae with
    | Ae_cst i -> Ne_csti i
    | Ae_var fa -> Ne_var (map_formal_arith_arg fa)
    | Ae_plus (_, _) -> Log.fatal_exn "emp_ind: unexpected expression" in
  match Ind_utils.emp_rule_cons ie.ie_ind with
  | None -> None
  | Some af ->
      match af with
      | Af_equal (Ae_var `Fa_this, re) ->
          Some (Nc_cons (Apron.Tcons1.EQ, Ne_var n, map_aexpr re))
      | _ -> None


(** Generation of set parameters to build an inductive predicate *)
let build_set_args (nset: int) (g: graph): graph * nid list =
  let rec f i g sargs =
    if i = 0 then g, sargs
    else
      let arg, g = setv_add_fresh false None g in
      f (i - 1) g (arg :: sargs) in
  f nset g []


(* merge two integer weaken type *)
let merge_wktype (wkl: int_wk_typ) (wkr: int_wk_typ):int_wk_typ =
  if wkl = wkr then wkl
  else
    match wkl, wkr with
    | `Leq, `Geq |  `Geq, `Leq  ->  `Eq
    | _, _ -> Log.fatal_exn "double type for a node"

(* convert types from inductive edge to segment end point *)
let seg_end_wkt (int_typ: int_wk_typ IntMap.t): int_wk_typ IntMap.t =
  IntMap.map
    (function
      | `Leq -> `Geq
      | `Geq -> `Leq
      | wk -> wk
    ) int_typ

(* type a list of integer parameters *)
let type_iargs_ie (ie: ind_args) (int_typ: int_wk_typ IntMap.t)
    (acc: int_wk_typ IntMap.t) =
  let do_i_type (n: int) (acc: int_wk_typ IntMap.t) (wk: int_wk_typ)
      : int_wk_typ IntMap.t =
    try IntMap.add n (merge_wktype (IntMap.find n acc) wk) acc
    with Not_found -> IntMap.add n wk acc in
  let _, acc =
    List.fold_left
      (fun (index, acc) n ->
        let wk = IntMap.find index int_typ in
        index+1, do_i_type n acc wk
      ) (0, acc) ie.ia_int in
  acc

(* compute weaken type for integer parameters in a graph *)
let type_iargs_g (g: graph) (f_rel: int -> int): int_wk_typ IntMap.t =
  IntMap.fold
    (fun key node acc->
      match node.n_e with
      | Hemp
      | Hpt _ -> acc
      | Hind ie ->
          let int_wk_typ = ie.ie_ind.i_pars_wktyp.int_typ in
          type_iargs_ie ie.ie_args int_wk_typ acc
      | Hseg se ->
          let sal = f_rel key in
          let dal = f_rel se.se_dnode in
          let sint_wk_typ = se.se_ind.i_pars_wktyp.int_typ in
          let dint_wk_typ = seg_end_wkt se.se_ind.i_pars_wktyp.int_typ in
          if sal = dal then
            type_iargs_ie se.se_sargs sint_wk_typ acc
          else
            type_iargs_ie se.se_dargs dint_wk_typ
              (type_iargs_ie se.se_sargs sint_wk_typ acc)
    ) g.g_g IntMap.empty

(* choose the integer parameters weaken type *)
let compute_wk_type (is: int) (ind: ind_edge) (sat: n_cons -> bool)
    : pars_wk_typ =
  match cons_emp_ind is ind with
  | None -> ind.ie_ind.i_pars_wktyp
  | Some ctr ->
      if sat ctr then ind.ie_ind.i_emp_pars_wktyp
      else ind.ie_ind.i_pars_wktyp

(* Checks whether a node is the root of an inductive *)
let node_is_ind (n: int) (g: graph): bool =
  match (node_find n g).n_e with
  | Hemp | Hpt _ -> false
  | Hind _ | Hseg _ -> true
(* get name of ind. def. attached to that node if any, None else *)
let ind_of_node (n: node): string option =
  match n.n_attr with
  | Attr_ind ind_name -> Some ind_name
  | Attr_array _ | Attr_none -> None
(* Checks whether a node has points-to edges *)
let node_is_pt (n: int) (g: graph): bool =
  match (node_find n g).n_e with
  | Hpt m -> not (Block_frag.is_empty m)
  | Hemp | Hind _ | Hseg _ -> false
(* Checks whether a node is placed in memory *)
let node_is_placed (n: node): bool =
  match n.n_alloc with
  | Nheap _ | Nstack | Nstatic | Nsubmem -> true
  | Nnone -> false
(* Asserts the node must be placed; crashes otherwise *)
let node_assert_placed (ctx: string) (n: node): unit =
  if not (node_is_placed n) then
    Log.fatal_exn "%s: node is not placed" ctx
(* Assume a node is placed
 * (when its value is discovered to be a valid address; used for sub-mem) *)
let node_assume_placed (i: int) (g: graph): graph =
  let n = node_find i g in
  let n = { n with
            n_alloc  = Nheap (Some Flags.abi_ptr_size) ;
            n_t      = Ntaddr } in
  { g with g_g = IntMap.add i n g.g_g }


(* Returns the set of all nodes *)
let get_all_nodes (g: graph): IntSet.t =
  IntMap.fold (fun i _ acc -> IntSet.add i acc) g.g_g IntSet.empty
(* Returns the predecessors of a node *)
let get_predecessors_of_node (n: int) (g: graph): IntSet.t =
  (node_find n g).n_preds
(* Collect offsets from a base address *)
let collect_offsets (pre: int) (g: graph) (acc: OffSet.t): OffSet.t =
  match (node_find pre g).n_e with
  | Hpt mc ->
      Block_frag.fold_base
        (fun _ pe acc -> OffSet.add (snd pe.pe_dest) acc) mc acc
  | _ -> acc

(** Points-to edges operations *)
(* Existence of a points-to edge *)
let pt_edge_mem ((is,os): onode) (t: graph): bool =
  let nsrc = node_find is t in
  match nsrc.n_e with
  | Hemp | Hind _ | Hseg _ -> false
  | Hpt mc -> Block_frag.mem (Bounds.of_offs os) mc
(* Creation of a block points to edge *)
let pt_edge_block_create (is: nid) (pe: pt_edge) (t: graph): graph =
  let nsrc = node_find is t in
  node_assert_placed "pt_edge_block_create" nsrc;
  let block =
    match nsrc.n_e with
    | Hemp ->
        let bnd_lo = Bounds.zero
        and bnd_hi = Bounds.add_size Bounds.zero pe.pe_size in
        Block_frag.create_block_span bnd_lo bnd_hi pe
    | _ -> Log.fatal_exn "pt_edge_block_create: improper edge" in
  let nsrc = { nsrc with n_e = Hpt block } in
  (* Fixing the back indexes *)
  let btargets = pt_edge_reach pe in
  add_bindexes true "pt_edge_block_create" is btargets
    { t with g_g = IntMap.add is nsrc t.g_g }
(* Appends a field at the end of a block *)
let pt_edge_block_append
    ?(nochk: bool = false) (* de-activates check that bounds coincide (join) *)
    ((is, bnd): bnode) (pe: pt_edge) (t: graph): graph =
  let nsrc = node_find is t in
  node_assert_placed "pt_edge_block_append" nsrc;
  let oblock =
    match nsrc.n_e with
    | Hemp -> Block_frag.create_empty bnd
    | Hpt block -> block
    | _ -> Log.fatal_exn "pt_edge_block_append: improper edge" in
  let nblock =
    Block_frag.append_tail ~nochk: nochk bnd
      (Bounds.add_size bnd pe.pe_size) pe oblock in
  let nsrc = { nsrc with n_e = Hpt nblock } in
  (* Fixing the back indexes *)
  let btargets = Bounds.t_sym_var_ids_add (pt_edge_reach pe) bnd in
  add_bindexes true "pt_edge_block_append" is btargets
    { t with g_g = IntMap.add is nsrc t.g_g }

(* Removal of a bunch of points-to edges from a node *)
let pt_edge_block_destroy (is: nid) (t: graph): graph =
  let n = node_find is t in
  match n.n_e with
  | Hpt _ ->
      let nn = { n with n_e = Hemp } in
      let posts = node_reach n in
      rem_bindexes false "pt_edge_block_destroy" is posts
        { t with g_g = IntMap.add is nn t.g_g }
   | _ -> Log.fatal_exn "pt_edge_block_destroy: not a points-to edge"

(* Finding a pt_edge, for internal use (no size used, so cannot be used to
 *  dereference an edge) *)
let pt_edge_find
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,os): onode) (t: graph): pt_edge =
  let nsrc = node_find is t in
  let bnd = Bounds.of_offs os in
  if nsrc.n_t != Ntaddr then
    Log.warn "Issue in pt_edge_find; type of src is %s\n"
      (ntyp_2str nsrc.n_t);
  match nsrc.n_e with
  | Hemp | Hind _ | Hseg _ -> Log.fatal_exn "pt_edge_find: does not exist (1)"
  | Hpt mc ->
      try Block_frag.find_addr_sat sat bnd mc
      with Not_found -> Log.fatal_exn "pt_edge_find: does not exist (2)"

(* Try to decide if an offset range is in a single points-to edge
 *  of a fragmentation, and if so, return its destination *)
let pt_edge_find_interval
    (sat: n_cons -> bool)
    (is: nid) (* node representing the base address *)
    (min_off: Offs.t) (* minimum offset of the range being looked for *)
    (size: int)       (* size of the range being looked for *)
    (t: graph): pt_edge option =
  match (node_find is t).n_e with
  | Hemp | Hind _ | Hseg _ -> None
  | Hpt mc ->
      let bnd_low = Bounds.of_offs min_off in
      let bnd_hi  = Bounds.of_offs (Offs.add_int min_off size) in
      try Some (Block_frag.find_chunk_sat sat bnd_low bnd_hi mc)
      with Not_found -> None

(* Splitting of a points-to edge *)
exception Retry of graph
let pt_edge_split
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,os): bnode) (mid_point: Offs.size) (t: graph): graph =
  if false then
    Log.debug "call to pt_edge_split\n - %s\n - %s\n"
      (Bounds.t_2str os) (Offs.size_2str mid_point);
  let old_pt = pt_edge_find sat (is, Bounds.to_offs os) t in
  assert (Offs.size_leq sat mid_point old_pt.pe_size);
  let sv_old_dest = fst old_pt.pe_dest in
  let old_src = node_find sv_old_dest t in
  let sz0 = mid_point
  and sz1 = Offs.size_sub_size old_pt.pe_size mid_point in
  let typ0, typ1 =
    match old_src.n_t with
    | Ntraw | Ntint -> Log.warn "imprecise split"; Ntraw, Ntraw
    | Ntaddr -> Ntraw, Ntraw
    | Ntset -> Log.fatal_exn "cannot split a set node" in
  let n0, t = sv_add_fresh typ0 old_src.n_alloc t in
  let n1, t = sv_add_fresh typ1 old_src.n_alloc t in
  let pe_0 = { pe_size = sz0 ; pe_dest = n0, Offs.zero }
  and pe_1 = { pe_size = sz1 ; pe_dest = n1, Offs.zero } in
  let nsrc = node_find is t in
  node_assert_placed "pt_edge_split" nsrc;
  let bndmid = Bounds.add_size os mid_point in
  let bndhi = Bounds.add_size os old_pt.pe_size in
  if false then
    Log.debug "PT_SPLIT:\n - pos %s\n - siz %s\n - res %s\n"
      (Bounds.t_2str os) (Offs.size_2str old_pt.pe_size) (Bounds.t_2str bndhi);
  let nblock =
    let oblock =
      match nsrc.n_e with
      | Hemp -> Block_frag.create_empty os
      | Hpt block -> block
      | _ -> Log.fatal_exn "pt_edge_split: improper edge" in
    Block_frag.split_sat sat os bndmid bndhi pe_0 pe_1 oblock in
  let nsrc = { nsrc with n_e = Hpt nblock } in
  let f_post_check (i: nid): bool =
    Block_frag.fold_base
      (fun _ pe acc -> acc || fst pe.pe_dest = i) nblock false in
  (* Fixing of the back indexes *)
  let btargets =
    IntSet.add n0 (Bounds.t_sym_var_ids_add (IntSet.singleton n1) bndmid) in
  add_bindexes true "pt_edge_split" is btargets
    (rem_bindex_chk f_post_check false "pt_edge_split" is
       sv_old_dest { t with g_g = IntMap.add is nsrc t.g_g })

(* Experimental algorithm for edge search *)
let pt_edge_search
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    (mc: pt_edge Block_frag.t) (bnd: Bounds.t) (sz: Offs.size)
    : (Bounds.t * Offs.size) option =
  Block_frag.fold_base
    (fun os pe acc ->
      (* inclusion in the left bound *)
      let b_incl_l = Bounds.leq sat os bnd in
      (* inclusion in the right bound *)
      let b_incl_r =
        Bounds.leq sat
          (Bounds.add_size bnd sz) (Bounds.add_size os pe.pe_size) in
      match acc, b_incl_l && b_incl_r with
      | None, true -> Some (os, Bounds.sub bnd os)
      | _, false -> acc
      | Some _, true -> Log.fatal_exn "separation violation"
    ) mc None

(* Retrieval algorithm that encapsulates the search for extract and replace *)
let pt_edge_retrieve
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,bnd): bnode) (mc: pt_edge Block_frag.t) (old_sz: Offs.size)
    (t: graph): pt_edge =
  try Block_frag.find_addr_sat sat bnd mc
  with
  | Not_found ->
      (* Search for an edge containing the one being searched for *)
      match pt_edge_search sat mc bnd old_sz with
      | Some (fo, fsz) ->
          let nt = pt_edge_split sat (is,fo) fsz t in
          raise (Retry nt)
      | None -> raise (No_edge
                         (Printf.sprintf "nf in pt_edge_retrieve (off): %s"
                            (Bounds.t_2str bnd)))

(* Retrieval algorithm that encapsulates the search for extract and replace *)
let pt_edge_localize_in_graph
    (sat: n_cons -> bool)
    ((i,o): onode) (size: int) (t: graph): pt_edge option =
  let n = node_find i t in
  match n.n_e with
  | Hpt mc ->
      begin
        let b_min = Bounds.of_offs o in
        let b_max = Bounds.add_int b_min size in
        Log.info "\tfound node, searching bound[%d] %s -> %s\n"
          i (Bounds.t_2str b_min) (Bounds.t_2str b_max);
        try Some (Block_frag.find_chunk_sat sat b_min b_max mc)
        with Not_found -> None
      end
  | _ -> None

(* Treating the case of Hemp in pt_edge_replace and pt_edge_extract
 * by searching for an opportunity for backward unfolding *)
let pt_edge_localize_in_empty (n: node) (is: nid) (t: graph) =
  (* experimental code to see whether there is an opportunity for
   * backward unfolding:
   *  - check the prevs of "is"
   *  - see if there is a segment where "is" is a back parameter
   *)
  (* HS, possible improvement:
   *   extend the search to other nodes, that are equal to another node,
   *   that would support backward unfolding
   *   (most likely at the call point of this function) *)
  let candidates =
    IntSet.fold
      (fun i acc ->
        let ni = node_find i t in
        match ni.n_e with
        | Hemp | Hpt _ | Hind _ -> acc
        | Hseg se ->
            let _, acc =
              List.fold_left
                (fun (k, acc) a ->
                  let b_par = IntSet.mem k se.se_ind.i_pr_pars in
                  if a = is && b_par then
                    k + 1, IntSet.add i acc
                  else k + 1, acc
                ) (0, acc) se.se_dargs.ia_ptr in
            acc
      ) n.n_preds IntSet.empty in
  let card = IntSet.cardinal candidates in
  if card = 1 then
    let candidate = IntSet.min_elt candidates in
    raise (Unfold_request (Uloc_main candidate, Udir_bwd))
  else
    begin
      Log.info "pt_edge_localize_in_empty (%d) [%d]:\n%s" is card
        (graph_2stri "  " t);
      raise (No_edge "pt_edge_localize_in_empty failed")
    end

(* Extend the search to other nodes, that are equal to another node *)
let pt_edge_localize_in_equal (sat: n_cons -> bool)
    ((is, os): onode) (t: graph): PairSet.t =
  IntMap.fold
    (fun key knode acc ->
      match knode.n_e with
      | Hpt mc ->
          if sat (Nc_cons (Apron.Tcons1.EQ, Ne_var key, Ne_var is)) then
            PairSet.add (key, is) acc
          else acc
      | _ -> acc
    ) t.g_g PairSet.empty

(* Replacement of a points-to edge by another *)
let pt_edge_replace
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,os): onode) (pte: pt_edge): graph -> graph =
  let bnd = Bounds.of_offs os in
  let rec aux (t: graph): graph =
    let n = node_find is t in
    if !flag_debug_graph_blocks then
      Log.force "Call to pt_edge_replace.aux:\n before: %s after:    %s\n"
        (heap_frag_2stri "  " is n.n_e) (pt_edge_2str (is,bnd) pte);
    match n.n_e with
    | Hemp ->
        (* Look for an opportunity to do backward unfolding *)
        pt_edge_localize_in_empty n is t
    | Hpt mc ->
        begin
          try
            let old_pe = pt_edge_retrieve sat (is,bnd) mc pte.pe_size t in
            if !flag_debug_graph_blocks then
              Log.force "Comparing sizes:\n - %s\n - %s\n"
                (Offs.size_2str pte.pe_size) (Offs.size_2str old_pe.pe_size);
            match Offs.size_order sat pte.pe_size old_pe.pe_size with
            | Some c ->
                if c = 0 then (* pte.pe_size = old_pe.pe_size *)
                  (* the edges found matches exactly the region to overwrite *)
                  let nmc = Block_frag.replace_sat sat bnd pte mc in
                  let nn = { n with n_e = Hpt nmc } in
                  let f_post_check (i: nid): bool =
                    Block_frag.fold_base
                      (fun _ pe acc -> acc || fst pe.pe_dest = i) nmc false in
                  let tt =
                    add_bindexes true "pt_edge_replace" is (pt_edge_reach pte)
                      (rem_bindexes_chk f_post_check false "pt_edge_replace"
                         is (pt_edge_reach old_pe)
                         { t with g_g = IntMap.add is nn t.g_g })
                  in
                  graph_sanity_check "pt_edge_replace" tt;
                  tt
                else if c < 0 then (* pte.pe_size < old_pe.pe_size then*)
                  (* only part of the edge needs be overwritten;
                   * we should split it *)
                  aux (pt_edge_split sat (is,bnd) pte.pe_size t)
                else (* c > 0, i.e., pte.pe_size > old_pe.pe_size *)
                  (* we would have to merging edges together... *)
                  Log.fatal_exn "pt_edge_replace: edges merging unsupported"
            | None ->
                if Offs.size_leq sat pte.pe_size old_pe.pe_size then
                  aux (pt_edge_split sat (is,bnd) pte.pe_size t)
                else Log.fatal_exn "incomparable sizes"
          with
          | Retry nt -> aux nt
        end
    | Hind _ ->
        if !flag_debug_trigger_unfold then
          Log.force "pt_edge_replace: inductive found, to unfold!\n";
        raise (Unfold_request (Uloc_main is, Udir_fwd))
    | Hseg _ ->
        if !flag_debug_trigger_unfold then
          Log.force "pt_edge_replace: segment found, to unfold!\n";
        raise (Unfold_request (Uloc_main is, Udir_fwd)) in
  aux

(* Extracts a points-to edge: reads, after split if necessary *)
let pt_edge_extract
    (sat: n_cons -> bool) (* checking of integer satisfiability constraints *)
    ((is,os): onode) (isz: int): graph -> graph * pt_edge =
  let bnd = Bounds.of_offs os in
  let sz = Offs.size_of_int isz in
  let rec aux (t: graph): graph * pt_edge =
    let n = node_find is t in
    if !flag_debug_graph_blocks && false then
      Log.force "Call to pt_edge_extract.aux:  (%d,%s)\n"
        is (Offs.t_2str os);
    let pt_extract mc =
      try
        let pte = pt_edge_retrieve sat (is,bnd) mc sz t in
        match Offs.size_order sat pte.pe_size sz with
        | Some c ->
            if c = 0 then (* equality, pte.pe_size = sz *)
              (* the edge found matches the size of the deref cell *)
              t, pte
            else if c > 0 then (* pte.pe_size > sz *)
              (* only part of the edge should be read; we should split *)
              aux (pt_edge_split sat (is,bnd) sz t)
            else (* c < 0, i.e., pte.pe_size < sz *)
              raise (No_edge "size mismatch")
        | None -> raise (No_edge "incomparable sizes")
      with
      | Retry nt ->
          aux nt in
    match n.n_e with
    | Hemp ->
        (* Look for an opportunity to do backward unfolding *)
        pt_edge_localize_in_empty n is t
    | Hpt mc ->
      pt_extract mc
    | Hind _ ->
        if !flag_debug_trigger_unfold then
          Log.force "pt_edge_extract: inductive found, to unfold!\n";
        raise (Unfold_request (Uloc_main is, Udir_fwd))
    | Hseg _ ->
        if !flag_debug_trigger_unfold then
          Log.force "pt_edge_extract: segment found, to unfold!\n";
        raise (Unfold_request (Uloc_main is, Udir_fwd)) in
  aux


(** Inductive parameters applications *)
(* Empty set of arguments *)
let ind_args_empty: ind_args =
  { ia_ptr = [ ] ;
    ia_int = [ ];
    ia_set = [ ]; }
(* Making lists of arguments *)
let rec ind_args_1_make (typ: ntyp) (i: int) (t: graph): nid list * graph =
  if i = 0 then [ ], t
  else
    let l0, t0 = ind_args_1_make typ (i-1) t in
    let i1, t1 = sv_add_fresh typ Nnone t0 in
    i1 :: l0, t1
(* Making lists of set arguments *)
let rec ind_sargs_make (i: int) (t: graph): nid list * graph =
  if i = 0 then [ ], t
  else
    let l0, t0 = ind_sargs_make (i-1) t in
    let i1, t1 = setv_add_fresh false None t0 in
    i1 :: l0, t1

(* Make a new inductive edge with fresh arg nodes *)
let ind_edge_make (iname: string) (lptr: nid list) (nipars: int)
    (spars: int) (t: graph)
    : ind_edge * graph =
  let lint, g1 = ind_args_1_make Ntint nipars t in
  let lset, g1 = ind_sargs_make spars g1 in
  { ie_ind  = Ind_utils.ind_find iname ;
    ie_args = { ia_ptr = lptr ;
                ia_int = lint;
                ia_set = lset; } },
  g1

(* Make a new segment edge with fresh arg nodes *)
let seg_edge_make (iname: string) (lptr: nid list) (dptr: nid list)
    (nipars: int) (spars: int) (idr: int) (t: graph)
    : seg_edge * graph =
  let lint, g1 = ind_args_1_make Ntint nipars t in
  let lset, g1 = ind_sargs_make spars g1 in
  let dint, g1 = ind_args_1_make Ntint nipars g1 in
  let dset, g1 = ind_sargs_make spars g1 in
  { se_ind  = Ind_utils.ind_find iname ;
    se_sargs = { ia_ptr = lptr ;
                 ia_int = lint ;
                 ia_set = lset } ;
    se_dargs = { ia_ptr = dptr ;
                 ia_int = dint ;
                 ia_set = dset } ;
    se_dnode = idr; },
  g1

(** Operations common to inductive and segment edges *)
let ind_seg_pre_add_check (n: node): unit =
  (* checks: source node should be an address, with no memory materialized
   *  -> we want to fix these eventually *)
  if n.n_t != Ntaddr then
    Log.info"ind_edge_add: node may not be an address";
  if n.n_alloc != Nnone then
    Log.info
      "ind_edge_add: possible double representation of allocation node %d"
      n.n_i

(** Inductive edges operations *)
(* Retrieve an inductive edge *)
(* Note: this function seems unused now... *)
let ind_edge_find (is: nid) (t: graph): ind_edge =
  let nsrc =
    try IntMap.find is t.g_g
    with Not_found -> Log.fatal_exn "nf in ind_edge_find (src)" in
  match nsrc.n_e with
  | Hind ie -> ie
  | _ -> Log.fatal_exn "ind_edge_find: no ind edge!"
(* Inductive edge addition *)
let ind_edge_add (is: nid) (ie: ind_edge) (t: graph): graph =
  (* enforcing consistency with the inductive *)
  if List.length ie.ie_args.ia_ptr != ie.ie_ind.i_ppars then
    Log.fatal_exn "ind_edge_add, ptr args (%s): %d-%d" ie.ie_ind.i_name
      (List.length ie.ie_args.ia_ptr) (ie.ie_ind.i_ppars);
  if List.length ie.ie_args.ia_int != ie.ie_ind.i_ipars then
    Log.fatal_exn "ind_edge_add, int args (%s): %d-%d" ie.ie_ind.i_name
      (List.length ie.ie_args.ia_int) (ie.ie_ind.i_ipars);
  if List.length ie.ie_args.ia_set != ie.ie_ind.i_spars then
    Log.fatal_exn "ind_edge_add, set args (%s): %d-%d" ie.ie_ind.i_name
      (List.length ie.ie_args.ia_set) (ie.ie_ind.i_spars);
  let iname = ie.ie_ind.i_name in
  if not (StringSet.mem iname t.g_inds) then
    Log.fatal_exn "seg_add: inductive %s not in graph" iname;
  (* source node retrieval *)
  let nsrc =
    try IntMap.find is t.g_g
    with Not_found -> Log.fatal_exn "nf in ind_edge_add (src)" in
  ind_seg_pre_add_check nsrc;
  (* addition of the edge *)
  match nsrc.n_e with
  | Hemp ->
      let nsrc1 =
        { nsrc with
          n_e    = Hind ie ;
          n_attr = Attr_ind ie.ie_ind.i_name } in
      let reach = ind_edge_reach ie in
      add_bindexes true "ind_edge_add" is reach
        { t with g_g = IntMap.add is nsrc1 t.g_g }
  | Hpt _ | Hind _ | Hseg _ ->
      Log.fatal_exn "ind_edge_add: there is already an edge"
let ind_edge_rem (is: nid) (t: graph): graph =
  let n = node_find is t in
  match n.n_e with
  | Hind ie ->
      (* argument nodes appear only on that inductive edge;
       * therefore, they should all be removed now *)
      let reach = ind_edge_reach ie in
      let nn = { n with
                 n_e = Hemp } in
      let t0 =
        rem_bindexes true "ind_edge_rem" is reach
          { t with g_g   = IntMap.add is nn t.g_g  } in
      t0
  | _ -> Log.fatal_exn "cannot find a semgent edge to remove"
(* Function extracting *one* *inductive* edge (for is_le) *)
let ind_edge_extract_single (g: graph): bool * (int * ind_edge) option =
  let found: (int * ind_edge) option ref = ref None (* inductive edge found *)
  and several = ref false in
  IntMap.iter
    (fun i e ->
      match e.n_e with
      | Hemp -> ( )
      | Hpt _ | Hseg _ -> several := true
      | Hind ie ->
          assert (List.length ie.ie_args.ia_int = 0);
          match !found with
          | None   -> found := Some (i, ie)
          | Some _ -> several := true
    ) g.g_g ;
  !several, !found


(** Segment edges operations *)
(* Retrieve an inductive edge *)
let seg_edge_find (is: nid) (t: graph): seg_edge =
  let nsrc =
    try IntMap.find is t.g_g
    with Not_found -> Log.fatal_exn "nf in seg_edge_find (src)" in
  match nsrc.n_e with
  | Hseg se -> se
  | _ -> Log.fatal_exn "seg_edge_find: no segment edge!"
(* Addition of a segment edge *)
let seg_edge_add
    (is: nid)
    (seg: seg_edge)
    (g: graph): graph =
  let n = node_find is g in
  ind_seg_pre_add_check n;
  let iname = seg.se_ind.i_name in
  if not (StringSet.mem iname g.g_inds) then
    Log.fatal_exn "seg_add: inductive %s not in graph" iname;
  match n.n_e with
  | Hemp ->
      let nn = { n with
                 n_e = Hseg seg } in
      let reach = seg_edge_reach seg in
      add_bindexes true "seg_edge_add" is reach
        { g with g_g = IntMap.add is nn g.g_g }
  | _ -> Log.fatal_exn "cannot add a segment over existing edge"
(* Removal of a segment edge *)
let seg_edge_rem (is: nid) (t: graph): graph =
  let n = node_find is t in
  match n.n_e with
  | Hseg se ->
      let nn = { n with n_e = Hemp } in
      let reach = seg_edge_reach se in
      rem_bindexes true "seg_edge_rem" is reach
        { t with g_g = IntMap.add is nn t.g_g }
  | _ -> Log.fatal_exn "cannot find a semgent edge to remove"
(* find sources of segments to some given node *)
let seg_edge_find_to (is: nid) (t: graph): IntSet.t =
  let n = node_find is t in
  IntSet.fold
    (fun ispred acc ->
      let npred = node_find ispred t in
      match npred.n_e with
      | Hseg se -> if se.se_dnode = is then IntSet.add ispred acc else acc
      | _ -> acc
    ) n.n_preds IntSet.empty


(** Inductives and segments *)
(* Extraction of an inductive or segment edge *)
let ind_or_seg_edge_find_rem (is: nid) (t: graph)
    : ind_edge                (* inductive edge (at the source) *)
    * (nid * ind_args) option (* destination if segment         *)
    * graph                   (* remaining graph                *) =
  let n =
    try IntMap.find is t.g_g
    with Not_found -> Log.fatal_exn "nf in ind_or_seg_edge_find_rem" in
  let t_rem = { t with g_g = IntMap.add is { n with n_e = Hemp } t.g_g } in
  let error (msg: string) =
    Log.fatal_exn "ind_or_seg_edge_find_rem: not found: %s at %d\n%s"
      msg is (graph_2stri "  " t) in
  match n.n_e with
  | Hemp -> error "empty"
  | Hpt _ -> error "points-to"
  | Hind ie ->
      let reach = ind_edge_reach ie in
      ie, None, rem_bindexes true "ind_or_seg_edge_find_rem" is reach t_rem
  | Hseg se ->
      let reach = seg_edge_reach se in
      { ie_ind  = Ind_utils.ind_find se.se_ind.i_name ;
        ie_args = se.se_sargs },
      Some (se.se_dnode, se.se_dargs),
      rem_bindexes true "ind_or_seg_find_rem" is reach t_rem
(* Asserting that some inductives have no parameters of a certain kind
 * (useful for weakening rules that do not support parameters yet) *)
let assert_no_ptr_arg (msg: string) (a: ind_args): unit =
  if List.length a.ia_ptr != 0 then
    Log.fatal_exn "rule no ptr arg violation: %s" msg
let assert_no_int_arg (msg: string) (a: ind_args): unit =
  if List.length a.ia_int != 0 then
    Log.fatal_exn "rule no int arg violation: %s" msg
let assert_no_arg (msg: string) (a: ind_args): unit =
  assert_no_ptr_arg msg a;
  assert_no_int_arg msg a


(** Functions for all kinds of edges *)
(* Removal of all edges at a node *)
let edge_rem_any (is: nid) (t: graph): graph =
  let n = node_find is t in
  match n.n_e with
  | Hemp -> t
  | Hpt _ -> pt_edge_block_destroy is t
  | Hind _ -> ind_edge_rem is t
  | Hseg _ -> seg_edge_rem is t


(** Memory management *)
(* Allocation and free of a memory block *)
let mark_alloc (id: nid) (sz: int) (t: graph): graph =
  let n = node_find id t in
  begin
    match n.n_alloc with
    | Nnone -> ( )   (* ok! *)
    | Nsubmem -> ( ) (* no notion of alloc *)
    | Nstack | Nstatic | Nheap _ as old_a ->
        (* Means the node already considered allocated;
         *  probably due to constraints that a node is allocated remain
         *  although a segment has been folded from those nodes *)
        Log.info "node was already known to be allocated %d %s"
          id (nalloc_2str old_a);
        let osz =
          match old_a with
          | Nheap (Some k) -> k
          | a -> Log.fatal_exn "with alloc: %s" (nalloc_2str a) in
        assert (osz = sz)
    end;
  let nn = { n with n_alloc = Nheap (Some sz) } in
  { t with g_g = IntMap.add id nn t.g_g }
let mark_free (id: nid) (t: graph): graph =
  let n = node_find id t in
  match n.n_alloc with
  | Nheap _ ->
      let nn = { n with n_alloc = Nnone } in
      { t with g_g = IntMap.add id nn t.g_g }
  | _ -> Log.fatal_exn "cannot free not allocated node"


(** Tests that can be (partly) evaluated in the graphs *)
(* Equalities generated by the knowledge a segment be empty *)
let empty_segment_equalities (nbase: int) (se: seg_edge): PairSet.t * PairSet.t =
  assert (List.length se.se_sargs.ia_ptr = List.length se.se_dargs.ia_ptr);
  assert (List.length se.se_sargs.ia_int = List.length se.se_dargs.ia_int);
  let f_pair (src: nid) (dst: nid): PairSet.t =
    PairSet.singleton (src, dst) in
  let f_pairs: PairSet.t -> nid list -> nid list -> PairSet.t =
    List.fold_left2 (fun acc src dst -> PairSet.add (src, dst) acc) in
  f_pairs (f_pairs (f_pair nbase se.se_dnode)
             se.se_sargs.ia_ptr se.se_dargs.ia_ptr)
    se.se_sargs.ia_int se.se_dargs.ia_int,
  f_pairs PairSet.empty  se.se_sargs.ia_set se.se_dargs.ia_set
(* Reduction of a segment known to be empty *)
let red_empty_segment (nbase: nid) (g: graph): graph * PairSet.t =
  let se = seg_edge_find nbase g in
  let eqs, seqs = empty_segment_equalities nbase se in
  seg_edge_rem nbase g, eqs (* HS, todo: set parameters *)
(* Graph renaming, for the reduction *)
let graph_rename_ids (renaming: int IntMap.t) (g: graph): graph =
  assert (g.g_svemod = Dom_utils.svenv_empty);
  IntSet.iter (fun i -> assert (not (IntMap.mem i renaming))) g.g_roots;
  let do_nid (i: nid): nid = try IntMap.find i renaming with Not_found -> i in
  let do_ind_args (ia: ind_args): ind_args =
    { ia with
      ia_ptr = List.map do_nid ia.ia_ptr;
      ia_int = List.map do_nid ia.ia_int } in
  let do_pt_edge (pe: pt_edge): pt_edge =
    { pe with
      pe_dest = do_nid (fst pe.pe_dest), snd pe.pe_dest } in
  let do_heap_frag: heap_frag -> heap_frag = function
    | Hemp -> Hemp
    | Hpt m -> Hpt (Block_frag.map_bound (fun x -> x) do_pt_edge m)
    | Hind ie -> Hind { ie with
                        ie_args = do_ind_args ie.ie_args }
    | Hseg se -> Hseg { se with
                        se_sargs = do_ind_args se.se_sargs;
                        se_dargs = do_ind_args se.se_dargs;
                        se_dnode = do_nid se.se_dnode } in
  let do_preds (s: IntSet.t) =
    IntSet.fold (fun i -> IntSet.add (do_nid i)) s IntSet.empty in
  let do_node (n: node): node =
    { n with
      n_e     = do_heap_frag n.n_e;
      n_preds = do_preds n.n_preds } in
  if renaming = IntMap.empty then g
  else
    let nodes = IntMap.map do_node g.g_g in
    IntMap.fold
      (fun irem ikeep acc ->
        let nkeep = node_find ikeep acc in
        let nrem = node_find irem acc in
        let nkeep =
          { nkeep with n_preds = IntSet.union nkeep.n_preds nrem.n_preds } in
        { acc with g_g = IntMap.add ikeep nkeep acc.g_g }
      ) renaming { g with g_g = nodes }
(* Reduction: merging nodes that denote the same concrete value *)
let graph_merge_eq_nodes
    (sat: n_cons -> bool)
    (eqreds: PairSet.t) (g: graph): graph * int IntMap.t =
  (* filtering eqpreds: removing diagonal elements
   * (those equalities trivially hold) *)
  let eqreds =
    PairSet.fold
      (fun (i0,i1) acc -> if i0 = i1 then acc else PairSet.add (i0,i1) acc)
      eqreds PairSet.empty in
  (* a non optimized union find structure (no incremental compression) *)
  let extract (i: int) (uf: int IntMap.t): int =
    let rec aux i = try aux (IntMap.find i uf) with Not_found -> i in
    aux i in
  let fusion (cmp: int -> int -> int) (i0: int) (i1: int) (uf: int IntMap.t) =
    let i0 = extract i0 uf in
    let i1 = extract i1 uf in
    let c = cmp i0 i1 in
    if c = 0 then
      Log.fatal_exn "graph_merge_eq_nodes: equality case should not occur"
    else if c < 0 then IntMap.add i1 i0 uf
    else IntMap.add i0 i1 uf in
  let compress (uf: int IntMap.t): int IntMap.t =
    IntMap.fold
      (fun i j acc -> IntMap.add i (extract j acc) acc) uf IntMap.empty in
  (* temporary reference *)
  let g = ref g in
  (* Condition testing (locally) *)
  let is_null (i: int): bool =
    sat (Nc_cons (Apron.Tcons1.EQ, Ne_var i, Ne_csti 0)) in
  let is_non_null (i: int): bool =
    sat (Nc_cons (Apron.Tcons1.DISEQ, Ne_var i, Ne_csti 0)) in
  (* keep is greater *)
  let compare (i0: int) (i1: int): int =
    match (node_find i0 !g).n_e, (node_find i1 !g).n_e with
    | Hemp, Hemp -> (* if i0 < i1 then i0, i1 else i1, i0 *) i0 - i1
    | Hemp, _ -> 1  (* i1, i0 *)
    | _, Hemp -> -1 (* i0, i1 *)
    | Hind ind0, Hind ind1 ->
        if Ind_utils.compare ind0.ie_ind ind1.ie_ind = 0 then
          if sat (Nc_cons (Apron.Tcons1.DISEQ, Ne_var i0, Ne_var i1)) then
            raise Bottom
          else
            let null0 = is_null i0
            and null1 = is_null i1
            and nonnull0 = is_non_null i0
            and nonnull1 = is_non_null i1 in
            match null0, null1, nonnull0, nonnull1 with
            | true, _, _, true
            | _, true, true, _ -> raise Bottom
            | true, true, _, _ ->
                g := ind_edge_rem i0 !g;
                1
            | _, _, true, true ->
                let f r = r.ir_kind = Ik_unk in
                if List.exists f ind0.ie_ind.i_rules then
                  Log.fatal_exn "merge_eq_nodes, ind-ind: fails to merge"
                else raise Bottom
            | _, _, _, _ ->
                Log.fatal_exn "merge_eq_nodes, ind-ind: other case, give up"
        else
          Log.fatal_exn
            "merge_eq_nodes, ind-ind: different inductives, give up"
    | _, _ ->
        (* we may actually need to make this work due to empty inductives *)
        Log.fatal_exn "illegal renaming: non empty edges (%d-%d)" i0 i1 in
  let renaming =
    compress
      (PairSet.fold
         (fun (i0, i1) acc -> fusion compare i0 i1 acc) eqreds IntMap.empty) in
  if false then
    Log.debug "Renaming: %s\n" (IntMap.t_2str "," string_of_int renaming);
  (* perform the renaming of all incoming edges of renamed nodes *)
  let g_renamed = graph_rename_ids renaming !g in
  (* rename the nodes *)
  IntMap.fold (fun irem _ -> sv_rem irem) renaming g_renamed, renaming
(* Whether a graph is compatible with a node being equal to zero *)
let graph_guard_node_null (v0: nid) (g: graph): guard_res =
  match (node_find v0 g).n_e with
  | Hpt _ ->
      (* v0 is an address, with fields; so _|_
       * (application of the separation principle) *)
      Gr_bot
  | Hseg se ->
      if se.se_ind.i_reds0 then
        (* we can deduce we have an empty segment at that point
         * possible improvement: we could also propagage to the segment dest *)
        Gr_emp_seg v0
      else Gr_no_info
  | Hind ie ->
      if ie.ie_ind.i_mt_rule then
        Gr_emp_ind v0
      else Gr_bot
  | _ -> Gr_no_info

(* return true only if the two pt blocks have share range *)
let pt_pt_disequal (b0: pt_edge Block_frag.t) (b1: pt_edge Block_frag.t): bool =
  let bfst_0, bend_0 = Block_frag.first_bound b0, Block_frag.end_bound b0 in
  let bfst_0, bend_0 = Offs.to_int (Bounds.to_offs bfst_0),
                       Offs.to_int (Bounds.to_offs bend_0) in
  let bfst_1, bend_1 = Block_frag.first_bound b1, Block_frag.end_bound b1 in
  let bfst_1, bend_1 = Offs.to_int (Bounds.to_offs bfst_1),
                       Offs.to_int (Bounds.to_offs bend_1) in
  (max bfst_0 bfst_1)< (min bend_0 bend_1)

(* return true only if pt block has share range with each non-empty rule
   of ind, and the empty rule of ind constraints that address = null *)
let pt_ind_disequal (ie: ind) (b: pt_edge Block_frag.t): bool =
  let bfst, bend = Block_frag.first_bound b, Block_frag.end_bound b in
  let bfst, bend =
    Offs.to_int (Bounds.to_offs bfst), Offs.to_int (Bounds.to_offs bend) in
  List.for_all
    (fun ele ->
      match ele.ir_kind with
      | Ik_unk -> false
      | Ik_empz -> true
      | Ik_range (l, r) -> max l bfst < min r bend
    ) ie.i_rules

(* return true only if all rules of both inds share some offset *)
let ind_ind_disequal (iel: ind) (ier: ind): bool =
  List.for_all
    (fun ele ->
      match ele.ir_kind with
       | Ik_unk -> false
       | Ik_empz -> true
       | Ik_range (l, r) ->
           List.for_all
             (fun eler ->
               match eler.ir_kind with
               | Ik_unk -> false
               | Ik_empz -> true
               | Ik_range (lr, rr) -> max l lr < min r rr
             ) ier.i_rules
    ) iel.i_rules

(* whether a graph + a condition are not compatible
 * (i.e., we should consider _|_ *)
let graph_guard (b: bool) (c: n_cons) (g: graph): guard_res =
  match c, b with
  | Nc_cons (Apron.Tcons1.EQ, Ne_var v0, Ne_csti 0), true
  | Nc_cons (Apron.Tcons1.EQ, Ne_csti 0, Ne_var v0), true
  | Nc_cons (Apron.Tcons1.DISEQ, Ne_var v0, Ne_csti 0), false
  | Nc_cons (Apron.Tcons1.DISEQ, Ne_csti 0, Ne_var v0), false ->
      (* Check whether node v0 may be null in g *)
      graph_guard_node_null v0 g
  | Nc_cons (Apron.Tcons1.EQ, e0, Ne_csti 0), true
  | Nc_cons (Apron.Tcons1.EQ, Ne_csti 0, e0), true
  | Nc_cons (Apron.Tcons1.DISEQ, e0, Ne_csti 0), false
  | Nc_cons (Apron.Tcons1.DISEQ, Ne_csti 0, e0), false ->
      (* If e0 writes down as v0+..., check whether v0 may be null in g *)
      begin
        match e0 with
        | Ne_bin (Apron.Texpr1.Add, Ne_var v0, _)
        | Ne_bin (Apron.Texpr1.Add, _, Ne_var v0) ->
            graph_guard_node_null v0 g
        | _ -> Gr_no_info
      end
  | Nc_cons (Apron.Tcons1.EQ, Ne_var v0, Ne_var v1), true
  | Nc_cons (Apron.Tcons1.DISEQ, Ne_var v0, Ne_var v1), false ->
      if false then Log.debug "node equality in the graph::: %d %d\n" v0 v1;
      if v0 != v1 then
        match (node_find v0 g).n_e, (node_find v1 g).n_e with
        | Hpt m0, Hpt m1 ->
            (* v0 and v1 are nodes corresponding to addresses
             * if points to edges maps are non empty, then _|_
             * (application of the separation principle) *)
            if Block_frag.is_not_empty m0
                && Block_frag.is_not_empty m1
                && pt_pt_disequal m0 m1 then
              Gr_bot
            else Gr_no_info
        (* cases where an equality may be deduced in the graph;
         * to reduce shortly thereafter *)
        | Hemp, Hemp ->
            if v0 < v1 then Gr_equality (v1, v0)
            else Gr_equality (v0, v1)
        | Hemp, _ -> Gr_equality (v0, v1)
        | _, Hemp -> Gr_equality (v1, v0)
        (* segment with destination corresponding to a region and
         * first element describing another region if non empty
         *  => imposes the emptiness of the segment *)
        | Hseg se, Hpt b -> Gr_emp_seg v0
        | Hpt b, Hseg se -> Gr_emp_seg v1
        | Hseg se, Hind ie -> Gr_emp_seg v0
        | Hind ie, Hseg se -> Gr_emp_seg v1
        | Hseg sel, Hseg ser -> Gr_emp_seg v0
        | Hind ie0, Hind ie1 ->
            if ind_ind_disequal ie0.ie_ind ie1.ie_ind &&
              ie0.ie_ind.i_mt_rule && ie1.ie_ind.i_mt_rule then
              Gr_equality (v0, v1)
            else
              begin
                Log.warn
                  "graph equality test; precision might have been gained";
                Gr_no_info
              end
        (* HS: when one side is ind, and other is pt *)
        | Hind ie, Hpt b ->
            let dis_range = pt_ind_disequal ie.ie_ind b in
            if dis_range && ie.ie_ind.i_mt_rule  then
              Gr_bot
            else if dis_range && not ie.ie_ind.i_mt_rule then
              begin
                if ie.ie_ind.i_emp_ipar = -1 then
                  Gr_emp_ind v0
                else
                  let ptr = List.nth ie.ie_args.ia_ptr ie.ie_ind.i_emp_ipar in
                  match (node_find ptr g).n_e with
                  | Hpt m0 ->
                      if Block_frag.is_not_empty m0
                          && Block_frag.is_not_empty b
                          && pt_pt_disequal m0 b then
                        Gr_bot
                      else Gr_emp_ind v0
                  | _ -> Gr_emp_ind v0
              end
            else
              begin
                Log.warn
                  "graph equality test; precision might have been gained";
                Gr_no_info
              end
        | Hpt b, Hind ie ->
            let dis_range = pt_ind_disequal ie.ie_ind b in
            if dis_range && ie.ie_ind.i_mt_rule  then
              Gr_bot
            else if dis_range && not ie.ie_ind.i_mt_rule  then
              Gr_emp_ind v1
            else
              begin
                Log.warn
                  "graph equality test; precision might have been gained";
                Gr_no_info
              end
      else Gr_no_info
  | _, _ -> Gr_no_info


(** Sat for conditions that can be partly evaluated in the graphs *)
(* Check if an SV disequality constraint is satisfied in a graph *)
let sat_graph_diseq (ls_cur_l: graph) (i: int) (j: int): bool =
  if i = j then false
  else
    let i_node = IntMap.find i ls_cur_l.g_g in
    let j_node = IntMap.find j ls_cur_l.g_g in
    match i_node.n_e, j_node.n_e with
    | Hpt _, Hpt _ -> true (* distinct SV carrying points-to => different *)
    | _ -> false


(** Segment splitting *)
let seg_split (is: nid) (g: graph): graph * nid =
  let se = seg_edge_find is g in
  (* integers and set parameters not supported yet *)
  let ind = se.se_ind in
  assert (ind.i_ipars = 0);
  assert (ind.i_spars = 0);
  (* creation of a middle node *)
  let im, g = sv_add_fresh Ntaddr Nnone g in
  (* creation of a set of parameters at the middle node *)
  let lpars, g =
    let rec aux i (l, g) =
      if i < 0 then (l, g)
      else
        let ii, g = sv_add_fresh Ntaddr Nnone g in
        aux (i-1) (ii :: l, g) in
    aux (ind.i_ppars-1) ([ ], g) in
  let lint, g = ind_args_1_make Ntint ind.i_ipars g in
  let lset, g = ind_sargs_make ind.i_spars g in
  let margs = { ia_ptr = lpars;
                ia_int = lint;
                ia_set = lset; } in
  (* remove the former segment edge *)
  let g = seg_edge_rem is g in
  (* build and add the two new segment edges *)
  let se0 = { se_ind   = ind;
              se_sargs = se.se_sargs;
              se_dargs = margs;
              se_dnode = im }
  and se1 = { se_ind   = ind;
              se_sargs = margs;
              se_dargs = se.se_dargs;
              se_dnode = se.se_dnode } in
  seg_edge_add is se0 (seg_edge_add im se1 g), im


(** Utilities *)
let node_attribute_lub (a0: node_attribute) (a1: node_attribute)
    : node_attribute =
  match a0, a1 with
  | Attr_array (stl, ll), Attr_array (str, lr) ->
      if stl = str && ll = lr then a0
      else Attr_none
  | Attr_ind il, Attr_ind ir ->
      if String.compare il ir = 0 then a0
      else Attr_none
  | _, _ -> Attr_none
(* For join, creation of a graph with a set of roots, from two graphs *)
let init_graph_from_roots
    (is_submem: bool) (* whether we consider a sub-memory or not *)
    (m: (int * int) IntMap.t)
    (msetv: (int * int) IntMap.t)
    (gl: graph) (gr: graph): graph =
  let graph =
    IntMap.fold
      (fun ii (il,ir) acc ->
        let nl = node_find il gl in
        let nr = node_find ir gr in
        let nt =
          if nl.n_t = nr.n_t then nl.n_t
          else
            match nl.n_t, nr.n_t with
            | Ntraw, nt | nt, Ntraw -> nt
            | _ -> Log.fatal_exn "init graph, nt" in
        let nalloc =
          if is_submem then Nsubmem
          else if nl.n_alloc = nr.n_alloc then nl.n_alloc
          else
            match nl.n_alloc, nr.n_alloc with
            | Nnone, _ | _, Nnone -> Nnone
            | _ -> Log.fatal_exn "init graph, nalloc: %s | %s"
                  (nalloc_2str nl.n_alloc) (nalloc_2str nr.n_alloc) in
        let r =
          match IntSet.mem il gl.g_roots, IntSet.mem ir gr.g_roots with
          | true, true -> true
          | false, false -> false
          | _ -> Log.fatal_exn "init_graph, root" in
        sv_add ~attr: (node_attribute_lub nl.n_attr nr.n_attr)
          ~root:(not is_submem && r) ii nt nalloc acc
      ) m (graph_empty gl.g_inds) in
  let graph =
    IntMap.fold
      (fun ii (il, ir) acc ->
        setv_add true ii acc
      ) msetv graph in
  graph

(* retrieve node with index 'n' from graph 'g' *)
let get_node (n: int) (g: graph): node =
  IntMap.find n g.g_g

(* A sub-memory specific utility function:
 * - given a (node,offset) pair, search whether there exist an edge
 *   pointing to it *)
let node_offset_is_referred (g: graph) ((i, o): int * Offs.t): bool =
  let n = node_find i g in
  try
    IntSet.iter
      (fun pred ->
        let npred = node_find pred g in
        match npred.n_e with
        | Hemp -> ( )
        | Hpt block ->
            Block_frag.iter_base
              (fun _ pe ->
                if i = fst pe.pe_dest && Offs.eq o (snd pe.pe_dest) then
                  raise True
              ) block
        | Hind _ | Hseg _ ->
            (* we should search for references there too... *)
            ( )
      ) n.n_preds;
    false
  with True -> true

(** Latex output *)
let latex_output (roots: (int, string) PMap.t) (chan: out_channel)
    (g: graph): unit =
  (* - construction of the "simplified graph"
   * - strongly connected components and topological order
   * - node ordering
   * - at some point, treat direct pt successors
   *)
  let module G = Graph.IntGraph in
  let pos_graph, roots =
    IntMap.fold
      (fun is n (accp, accr) ->
        if PMap.mem is roots then
          match n.n_e with
          | Hpt mc -> (* mc should contain only one element at offset zero *)
              let v = Block_frag.find_addr Bounds.zero in
              accp, IntMap.add is v accr
          | _ -> Log.fatal_exn "latex_output, crashed on root"
        else
          let accp = G.node_add is accp in
          let accp =
            match n.n_e with
            | Hemp
            | Hind _ -> accp
            | Hpt mc ->
                Block_frag.fold_base
                  (fun _ pe accp ->
                    let dest = fst pe.pe_dest in
                    G.edge_add is dest (G.node_add dest accp)
                  ) mc accp
            | Hseg se ->
                G.edge_add is se.se_dnode (G.node_add se.se_dnode accp) in
          accp, accr
      ) g.g_g (G.empty, IntMap.empty) in
  let _ = G.tarjan pos_graph in
  Log.todo_exn "latex output (1)"


(** Ensuring consistency with numerical values *)
let sve_sync_bot_up (g: graph): graph * svenv_mod =
  { g with g_svemod = Dom_utils.svenv_empty }, g.g_svemod


(** Garbage collection support *)
(* Incremental garbage collection:
 *  -> this funciton is purely based on the back indexes;
 *   i.e, a node with no back_index, and that is not a root is removed
 *  -> for now, we rely on an externally supplied set;
 *     later on, use the g_roots field and trigger gc anywhere *)
(* Improvements to make in the GC code:
 *  - rely on a g_roots field for the root communication ?
 *  - do things even more incrementally: try removing a node
 *    when an edge to it gets removed
 *  - we need to study why is gc_incr not more effective
 *  - gc functions temporarily break invariants of back pointers
 *  - gc functions should warn when they detect a points to edge that
 *    needs to be removed *)
let gc_incr (roots: int Aa_sets.t) (g: graph): graph =
  if Flags.flag_gc_stat then incr Statistics.gc_stat_incr_num;
  (* gc should only be performed on states with no node pending treatment *)
  assert (g.g_svemod = Dom_utils.svenv_empty);
  (* proceed with the garbage collection *)
  IntMap.fold
    (fun i n acc ->
      if IntSet.cardinal n.n_preds > 0 || Aa_sets.mem i roots then
        acc
      else
        begin
          if !Flags.flag_debug_back_index then
            Log.force "gc_incr removing node %d\n" i;
          if Flags.flag_gc_stat then incr Statistics.gc_stat_incr_rem;
          sv_rem i acc
        end
    ) g.g_g g
(* Removal of all nodes not reachable from a set of roots *)
let gc (roots: int Aa_sets.t) (g: graph): graph =
  if Flags.flag_gc_stat then incr Statistics.gc_stat_full_num;
  (* gc should only be performed on states with no node pending treatment *)
  assert (g.g_svemod = Dom_utils.svenv_empty);
  (* perform an incremental collection first, if required *)
  let g =
    if Flags.flag_gc_incr then gc_incr roots g
    else g in
  if !Flags.flag_gc_full then
    (* Exhaustive traversal, saturation of set of roots *)
    let reach =
      let r = ref IntSet.empty
      and todos = ref roots in
      let add_dest (i: int): unit =
        if not (IntSet.mem i !r) then
          todos := Aa_sets.add i !todos in
      while !todos != Aa_sets.empty do
        let i = Aa_sets.min_elt !todos in
        r := IntSet.add i !r;
        todos := Aa_sets.remove i !todos;
        try
          let n = IntMap.find i g.g_g in
          let s = node_reach n in
          IntSet.iter add_dest s
        with Not_found -> ( )
      done;
      !r in
    let nremoved =
      IntMap.fold
        (fun i _ acc ->
          if IntSet.mem i reach then acc
          else
            begin
              if !Flags.flag_debug_back_index then
                Log.force "gc_full removing node %d\n" i;
              if Flags.flag_gc_stat then incr Statistics.gc_stat_full_rem;
              IntSet.add i acc
            end
        ) g.g_g IntSet.empty in
    IntSet.fold sv_rem nremoved (IntSet.fold edge_rem_any nremoved g)
  else g


(** Functions on node injections (for is_le) *)
module Nemb =
  struct
    let empty: node_embedding =
      { n_img = IntMap.empty ;
        n_pre = IntMap.empty }
    (* To string, compact version *)
    let ne_2str (ni: node_embedding): string =
      IntMap.t_2str "\n" string_of_int ni.n_img
    (* To string, long version *)
    let ne_full_2stri (ind: string) (inj: node_embedding): string =
      IntMap.fold
        (fun i j acc ->
          Printf.sprintf "%s%s%d => %d\n" acc ind i j
        ) inj.n_img ""
    (* Tests membership *)
    let mem (i: int) (ni: node_embedding): bool =
      IntMap.mem i ni.n_img
    (* Find an element in the mapping *)
    let find (i: int) (ni: node_embedding): int =
      IntMap.find i ni.n_img
    (* Add an element to the mapping *)
    let add (i: int) (j: int) (ni: node_embedding): node_embedding =
      try
        assert (IntMap.find i ni.n_img = j);
        ni
      with
      | Not_found ->
          let npre =
            let oset =
              try IntMap.find j ni.n_pre with Not_found -> IntSet.empty in
            IntSet.add i oset in
          { n_img = IntMap.add i j ni.n_img ;
            n_pre = IntMap.add j npre ni.n_pre }
    (* Initialization *)
    let init (m: node_emb): node_embedding =
      Aa_maps.fold add m empty
    (* Extraction of siblings information *)
    let siblings (ni: node_embedding): IntSet.t IntMap.t =
      IntMap.fold
        (fun j pre acc ->
          if IntSet.cardinal pre > 1 then IntMap.add j pre acc
          else acc
        ) ni.n_pre IntMap.empty
  end


(** Functions on node weak injections (for directed weakening) *)
module Nwkinj =
  struct
    let empty: node_wkinj =
      { wi_img  = IntMap.empty;
        wi_l_r  = IntMap.empty;
        wi_lr_o = PairMap.empty }
    (* Verification of existence of a mapping *)
    let mem (wi: node_wkinj) ((il, ir): int * int) (io: int): bool =
      try
        let cl, co = IntMap.find ir wi.wi_img in
        cl = il && co = io
      with
      | Not_found -> false
    (* Find function, may raise Not_found *)
    let find (wi: node_wkinj) (p: int * int): int =
      PairMap.find p wi.wi_lr_o
    (* Addition of a mapping *)
    let add (wi: node_wkinj) ((il, ir): int * int) (io: int): node_wkinj =
      if IntMap.mem ir wi.wi_img then
        Log.fatal_exn "Node_weak_inj: cannot override %d" ir
      else
        let os = try IntMap.find il wi.wi_l_r with Not_found -> IntSet.empty in
        assert (not (PairMap.mem (il,ir) wi.wi_lr_o));
        { wi_img  = IntMap.add ir (il, io) wi.wi_img;
          wi_l_r  = IntMap.add il (IntSet.add ir os) wi.wi_l_r;
          wi_lr_o = PairMap.add (il,ir) io wi.wi_lr_o }
    (* To string, long and indented version *)
    let wi_2stri (ind: string) (wi: node_wkinj): string =
      let s0 =
        PairMap.fold
          (fun (il, ir) ii acc ->
            Printf.sprintf "%s  (%d,%d) => %d\n%s" ind il ir ii acc
          ) wi.wi_lr_o  "" in
      Printf.sprintf "%sInjection:\n%s"
        (* "%sInjection:\n%s%sProjection:\n%s%sOk: %b\n" *)
        ind s0 (* ind (check nr) *)
  end


(** Functions on node relations (for join) *)
module Nrel =
  struct
    let empty =
      { n_inj = PairMap.empty ;
        n_pi  = IntMap.empty ;
        n_l2r = IntMap.empty ;
        n_r2l = IntMap.empty ; }
    (* Consistency check *)
    let check (nr: node_relation): bool =
      try
        PairMap.iter
          (fun (il,ir) ii ->
            let kl, kr = IntMap.find ii nr.n_pi in
            if kl != il || kr != ir then raise Stop
          ) nr.n_inj ;
        IntMap.iter
          (fun ii ip ->
            if PairMap.find ip nr.n_inj != ii then raise Stop
          ) nr.n_pi ;
        true
      with
      | Stop -> false
      | Not_found -> false
    (* Verification of existence of a mapping *)
    let mem (nr: node_relation) (pn: int * int) (nn: int): bool =
      try PairMap.find pn nr.n_inj = nn
      with Not_found -> false
    (* Find function, may raise Not_found *)
    let find (nr: node_relation) (pn: int * int): int =
      PairMap.find pn nr.n_inj
    (* find a pair from out *)
    let find_p (nr: node_relation) (p:int): int * int =
      IntMap.find p nr.n_pi
    (* Addition of a mapping *)
    let add (nr: node_relation) ((pl, pr) as pn: int * int)
        (nn: int): node_relation =
      if PairMap.mem pn nr.n_inj then
        Log.info "trying to re-add: (%d, %d) => %d [%d]" pl pr nn
          (PairMap.find pn nr.n_inj);
      assert (not (PairMap.mem pn nr.n_inj));
      assert (not (IntMap.mem nn nr.n_pi));
      let l2r =
        let o = try IntMap.find pl nr.n_l2r with Not_found -> IntSet.empty in
        IntMap.add pl (IntSet.add pr o) nr.n_l2r in
      let r2l =
        let o = try IntMap.find pr nr.n_r2l with Not_found -> IntSet.empty in
        IntMap.add pr (IntSet.add pl o) nr.n_r2l in
      { n_inj = PairMap.add pn nn nr.n_inj ;
        n_pi  = IntMap.add nn pn nr.n_pi ;
        n_l2r = l2r ;
        n_r2l = r2l ; }
    (* To string, long version *)
    let nr_2stri (ind: string) (nr: node_relation): string =
      let s0 =
        PairMap.fold
          (fun (il, ir) ii acc ->
            Printf.sprintf "%s  (%d,%d) => %d\n%s" ind il ir ii acc
          ) nr.n_inj  "" in
      let s1 =
        IntMap.fold
          (fun ii (il, ir) acc ->
            Printf.sprintf "%s  %d => (%d,%d)\n%s" ind ii il ir acc
          ) nr.n_pi "" in
      Printf.sprintf "%sInjection:\n%s%sProjection:\n%s%sOk: %b\n"
        ind s0 ind s1 ind (check nr)
    (* To string, compact version *)
    let nr_2strc (nr: node_relation): string =
      let isdeb = ref true in
      let s =
        PairMap.fold
          (fun (il, ir) ii acc ->
            let sep = if !isdeb then "" else "; " in
            isdeb := false;
            Printf.sprintf "%s%s(%d,%d) => %d" acc sep il ir ii
          ) nr.n_inj "" in
      Printf.sprintf "{ %s }" s
    (* Collect nodes associated to other side *)
    let siblings (s: side) (i: int) (nr: node_relation): IntSet.t =
      try IntMap.find i (if s = Lft then nr.n_l2r else nr.n_r2l)
      with Not_found -> IntSet.empty
    (* Search for nodes that have multiple right matches *)
    let mult_bind_candidates (side: side)
        (nr: node_relation) (b: IntSet.t): IntSet.t =
      IntMap.fold
        (fun il r acc ->
          if IntSet.subset b r then IntSet.add il acc
          else acc
        ) (if side = Lft then nr.n_l2r else nr.n_r2l) IntSet.empty
    (* Fold function *)
    let fold (f: int -> (int * int) -> 'a -> 'a) (nr: node_relation): 'a -> 'a =
      IntMap.fold f nr.n_pi
  end

(** Utilities over steps *)
let is_segment = function
  | Segment _ -> true
  | _ -> false
let is_offset = function
  | Offset  _ -> true
  | _ -> false

(** Operations on abs_graph_arg: helping join *)
(* Check if memory starting from SV could be weakened into a segment *)
let sv_seg_weaken (gl: abs_graph_arg option) (sl: int): bool =
  try
    let gl = Option.get gl in
    let onode = sl, Offs.zero in
    List.exists
      (fun ele ->
         ele.sc = onode && is_segment (List.hd ele.pth)
         && ele.sc <> ele.dt ) gl
  with
  | Not_found -> false
  | Invalid_argument _ -> false
  | Failure _ -> false

(* Check if memory starting from SV could have a segment intro *)
let sv_seg_intro (gl: abs_graph_arg option) (sl: int): bool =
  try
    let gl = Option.get gl in
    let onode = sl, Offs.zero in
    List.exists
      (fun ele -> ele.sc = onode && is_segment (List.hd ele.pth)) gl
  with
  | Not_found -> false
  | Invalid_argument _ -> false
  | Failure _ -> false

(* Check whether a segment extension could be performed *)
let is_bseg_ext (gl: abs_graph_arg option) (sl: int)
    (gr: abs_graph_arg option) (sr: int): bool =
  sv_seg_weaken gl sl && sv_seg_weaken gr sr
let is_bseg_intro  (gl: abs_graph_arg option) (sl: int)
    (gr: abs_graph_arg option) (sr: int): bool =
  sv_seg_intro gl sl && sv_seg_intro gr sr

(* choose destination nodes for seg_intro from encode graph *)
let choose_dst (sc: int) (ag: abs_graph_arg option)
    (sibs: IntSet.t): IntSet.t =
  try
    let ag = Option.get ag in
    let sc = sc, Offs.zero in
    let send =
      List.fold_left
        (fun acc ele ->
          if ele.sc = sc && is_segment (List.hd ele.pth) then
            IntSet.add (fst ele.dt) acc
          else acc
        ) IntSet.empty ag in
    IntSet.inter send sibs
  with
  | Invalid_argument _ -> IntSet.empty

(** Operations on "join_arg" type: join with additional arguments *)
(* Translation of join argument *)
let tr_join_arg (sat: n_cons -> bool) ((g, x): graph * join_ele)
    : graph * join_arg =
  let tr_node (n: PairSet.t) (x: graph): onode * graph =
    try
      let os, is = PairSet.choose n in
      let n = PairSet.remove (os, is) n in
      let x, pte =
        pt_edge_extract sat (is, Offs.of_int os) Flags.abi_ptr_size x in
      PairSet.fold
        (fun (os, is) (onode, x) ->
          let x, pte =
            pt_edge_extract sat (is, Offs.of_int os) Flags.abi_ptr_size x in
          assert (pte.pe_dest = onode);
          onode, x
        ) n (pte.pe_dest, x)
    with Not_found -> Log.fatal_exn "tr_join_arg, node not found" in
  let tr_abs_g ((g, n, _disj_n): abs_graph) (x: graph): abs_graph_arg * graph =
    List.fold_left
      (fun (acc, x) (sc, p, dt) ->
        let sc, x = tr_node sc x in
        let dt, x = tr_node dt x in
        { sc  = sc;
          dt  = dt;
          pth = p } :: acc, x
      ) ([], x) g in
  let f (ag: abs_graph option) (g: graph): abs_graph_arg option * graph =
    match ag with
    | None -> None, g
    | Some ag -> let ag, g = tr_abs_g ag g in Some ag, g in
  let abs_gi, g = f x.abs_gi g in
  let abs_go, g = f x.abs_go g in
  g, { abs_gi = abs_gi;
       abs_go = abs_go; }

(* Find end points for segment extension *)
let seg_extension_end (is: int) (arg: join_arg): (int * string) option =
  match arg.abs_go with
  | None -> None
  | Some abs_g ->
      try
        let pt =
          List.find
            (fun ele ->
              ele.sc = (is, Offs.zero)
                &&
              begin
                match ele.pth with
                | [] -> false
                | seg :: tl -> is_segment seg
              end
            ) abs_g in
        assert (snd pt.dt = Offs.zero);
        let x =
          match List.hd pt.pth with
          | Segment (name, _) -> name
          | _ -> Log.fatal_exn "improper case" in
        Some (fst pt.dt, x)
      with Not_found -> None

(* Find a node in encoded graph *)
let encode_node_find (is: int) (arg: join_arg): bool =
  match arg.abs_gi with
  | None -> false
  | Some gi -> List.exists (fun ele -> fst ele.sc = is) gi

(* Remove node and related edges in encoded graph *)
let remove_node (is: int) (id: int) (arg: join_arg): join_arg =
  let f ele = (fst ele.sc <> is) || ( fst ele.dt <> id) in
  let i = BatOption.map (List.filter f) arg.abs_gi in
  let o = BatOption.map (List.filter f ) arg.abs_go in
  { abs_gi = i;
    abs_go = o }

(* Consume pt in encoded graph *)
let encode_pt_pt (ons: onode) (dons: onode) (arg: join_arg): join_arg =
  let consume_pt ((is, offs): int * Offs.t) ((ds, dof): int * Offs.t)
      (arg: abs_graph_arg): abs_graph_arg =
    (* HLI: add some comment after tests *)
    List.fold_left
      (fun acc ele ->
        let default = ele :: acc in
        if ele.sc <> (is, Offs.zero) then default
        else
          begin
            match ele.pth with
            | [ Offset off ] ->
                if off <> offs then default
                else
                  begin
                    assert ((ds, dof) = ele.dt);
                    acc
                  end
            | Offset off :: t ->
                if off <> offs then default
                else
                  (* (assert ((ds, dof) <> ele.dt); *)
                  { ele with
                    sc = (ds, dof);
                    pth = t } :: acc
            | _ -> ele :: acc
          end
      ) [ ] arg in
  { abs_gi = BatOption.map (consume_pt ons dons) arg.abs_gi;
    abs_go = BatOption.map (consume_pt ons dons) arg.abs_go; }

(* Collect all inductive definitions used in a graph *)
let collect_inds (g: graph): StringSet.t =
  IntMap.fold
    (fun key ele acc ->
      match ele.n_e with
      | Hemp -> acc
      | Hpt _ -> acc
      | Hind ind_edge -> StringSet.add ind_edge.ie_ind.i_name acc
      | Hseg seg_edge -> StringSet.add seg_edge.se_ind.i_name acc
    ) g.g_g StringSet.empty

let visu_opt_of_string (opt: string): visu_option =
  match opt with
  | "CC" -> Connex_component
  | "SUCC" -> Successors
  | "CUTL" -> Cut_leaves
  | s -> failwith ("visu_opt_of_string: " ^ s)

