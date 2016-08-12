(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: constrain_utils.ml
 **       basic tools over constraints
 ** Antoine Toubhans, 2012/04/19 *)
open Data_structures
open Flags
open Lib
open Ast_sig
open Ast_utils
open Off_sig
open Constrain_sig

(** Error report *)
module Log =
  Logger.Make(struct let section = "ctrn_uts" and level = Log_level.DEBUG end)

  
(* id utilitary tools *)
let id_next (i: id): id = i + 1
let id_zero: id = 0
let id_eq: id -> id -> bool = (=)

let destination_eq (d1: destination) (d2: destination): bool = 
  match d1, d2 with
  | Pd_null, Pd_null -> true
  | Pd_id x, Pd_id y -> id_eq x y
  | _ -> false

(* paths utilitary tools *)
let path_concat: path -> path -> path = Regular_expr.concat  
let path_is_rigid: path -> bool = Regular_expr.is_rigid  
    
(* c_path utilitary tools *)
let c_path_concat (c1: c_path) (a: id) (c2: c_path): c_path option =
  if PSet.mem a c1.cp_targets
      && Regular_expr.eq c1.cp_induc_path c2.cp_induc_path 
      && destination_eq c1.cp_prop_dst c2.cp_prop_dst then
    let cp_targets =
      PSet.union (PSet.remove a c1.cp_targets) c2.cp_targets in
    let ppath =
      Regular_expr.simplify
        (Regular_expr.plus c1.cp_prop_path c2.cp_prop_path) in
    Some { cp_targets;
           cp_target_null = c1.cp_target_null || c2.cp_target_null;
           cp_induc_path  = c1.cp_induc_path;
           cp_prop_path   = ppath;
           cp_prop_dst    = c1.cp_prop_dst }
  else None
      
let c_path_get_args (c: c_path): id PSet.t =
  match c.cp_prop_dst with
  | Pd_null -> c.cp_targets
  | Pd_id x -> PSet.add x c.cp_targets

let c_path_map (f: id -> id) (c: c_path): c_path =
  let d =
    match c.cp_prop_dst with
    | Pd_id n -> Pd_id (f n)
    | Pd_null -> Pd_null in
  { cp_targets = PSet.fold (fun n -> PSet.add (f n)) c.cp_targets PSet.empty;
    cp_target_null = c.cp_target_null;
    cp_induc_path = c.cp_induc_path;
    cp_prop_path = c.cp_prop_path;
    cp_prop_dst = d }      

let c_path_map_null (n: id) (c: c_path): c_path = 
  let cp_prop_dst =
    match c.cp_prop_dst with
    | Pd_id x -> if id_eq x n then Pd_null else Pd_id x
    | Pd_null -> Pd_null in
  { cp_targets     = PSet.remove n c.cp_targets;
    cp_target_null = c.cp_target_null || PSet.mem n c.cp_targets;
    cp_induc_path  = c.cp_induc_path;
    cp_prop_path   = c.cp_prop_path;
    cp_prop_dst }

let c_path_eq (c1: c_path) (c2: c_path): bool = 
  PSet.equal c1.cp_targets c2.cp_targets
    && c1.cp_target_null = c2.cp_target_null
    && Regular_expr.eq c1.cp_induc_path c2.cp_induc_path
    && Regular_expr.eq c1.cp_prop_path c2.cp_prop_path
    && destination_eq c1.cp_prop_dst c2.cp_prop_dst
    
(* d_path utilitary tools *)
let d_path_concat (d1: d_path) (a: id) (d2: d_path): d_path option =
  if Offs.eq d1.dp_bw_induc d2.dp_bw_induc 
      && PSet.equal d1.dp_fw_induc d2.dp_fw_induc 
      && PSet.mem (d2.dp_bw_target, a) d1.dp_targets then
    let targs =
      PSet.union d2.dp_targets
        (PSet.remove (d2.dp_bw_target, a) d1.dp_targets) in
    Some { dp_bw_target = d1.dp_bw_target;
           dp_fw_induc  = d1.dp_fw_induc;
           dp_bw_induc  = d1.dp_bw_induc;
           dp_targets   = targs }
  else None
let d_path_get_args (d: d_path): id PSet.t =
  PSet.fold (fun (x, y) s -> PSet.add x (PSet.add y s))
    d.dp_targets (PSet.singleton d.dp_bw_target)
let d_path_map (f: id -> id) (d: d_path): d_path = 
  let targets = 
    PSet.fold(fun (x, y) -> PSet.add (f x, f y)) d.dp_targets PSet.empty in
  { dp_bw_target = f d.dp_bw_target;
    dp_fw_induc  = d.dp_fw_induc;
    dp_bw_induc  = d.dp_bw_induc;
    dp_targets   = targets }
let d_path_map_null (n: id) (d: d_path): d_path option = 
  if (d.dp_bw_target = n 
    || (PSet.exists (fun (x, _) -> x = n)) d.dp_targets) then
    None
  else
    let targets = PSet.filter (fun (_, y) -> y != n) d.dp_targets in
    Some { dp_bw_target = d.dp_bw_target;
           dp_fw_induc  = d.dp_fw_induc;
           dp_bw_induc  = d.dp_bw_induc;
           dp_targets   = targets }
let d_path_eq (d1: d_path) (d2: d_path): bool =
  PSet.equal d1.dp_targets d2.dp_targets
    && d1.dp_bw_target = d2.dp_bw_target
    && Offs.eq d1.dp_bw_induc d2.dp_bw_induc
    && PSet.equal d1.dp_fw_induc d2.dp_fw_induc
    
(* eq classes utilitary functions *)
let eq_class_create_singl (n: id) (eq: eq_class) = 
  Ecl_id eq.next,
  { null_cl = eq.null_cl;
    cl      = IntMap.add eq.next (PSet.singleton n) eq.cl;
    next    = eq.next + 1 }
    
(* returns (n, S, E):
   n: the new name of the merged eq classes
   S: set of id that need a fresh-up
   E: the new eq_class                      *)
let eq_class_fusion (i: eq_cl_loc) (j: eq_cl_loc) 
    (eq: eq_class): eq_cl_loc * id PSet.t * eq_class = 
  match i, j with 
  | Ecl_null, Ecl_null -> 
      Log.fatal_exn "eq_class_fusion: shall not be called here"
  | Ecl_null, Ecl_id i | Ecl_id i, Ecl_null ->
      let cli = try IntMap.find i eq.cl with | Not_found -> PSet.empty in
      let cl = IntMap.remove i eq.cl in
      let null_cl = PSet.union cli eq.null_cl in
      Ecl_null, cli, { null_cl; cl; next = eq.next }
  | Ecl_id i, Ecl_id j -> 
      let cli, clj = 
        (try IntMap.find i eq.cl with | Not_found -> PSet.empty),
        (try IntMap.find j eq.cl with | Not_found -> PSet.empty) in
      if PSet.cardinal cli > PSet.cardinal clj then
        let cl = IntMap.remove j eq.cl in
        let cl = IntMap.add i (PSet.union cli clj) cl in
        Ecl_id i, clj, { eq with cl }
      else
        let cl = IntMap.remove i eq.cl in
        let cl = IntMap.add j (PSet.union clj cli) cl in
        Ecl_id j, cli, { eq with cl }
          
let eq_class_remove (loc: eq_cl_loc) (n: id) (e: eq_class): eq_class = 
  match loc with
  | Ecl_id id ->
      let lm = try IntMap.find id e.cl with | Not_found -> PSet.empty in
      let lm = PSet.remove n lm in
      if PSet.is_empty lm then
        { e with cl = IntMap.remove id e.cl }
      else
        { e with cl = IntMap.add id lm e.cl }
  | Ecl_null -> 
      let null_cl = PSet.remove n e.null_cl in
      { e with null_cl }

let eq_class_find (loc: eq_cl_loc) (e: eq_class): id PSet.t = 
  match loc with
  | Ecl_null -> e.null_cl
  | Ecl_id i -> IntMap.find i e.cl

(* it folds: 
 * - f_eqs over all couple (n, m) (with n<>m) 
 * such that n==m stands for the eq_class variable e,
 * including n & m that are both in the zero equality class;
 * - f_nulls over all n such that n==0 stands *)
let fold_eq_class (f_eqs: id -> id -> 'a -> 'a) (f_nulls: id -> 'a -> 'a)
    (e: eq_class) (a: 'a): 'a = 
  let rec aux set a =
    if PSet.is_empty set then a
    else
      let n = PSet.choose set in
      let set = PSet.remove n set in
      let a = PSet.fold (f_eqs n) set a in
      aux set a in
  let a = IntMap.fold (fun _ -> aux) e.cl a in
  let a = aux e.null_cl a in
  PSet.fold f_nulls e.null_cl a

(* node utilitary functions *)
let iter_fw_paths (f: path -> destination -> unit) (n: node): unit =
  PMap.iter (fun p -> PSet.iter (f p)) n.n_fw_paths

let iter_bw_paths (f: path -> id -> unit) (n: node): unit =
  PMap.iter (fun p -> PSet.iter (f p)) n.n_bw_paths

let fold_fw_paths (f: path -> destination -> 'a -> 'a) (n: node): 'a -> 'a = 
  PMap.fold (fun p -> PSet.fold (f p)) n.n_fw_paths
    
let fold_bw_paths (f: path -> id -> 'a -> 'a) (n: node): 'a -> 'a = 
  PMap.fold (fun p -> PSet.fold (f p)) n.n_bw_paths

let for_all_paths (f: path -> destination -> bool) (n: node): bool =
  let rec aux n_pmap = 
    if PMap.is_empty n_pmap then true
    else
      let p, dst_l = PMap.choose n_pmap in
      if PSet.for_all (f p) dst_l then 
        aux (PMap.remove p n_pmap)
      else false in
  aux n.n_fw_paths

let iter_c_paths (f: c_path -> unit) (n: node): unit = 
  PSet.iter f n.n_c_paths
let fold_c_paths (f: c_path -> 'a -> 'a) (n: node): 'a -> 'a =
  PSet.fold f n.n_c_paths
let iter_d_paths (f: d_path -> unit) (n: node): unit = 
  PSet.iter f n.n_d_paths
let fold_d_paths (f: d_path -> 'a -> 'a) (n: node): 'a -> 'a =
  PSet.fold f n.n_d_paths

let for_all_c_paths (f: c_path -> bool) (n: node): bool =
  PSet.for_all f n.n_c_paths
let for_all_d_paths (f: d_path -> bool) (n: node): bool =
  PSet.for_all f n.n_d_paths

let add_fw_paths (p: path) (dst: destination) (no: node): node = 
  let n_fw_paths = no.n_fw_paths in
  let n_fw_paths = 
    try
      let ns = PMap.find p n_fw_paths in
      PMap.add p (PSet.add dst ns) n_fw_paths 
    with Not_found -> PMap.add p (PSet.add dst PSet.empty) n_fw_paths in
  { no with n_fw_paths }  

let add_bw_paths (p: path) (n: id) (no: node): node = 
  let n_bw_paths = no.n_bw_paths in
  let n_bw_paths = 
    try
      let ns = PMap.find p n_bw_paths in
      PMap.add p (PSet.add n ns) n_bw_paths 
    with Not_found -> PMap.add p (PSet.add n PSet.empty) n_bw_paths in
  { no with n_bw_paths }
    
let remove_fw_paths (p: path) (dst: destination) (no: node): node =
  let n_fw_paths = no.n_fw_paths in
  let n_fw_paths = 
    try
      let ns = PMap.find p n_fw_paths in
      let ns = PSet.filter (fun m -> not (destination_eq dst m)) ns in
      if PSet.is_empty ns then PMap.remove p n_fw_paths 
      else PMap.add p ns n_fw_paths 
    with Not_found -> n_fw_paths in
  { no with n_fw_paths }

let remove_bw_paths (p: path) (n: id) (no: node): node =
  let n_bw_paths = no.n_bw_paths in
  let n_bw_paths = 
    try
      let ns = PMap.find p n_bw_paths in
      let ns = PSet.filter (fun m -> not (id_eq n m)) ns in
      if PSet.is_empty ns then PMap.remove p n_bw_paths 
      else PMap.add p ns n_bw_paths 
    with Not_found -> n_bw_paths in
  { no with n_bw_paths }


(* initializers *)
let init_eq_class: eq_class = 
  { null_cl = PSet.empty;
    cl      = IntMap.empty;
    next    = 0 }
    
let top (): cstr = 
  { nodes    = PMap.empty;
    eq_class = init_eq_class;
    id_up    = id_zero;
    id_free  = [] }

(* pretty printing *)
let id_2str (n: id): string = Printf.sprintf "|%i|" n
let path_2str: path -> string = Regular_expr.t_2str Offs.t_2str
let destination_2str: destination -> string = function
  | Pd_id n -> id_2str n
  | Pd_null -> "0"
let c_path_2str (src: id) (c: c_path): string = 
  Printf.sprintf "C[ %s , X.%s|>>%s ]( %s, { %s%s })"
    (path_2str c.cp_induc_path)
    (path_2str c.cp_prop_path)
    (destination_2str c.cp_prop_dst)
    (id_2str src)
    (PSet.t_2str "," id_2str c.cp_targets)
    (if c.cp_target_null && PSet.is_empty c.cp_targets then "null"
    else if c.cp_target_null then ",null"
    else "")
let d_path_2str (src: id) (d: d_path): string = 
  Printf.sprintf "D[ { %s } , %s ](%s, %s){ %s }"
    (PSet.t_2str "," Offs.t_2str d.dp_fw_induc)
    (Offs.t_2str d.dp_bw_induc)
    (id_2str d.dp_bw_target) (id_2str src)
    (PSet.t_2str ","
       (fun (x, y) -> Printf.sprintf "(%s, %s)" (id_2str x) (id_2str y))
       d.dp_targets)
    
let eq_cl_loc_2str: eq_cl_loc -> string = function
  | Ecl_null -> "Null"
  | Ecl_id i -> Printf.sprintf "[%i]" i

let node_2stri (ind: string) (src: id) (n: node): string = 
  if flag_debug_pl_back_info then
    Printf.sprintf 
      "%s%s:equality class id: %s\n%s%s%s%sC(bw){ %s }\n%s%sD(bw){ %s }%s\n" 
      ind (id_2str src) (eq_cl_loc_2str n.n_eqs) 
      (fold_fw_paths
         (fun p dst s ->
           Printf.sprintf "%s%s%s.%s |>> %s\n" s ind (id_2str src)
             (path_2str p) (destination_2str dst))
         n "")
      (PMap.t_2str "" ""
         (fun p dsts ->  
           Printf.sprintf "%s{ %s }.%s|>>%s (bw)\n" 
             ind (PSet.t_2str "," id_2str dsts)
             (path_2str p) (id_2str src))        
         n.n_bw_paths)
      (PSet.t_2str ""
         (fun c -> Printf.sprintf "%s%s\n" ind (c_path_2str src c)) 
         n.n_c_paths)
      ind (PSet.t_2str "," id_2str n.n_bw_c_paths)
      (PSet.t_2str ""
         (fun c -> Printf.sprintf "%s%s\n" ind (d_path_2str src c)) 
         n.n_d_paths)
      ind (PSet.t_2str "," id_2str n.n_bw_d_paths)
      (if n.n_not_null then 
        Printf.sprintf "%s%s != 0\n" ind (id_2str src) 
      else "")
  else
    Printf.sprintf "%s%s%s%s"      
      (fold_fw_paths
         (fun p dst s ->
           Printf.sprintf "%s%s%s.%s |>> %s\n" s ind (id_2str src)
             (path_2str p) (destination_2str dst))
         n "")
      (PSet.t_2str ""
         (fun c -> Printf.sprintf "%s%s\n" ind (c_path_2str src c)) 
         n.n_c_paths)
      (PSet.t_2str ""
         (fun c -> Printf.sprintf "%s%s\n" ind (d_path_2str src c)) 
         n.n_d_paths)
      (if n.n_not_null then 
        Printf.sprintf "%s%s != 0\n" ind (id_2str src) 
      else "")
      
let eq_class_2stri (ind: string) (e: eq_class): string = 
  let s =
    let t =
      if e.null_cl = PSet.empty then "empty"
      else PSet.t_2str "," id_2str e.null_cl in
    Printf.sprintf "%sNids equal to null: { %s }\n" ind t in
  IntMap.fold
    (fun i eqs s ->
      let t =
        if eqs = PSet.empty then "empty"
        else PSet.t_2str "," id_2str eqs in
      Printf.sprintf "%s%sEq.cl: id[%i]. { %s }\n" s ind i t)
    e.cl s
    
let cstr_2stri (ind: string) (s: cstr): string =
  Printf.sprintf 
    "%s%sfree ids: { %s } & %s and upper\n%s" 
    (eq_class_2stri ind s.eq_class)
    ind (gen_list_2str "" id_2str "," s.id_free)
    (id_2str s.id_up) 
    (PMap.t_2str "" "" (node_2stri ind) s.nodes)
    
let cstr_2str: cstr -> string = cstr_2stri ""

let cstr_indcall_2stri (ind: string) (t: cstr_indcall): string = 
  let s_main = Printf.sprintf "%smain argument: %s\n" ind (id_2str t.cstri_main)
  and s_ipars =
    Printf.sprintf "%sinteger arguments: { %s }\n"
      ind (gen_list_2str "" id_2str "," t.cstri_ipars)
  and s_ppars =
    Printf.sprintf "%spointer arguments: { %s }\n"
      ind (gen_list_2str "" id_2str "," t.cstri_ppars)
  and s_cstr =
    Printf.sprintf "%s{\n%s%s}\n" ind
      (cstr_2stri (ind^"  ") t.cstri_cstr) ind in
  Printf.sprintf "%s%s%s%s" s_main s_ipars s_ppars s_cstr
    
let cstr_segcall_2stri (ind: string) (t: cstr_segcall): string = 
  let s_src =
    Printf.sprintf "%ssource argument: %s\n" ind (id_2str t.cstrs_src)
  and s_sipars =
    Printf.sprintf "%ssource integer arguments: { %s }\n"
      ind (gen_list_2str "" id_2str "," t.cstrs_sipars)
  and s_cstrpars =
    Printf.sprintf "%ssource pointer arguments: { %s }\n"
      ind (gen_list_2str "" id_2str "," t.cstrs_sppars)
  and s_dst =
    Printf.sprintf "%sdestination argument: %s\n" ind (id_2str t.cstrs_dst)
  and s_dipars =
    Printf.sprintf "%sdest. integer arguments: { %s }\n"
      ind (gen_list_2str "" id_2str "," t.cstrs_dipars)
  and s_dppars =
    Printf.sprintf "%sdest. pointer arguments: { %s }\n"
      ind (gen_list_2str "" id_2str "," t.cstrs_dppars)
  and s_cstr =
    Printf.sprintf "%s{\n%s%s}\n"
      ind (cstr_2stri (ind^"  ") t.cstrs_cstr) ind in
  Printf.sprintf "%s%s%s%s%s%s%s" s_src s_sipars s_cstrpars 
    s_dst s_dipars s_dppars s_cstr

let id_mapping_2stri (ind: string) (map: id_mapping): string =
  let new_ind = ind^"  " in
  PMap.fold
    (fun n (nl, nr) s ->
      Printf.sprintf "%s%s%s -> (%s, %s)\n"
        s new_ind (id_2str n) (id_2str nl) (id_2str nr)) 
    map.nm_rev (ind^"Mapping:\n")

(* general tools *)
let get_node (n: id) (s: cstr): node = 
  try PMap.find n s.nodes
  with
  | Not_found -> 
      Log.info "in get_node.\n id: %s\ncstr: {\n%s\n}"
        (id_2str n) (cstr_2stri "\t" s);
      Log.fatal_exn "in get node, shall not happen" 
        
(* testing *)
let are_id_eq (x: id) (y: id) (s: cstr): bool = 
  x = y || 
  (try 
    let nx = PMap.find x s.nodes
    and ny = PMap.find y s.nodes in
    match nx.n_eqs, ny.n_eqs with
    | Ecl_id ix, Ecl_id iy -> ix = iy
    | Ecl_null, Ecl_null -> true
    | Ecl_null, Ecl_id _
    | Ecl_id _, Ecl_null -> false
  with | Not_found -> false)

let is_id_null (n: id) (t: cstr): bool = 
  let no = get_node n t in
  match no.n_eqs with
  | Ecl_null -> true
  | _ -> false

let is_id_not_null (n: id) (t: cstr): bool = 
  let no = get_node n t in
  no.n_not_null ||
  not (for_all_paths (fun p _ -> Regular_expr.has_empty p) no)
    
let are_destination_eq (x:destination) (y: destination) (t: cstr): bool =
  match x, y with
  | Pd_null, Pd_null -> true
  | Pd_id x, Pd_null | Pd_null, Pd_id x -> is_id_null x t
  | Pd_id x, Pd_id y -> are_id_eq x y t

let is_there_path (n: id) (p: path) (dst: destination) (t: cstr): bool = 
  let no = get_node n t in
  try
    let ldst = PMap.find p no.n_fw_paths in
    PSet.exists (fun d -> are_destination_eq dst d t) ldst
  with Not_found -> false

let for_all_node (f: id -> node -> bool) (t: cstr): bool =
  let rec aux nmap = 
    if PMap.is_empty nmap then true
    else
      let n, no = PMap.choose nmap in 
      if f n no then aux (PMap.remove n nmap)
      else false
  in aux t.nodes

let is_bot (s: cstr): bool = 
  PMap.fold
    (fun i ni b -> b || (is_id_null i s && is_id_not_null i s))
    s.nodes false

(* sanity checks *)
let sanity_check (mess: string) (s: cstr): unit = 
  if flag_debug_pl_sanity then
    Log.force "sanity check: %s [starting]" mess;
  (* check that all ids in id_free are less than id_up *)
  List.iter
    (fun id ->
      if id >= s.id_up then 
        Log.fatal_exn "%s: sanity check failed: free ids unsound" mess
    ) s.id_free;
  (* checks that all nodes belong to the env *)
  PMap.iter
    (fun id _ ->
      if List.mem id s.id_free || id>=s.id_up then
        Log.fatal_exn "%s: sanity check failed (1): %s not in the env"
          mess (id_2str id)
    ) s.nodes;
  (* checks that all nodes pointed by belong to the env *)
  PMap.iter
    (fun _ ->
      iter_fw_paths
        (fun _ dst ->
          match dst with 
          | Pd_null -> ()
          | Pd_id dst ->
              if List.mem dst s.id_free || dst >= s.id_up then
                Log.fatal_exn "%s: sanity check failed (2): %s not in the env"
                  mess (id_2str dst)
        )
    ) s.nodes;
  (* checks that all nodes in c_paths belong to the env *)
  PMap.iter
    (fun _ ->
      iter_c_paths 
        (fun c ->
          let ids_to_check = c_path_get_args c in
          PSet.iter
            (fun x -> 
              if List.mem x s.id_free || x>=s.id_up then
                Log.fatal_exn
                  "%s: sanity check failed (3): %s not in the env"
                  mess (id_2str x)
            ) ids_to_check
        )
    ) s.nodes;
  (* checks that all nodes in d_paths belong to the env *)
  PMap.iter
    (fun _ ->
      iter_d_paths 
        (fun d -> 
          let ids_to_check = d_path_get_args d in
          PSet.iter
            (fun x -> 
              if List.mem x s.id_free || x>=s.id_up then
                Log.fatal_exn
                  "%s: sanity check failed (4): %s not in the env"
                  mess (id_2str x)
            ) ids_to_check
        )
    ) s.nodes;
  (* check eq classes soundness *)
  IntMap.iter
    (fun i cl ->
      PSet.iter
        (fun id -> 
          if not (PMap.mem id s.nodes) then
            Log.fatal_exn
              "%s: sanity check failed: eq soundness, %s not found"
              mess (id_2str id);
          let n = PMap.find id s.nodes in
          if n.n_eqs <> Ecl_id i then
            Log.fatal_exn
              "%s: sanity check failed: eq soundness at %s (eq_cl: %i)"
              mess (id_2str id) i
        ) cl
    ) s.eq_class.cl;
  (* check null classes soundness *)
  PSet.iter
    (fun id -> 
      if not (PMap.mem id s.nodes) then
        Log.fatal_exn
          "%s: sanity check failed: null_eq soundness, %s not found"
          mess (id_2str id);
      let n = PMap.find id s.nodes in
      if n.n_eqs <> Ecl_null then
        Log.fatal_exn "%s: sanity check failed: null_eq soundness at %s"
          mess (id_2str id)
    ) s.eq_class.null_cl;
  (* checks backward information *)
  PMap.iter
    (fun id n ->
      iter_fw_paths
        (fun p pd ->
          match pd with 
          | Pd_null -> ()
          | Pd_id dst -> 
              let ndst =
                try PMap.find dst s.nodes
                with Not_found ->
                  Log.fatal_exn "%s: sanity check failed: %s not found"
                    mess (id_2str dst) in
              let bw =
                try PMap.find p ndst.n_bw_paths
                with Not_found ->
                  Log.fatal_exn
                    "%s: sanity check failed: no backward info at %s"
                    mess (id_2str dst) in
              if not (PSet.exists (id_eq id) bw) then
                Log.fatal_exn
                  "%s: sanity check failed: backward info at %s"
                  mess (id_2str dst)
        ) n
    ) s.nodes;
  if flag_debug_pl_sanity then
    Log.force "sanity check: %s [complete]" mess

(** utlilitary functions *)
let create_fresh_node (s: cstr): id * cstr = 
  if pl_do_sanity_check_before then 
    sanity_check "create_fresh_node" s;    
  let x, id_up, id_free =
    match s.id_free with
    | [] -> s.id_up, id_next s.id_up, []
    | x::id_free -> x, s.id_up, id_free in
  let eq_id, eq_class = eq_class_create_singl x s.eq_class in
  let nx: node = 
    { n_eqs        = eq_id;
      n_fw_paths   = PMap.empty;
      n_bw_paths   = PMap.empty;
      n_c_paths    = PSet.empty;
      n_bw_c_paths = PSet.empty;
      n_d_paths    = PSet.empty;
      n_bw_d_paths = PSet.empty;
      n_not_null   = false } in
  x, { nodes = PMap.add x nx s.nodes;
       eq_class;
       id_up = id_up;
       id_free = id_free }

let create_nfresh_nodes (n: int) (t: cstr): id list * cstr = 
  if pl_do_sanity_check_before then 
    sanity_check "create_nfresh_nodes" t; 
  let rec aux l_fresh_id n t = 
    match n, t.id_free with
    | 0, _ | _, [] -> l_fresh_id, n, t
    | _ ->
        let id, t = create_fresh_node t in
        aux (id::l_fresh_id) (n-1) t in
  (* first we take variable in id_free *)
  let l_fresh_id, n, t = aux [] n t in
  let rec aux l_fresh_id n t =
    if n = 0 then l_fresh_id, t
    else
      let eq_id, eq_cl = eq_class_create_singl (t.id_up+n-1) t.eq_class in
      let no = { n_eqs        = eq_id;
                 n_fw_paths   = PMap.empty;
                 n_bw_paths   = PMap.empty;
                 n_c_paths    = PSet.empty;
                 n_bw_c_paths = PSet.empty;
                 n_d_paths    = PSet.empty;
                 n_bw_d_paths = PSet.empty;
                 n_not_null   = false } in
      let t = { t with nodes = PMap.add (t.id_up+n-1) no t.nodes } in
      let t = { t with eq_class = eq_cl } in
      aux ((t.id_up+n-1)::l_fresh_id) (n-1) t in
  let l_fresh_id, t = aux l_fresh_id n t in
  l_fresh_id, { t with id_up = t.id_up+n }
    
let remove_node (x: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then 
    sanity_check (Printf.sprintf "remove: %s" (id_2str x)) t;    
  let nx = get_node x t in
  let t =
    fold_fw_paths
      (fun p dst t ->
        match dst with
        | Pd_null -> t
        | Pd_id dst -> 
            let ndst = get_node dst t in
            let ndst = remove_bw_paths p x ndst in
            let nodes = PMap.add dst ndst t.nodes in
            { t with nodes }
      ) nx t in
  let t =
    fold_bw_paths
      (fun p src t ->
        let nsrc = get_node src t in 
        let nsrc = remove_fw_paths p (Pd_id x) nsrc in
        let nodes = PMap.add src nsrc t.nodes in
        { t with nodes}
      ) nx t in
  (* remove c-paths whose x belong to *)
  let nodes =
    PSet.fold
      (fun y nodes ->
        let ny = PMap.find y nodes in
        let n_c_paths =
          PSet.filter
            (fun c -> not (PSet.mem x (c_path_get_args c))) ny.n_c_paths in
        let ny = { ny with n_c_paths } in
        PMap.add y ny nodes) nx.n_bw_c_paths t.nodes in
  (* upgrade c_bw_paths field *)
  let nodes =
    PMap.map
      (fun ny -> { ny with n_bw_c_paths = 
                   PSet.remove x ny.n_bw_c_paths }) nodes in 
  (* remove d-paths whose x belong to *)
  let nodes =
    PSet.fold
      (fun y nodes ->
        let ny = PMap.find y nodes in
        let n_d_paths =
          PSet.filter (fun d -> not (PSet.mem x (d_path_get_args d)))
            ny.n_d_paths in
        let ny = { ny with n_d_paths } in
        PMap.add y ny nodes) nx.n_bw_d_paths nodes in
  (* upgrade d_bw_paths field *)
  let nodes =
    PMap.map
      (fun ny -> { ny with n_bw_d_paths =
                   PSet.remove x ny.n_bw_d_paths }
      ) nodes in
  let nodes = PMap.remove x nodes in
  { nodes;
    eq_class = eq_class_remove nx.n_eqs x t.eq_class;
    id_up    = t.id_up;
    id_free  = x::t.id_free }

let add_null (x: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check "add_null" t;
  if is_id_null x t then t
  else
    let e = t.eq_class in
    let nx = get_node x t in
    let eqx = nx.n_eqs in
    let eqz, up_z, e = eq_class_fusion eqx Ecl_null e in
    let nodes =
      PSet.fold
        (fun z nodes ->
          let nz =
            try PMap.find z nodes
            with Not_found -> Log.fatal_exn "in add_null: shall not happen !" in
          let nz = { nz with n_eqs = eqz } in
          PMap.add z nz nodes
        ) up_z t.nodes in
    { nodes    = nodes;
      eq_class = e;
      id_up    = t.id_up;
      id_free  = t.id_free }
      
let add_not_null (x: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check "add_not_null" t;
  let nx = get_node x t in
  let nx = { nx with n_not_null = true } in
  { t with nodes = PMap.add x nx t.nodes }

let add_eq (x: id) (y: id) (t: cstr): cstr =
  if pl_do_sanity_check_before then
    sanity_check "add_eq" t;
  if are_id_eq x y t then t
  else
    let nx = get_node x t and ny = get_node y t in
    let eqx = nx.n_eqs and eqy = ny.n_eqs in
    let eqz, up_z, cl = eq_class_fusion eqx eqy t.eq_class in
    let nodes =
      PSet.fold
        (fun z nodes ->
          let nz =
            try PMap.find z nodes 
            with Not_found -> Log.fatal_exn "in add_eq: shall not happen !" in
          let nz = { nz with n_eqs = eqz } in
          PMap.add z nz nodes
        ) up_z t.nodes in
    { nodes    = nodes;
      eq_class = cl;
      id_up    = t.id_up;
      id_free  = t.id_free }

let add_dst_eq (dstl: destination) (dstr: destination): cstr -> cstr = 
  match dstl, dstr with
  | Pd_id i, Pd_id j -> add_eq i j  
  | Pd_null, Pd_id i | Pd_id i, Pd_null -> add_null i 
  | _ -> fun x -> x

let add_path (src: id) (p: path) (dst: destination) (t: cstr): cstr =
  if pl_do_sanity_check_before then 
    sanity_check "add_path" t;    
  let nsrc = get_node src t in
  let nsrc = add_fw_paths p dst nsrc in
  let nodes = PMap.add src nsrc t.nodes in
  let t = { t with nodes } in
  match dst with
  | Pd_null -> t
  | Pd_id dst -> 
      let ndst = get_node dst t in
      let ndst = add_bw_paths p src ndst in
      let nodes = PMap.add dst ndst t.nodes in
      { t with nodes }

let remove_path (src: id) (p: path) (dst: destination) (t: cstr): cstr = 
  if pl_do_sanity_check_before then 
    sanity_check "remove_path" t;    
  let nsrc = get_node src t in
  let nsrc = remove_fw_paths p dst nsrc in
  let nodes = PMap.add src nsrc t.nodes in
  let t = { t with nodes } in
  match dst with
  | Pd_null -> t
  | Pd_id dst -> 
      let ndst = get_node dst t in
      let ndst = remove_bw_paths p src ndst in
      let nodes = PMap.add dst ndst t.nodes in
      { t with nodes }

let add_c_path (n: id) (c: c_path) (t: cstr): cstr =
  if pl_do_sanity_check_before then 
    sanity_check "add_c_path" t;    
  let nn = get_node n t in
  let nn = { nn with n_c_paths = PSet.add c nn.n_c_paths } in
  let t = { t with nodes = PMap.add n nn t.nodes } in
  let bw_ids = c_path_get_args c in
  PSet.fold
    (fun x t -> 
      let nx = get_node x t in
      let nx = { nx with n_bw_c_paths = PSet.add n nx.n_bw_c_paths } in
      { t with nodes = PMap.add x nx t.nodes }
    ) bw_ids t

let remove_c_path (n: id) (c: c_path) (t: cstr): cstr = 
  if pl_do_sanity_check_before then 
    sanity_check "remove_c_path" t;    
  let no = get_node n t in
  let n_c_paths = PSet.filter (fun cp -> not (c_path_eq cp c)) no.n_c_paths in
  let no = { no with n_c_paths } in
  let nodes = PMap.add n no t.nodes in
  { t with nodes }

let add_d_path (n: id) (d: d_path) (t: cstr): cstr =
  if pl_do_sanity_check_before then 
    sanity_check "add_d_path" t;    
  let nn = get_node n t in
  let nn = { nn with n_d_paths = PSet.add d nn.n_d_paths } in
  let t = { t with nodes = PMap.add n nn t.nodes } in
  let bw_ids = d_path_get_args d in
  PSet.fold
    (fun x t -> 
      let nx = get_node x t in
      let nx = { nx with n_bw_d_paths = PSet.add n nx.n_bw_d_paths } in
      { t with nodes = PMap.add x nx t.nodes }
    ) bw_ids t

let remove_d_path (n: id) (d: d_path) (t: cstr): cstr = 
  if pl_do_sanity_check_before then 
    sanity_check "remove_d_path" t;    
  let no = get_node n t in
  let n_d_paths = PSet.filter (fun dp -> not (d_path_eq dp d)) no.n_d_paths in
  let no = { no with n_d_paths } in
  let nodes = PMap.add n no t.nodes in
  { t with nodes }

let find_paths (n: id) (p0: path) (t: cstr): destination PSet.t =
  let no = get_node n t in
  PMap.fold
    (fun p s_dst s ->
      if Regular_expr.is_le p p0 then PSet.union s_dst s else s
    ) no.n_fw_paths PSet.empty

let find_bw_paths (n: id) (p0: path) (t: cstr): id PSet.t =
  let no = get_node n t in
  PMap.fold
    (fun p s_src s ->
      if Regular_expr.is_le p p0 then PSet.union s_src s else s
    ) no.n_bw_paths PSet.empty

let find_d_path (n: id) (f: d_path -> bool) (t: cstr): d_path option =
  let no = get_node n t in
  fold_d_paths
    (fun d -> function
      | Some dr -> Some dr
      | None -> if f d then Some d else None
    ) no None

(* returns the equality class of NULL *)
let find_nulls (t: cstr): id PSet.t = 
  t.eq_class.null_cl
(* returns a map of (index -> equality class) *)
let find_eq_classes (t: cstr): id PSet.t IntMap.t = 
  t.eq_class.cl
