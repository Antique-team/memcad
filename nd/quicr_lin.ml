(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: quickr_lin.ml
 **       This domain features a collection of basic relations:
 **       - "linear" constraints (using disjoint union)
 **       - inclusion
 **       - membership
 **       - equality
 ** Xavier Rival, May 2015 *)

(** Importing the "set_lin" module from MemCAD as a stand-alone domain.
 ** This module is a bit experimental. We could explore splitting it into
 ** several modules, in particular using a functor representing equality
 ** relations and collapsing dimensions that are know equal (avoiding
 ** additional work in some transfer functions, but requiring some
 ** reduction work too ---not sure what side wins!) *)

(* Todo:
 * The integration of this module here is a bit work in progress, so I leave
 * some cleaning tasks for later:
 *  - moving the libraries into utility files
 *  - now type t has a single field; remove struct
 *  - add Format printers in the maps
 *  - move stuffs specific to set_lin in a separate module
 *  - do reduction on a SET of symbols about to be removed, and not just one
 * 
 * The functions below still have a very rudimentary implementation, that
 * should be improved:
 *  - meet
 *  - serialize
 *  - query
 *  - combine
 *)

open Lib
open Data_structures

module Log =
  Logger.Make(struct let section = "nd_quicl" and level = Log_level.DEBUG end)

(* Printing maps and sets *)
let pp_set_syms (c: string) (pp_sym: Format.formatter -> int -> unit)
    (ch: Format.formatter) (s: IntSet.t): unit =
  let _ =
    IntSet.fold
      (fun i b ->
        Format.fprintf ch "%s%a" (if b then "" else c) pp_sym i;
        false
      ) s true in
  ( )


(** Module abbrevs *)

module L = SETr.SymSing.Logic
module R = SETr.Rename


(** Abstract values *)

(* Linear constraints correspond to an equality of the form
 *     S = { x_0, x_1, ..., x_n } \uplus S_0 \uplus ... \uplus S_k
 *  - sl_elts is the set   x_0, x_1, ..., x_n
 *  - sl_sets is the set   S_0, S_1, ..., S_k *)
type set_lin =
    { sl_elts: IntSet.t; (* elements *)
      sl_sets: IntSet.t  (* sets *) }

(* Underlying type for constraints:
 *  - u_lin maps S to the linear constraint mentioned above, if any
 *     (we may have to authorize several constraints per variable
 *  - u_sub maps S to a set of sets S_0, ..., S_k known to be subsets of S
 *  - u_mem maps S to a set of elements x_0, ..., x_n known to belong to S
 *  - u_eqs maps S to a set of sets S_0, ..., S_k known to be equal to S *)
type u =
    { u_lin:   set_lin IntMap.t;  (* Si = a linear constraint (if any) *)
      u_sub:   IntSet.t IntMap.t; (* Si => set of subsets of Si *)
      u_mem:   IntSet.t IntMap.t; (* Si => set of elements *)
      u_eqs:   IntSet.t IntMap.t  (* Si => set of equal sets *) }

(* The type of abstract elements (bottom or non bottom) *)
type t = u option (* None if _|_, Some u if non bot constraints u *)

(* A straightforward lift operation *)
let lift (f: u -> u) (x: t): t =
  match x with
  | None -> x
  | Some u -> Some (f u)


(** Abstract domain interface types, and "initialization" *)

type ctx = unit
type sym = int
type cnstr = sym L.t
type output = cnstr
type query = sym L.q
let init () = ()


(** Error report and debugging *)

(* Main debug switch *)
let debug_module = true


(** Lattice elements *)

(* Bottom element (empty context) *)
let bottom (): t = None
let is_bottom () (x: t): bool = x = None

(* Top element (empty context) *)
let top (): t = Some { u_lin   = IntMap.empty;
                       u_sub   = IntMap.empty;
                       u_mem   = IntMap.empty;
                       u_eqs   = IntMap.empty }
let is_top () (x: t): bool =
  match x with
  | None -> false
  | Some u ->
      u.u_lin = IntMap.empty && u.u_sub = IntMap.empty
        && u.u_sub = IntMap.empty && u.u_eqs = IntMap.empty

(* Context management *)
let context (x: t) = ( )

(* Symbols that are constrained (only those that explicitely appear) *)
let symbols () (x: t): sym list =
  match x with
  | None -> [ ]
  | Some u ->
      let f = IntMap.fold (fun i s acc -> IntSet.add i (IntSet.union s acc)) in
      let acc = f u.u_sub (f u.u_mem (f u.u_eqs IntSet.empty)) in
      let acc =
        IntMap.fold
          (fun i sl acc ->
            IntSet.add i (IntSet.union (IntSet.union sl.sl_elts sl.sl_sets) acc)
          ) u.u_lin acc in
      IntSet.fold (fun i l -> i :: l) acc [ ]


(** Basic functions over set_lin *)

exception Lin_error of string (* Failure to preserve linearity *)

(* Empty (corresponds to empty set) *)
let sl_empty: set_lin =
  { sl_elts = IntSet.empty;
    sl_sets = IntSet.empty }
let sl_is_empty (sl: set_lin): bool =
  sl.sl_elts = IntSet.empty && sl.sl_sets = IntSet.empty
(* Other basic values (singleton, single set) *)
let sl_one_set (i: int) = { sl_empty with sl_sets = IntSet.singleton i }
let sl_one_elt (i: int) = { sl_empty with sl_elts = IntSet.singleton i }

(* Conversion to string *)
let pp_sl
    (pp_sym: Format.formatter -> sym -> unit)
    (ch: Format.formatter) (sl: set_lin): unit =
  if sl.sl_elts = IntSet.empty && sl.sl_sets = IntSet.empty then
    Format.fprintf ch "empty"
  else
    Format.fprintf ch "{ %a } + %a" (pp_set_syms ", " pp_sym) sl.sl_elts
      (pp_set_syms " + " pp_sym) sl.sl_sets

(* Equality of set constraints *)
let sl_eq c sl =
  IntSet.equal c.sl_elts sl.sl_elts && IntSet.equal c.sl_sets sl.sl_sets

(* Adding two linear combinations of sets *)
let sl_add (lin0: set_lin) (lin1: set_lin): set_lin =
  if IntSet.inter lin0.sl_elts lin1.sl_elts = IntSet.empty
      && IntSet.inter lin0.sl_sets lin1.sl_sets = IntSet.empty then
    { sl_elts = IntSet.union lin0.sl_elts lin1.sl_elts;
      sl_sets = IntSet.union lin0.sl_sets lin1.sl_sets }
  else raise (Lin_error "sl_add: non disjoint constraints")
(* Inclusion of set_lin *)
let sl_subset (sl0: set_lin) (sl1: set_lin): bool =
  IntSet.subset sl0.sl_elts sl1.sl_elts
    && IntSet.subset sl0.sl_sets sl1.sl_sets
(* Subtraction of set_lin *)
let sl_sub (sl0: set_lin) (sl1: set_lin): set_lin =
  if IntSet.subset sl1.sl_elts sl0.sl_elts
      && IntSet.subset sl1.sl_sets sl0.sl_sets then
    { sl_elts = IntSet.diff sl0.sl_elts sl1.sl_elts;
      sl_sets = IntSet.diff sl0.sl_sets sl1.sl_sets }
  else raise (Lin_error "sl_sub: non disjoint constraints")

(* Linearization of an expression into a set_lin *)
let linearize (ex: int L.e): set_lin option =
  let rec aux = function
    | L.Empty -> sl_empty
    | L.Sing i -> sl_one_elt i
    | L.Var i -> sl_one_set i
    | L.DisjUnion (e0, e1) -> sl_add (aux e0) (aux e1)
    | _ -> raise (Lin_error "unsupported construction") in
  try Some (aux ex) with Lin_error _ -> None


(** Pretty-printing *)

(* Internal and abstract state representations are fairly close
 * for this domain, hence we make just one pretty-printing function *)
let pp
    (pp_sym: Format.formatter -> sym -> unit) (* sym is int... *)
    (ch: Format.formatter) (x: t): unit =
  match x with
  | None -> Format.fprintf ch "BOT\n"
  | Some u ->
      IntMap.iter
        (fun i c -> Format.fprintf ch "%a = %a@\n" pp_sym i (pp_sl pp_sym) c)
        u.u_lin;
      IntMap.iter
        (fun i s ->
          if s != IntSet.empty && i <= IntSet.min_elt s then
            let s = IntSet.remove i s in
            let plur = if IntSet.cardinal s > 1 then "s" else "" in
            Format.fprintf ch "%a equal to set%s %a@\n" pp_sym i plur
              (pp_set_syms ", " pp_sym) s
        ) u.u_eqs;
      IntMap.iter
        (fun i s ->
          let plur = if IntSet.cardinal s > 1 then "s" else "" in
          Format.fprintf ch "%a contains set%s: %a@\n" pp_sym i plur
            (pp_set_syms ", " pp_sym) s
        ) u.u_sub;
      IntMap.iter
        (fun i s ->
          let plur = if IntSet.cardinal s > 1 then "s" else "" in
          Format.fprintf ch "%a contains element%s: %a@\n" pp_sym i plur
            (pp_set_syms ", " pp_sym) s
        ) u.u_mem

let pp_debug () = pp
let pp_print () = pp
let pp_sym ch i = Format.fprintf ch "%d" i


(** Manipulating constraints *)

(* Fast access to constraints *)
let u_get_sub (u: u) (i: int): IntSet.t = (* subsets of i *)
  try IntMap.find i u.u_sub with Not_found -> IntSet.empty
let u_get_mem (u: u) (i: int): IntSet.t = (* elements of i *)
  try IntMap.find i u.u_mem with Not_found -> IntSet.empty
let u_get_eqs (u: u) (i: int): IntSet.t = (* sets equal to *)
  try IntMap.find i u.u_eqs with Not_found -> IntSet.singleton i

(* Helper functions to add basic constraints *)
let u_add_inclusion (u: u) (i: int) (j: int): u = (* i included in j *)
  let osub = u_get_sub u j in
  { u with u_sub = IntMap.add j (IntSet.add i osub) u.u_sub }
let u_add_mem (u: u) (i: int) (j: int): u = (* i is an element of j *)
  let omem = u_get_mem u j in
  { u with u_mem = IntMap.add j (IntSet.add i omem) u.u_mem }
let u_add_eq (u: u) (i: int) (j: int): u = (* i = j *)
  let c = IntSet.union (u_get_eqs u i) (u_get_eqs u j) in
  { u with u_eqs = IntSet.fold (fun i -> IntMap.add i c) c u.u_eqs }
let u_add_lin (u: u) (i: int) (sl: set_lin): u = (* i = sl *)
  (* a bit of reduction: search of all other equalities to sl *)
  let u =
    IntMap.fold
      (fun j0 sl0 acc ->
        if sl_eq sl sl0 then u_add_eq u i j0
        else u
      ) u.u_lin u in
  if IntMap.mem i u.u_lin then
    Log.warn "u_add_lin: over-writing constraint";
  { u with u_lin = IntMap.add i sl u.u_lin }

(* Guard operator, adds a new constraint *)
let constrain () (c: cnstr): t -> t =
  let u_constrain (u: u): u =
    (* Basic constraints added using the utility functions:
     *  all constraints needed in the graph examples are supported,
     *  except the S0 = S1 \cup S2 (not \uplus), as I believe such
     *  constraints should just not arise here! *)
    match c with
    | L.In (i, L.Var j) ->
        u_add_mem u i j
    | L.Eq (L.Var i, L.Empty) | L.Eq (L.Empty, L.Var i) ->
        if IntMap.mem i u.u_lin then
          Log.warn "constrain: existing linear constraint";
        let cons = { sl_elts = IntSet.empty; sl_sets = IntSet.empty } in
        { u with u_lin = IntMap.add i cons u.u_lin }
    | L.Eq (L.Var i, L.Var j) ->
        u_add_eq u i j
    | L.Eq (L.Var i, L.DisjUnion (L.Var j, L.Var k))
    | L.Eq (L.DisjUnion (L.Var j, L.Var k), L.Var i) ->
        u_add_lin u i { sl_sets = IntSet.add j (IntSet.singleton k);
                        sl_elts = IntSet.empty }
    | L.Eq (L.Var i, L.Sing j) | L.Eq (L.Sing j, L.Var i)
    | L.Eq (L.Var i, L.DisjUnion (L.Empty, L.Sing j))
    | L.Eq (L.Var i, L.DisjUnion (L.Sing j, L.Empty)) ->
        u_add_lin u i { sl_sets = IntSet.empty;
                        sl_elts = IntSet.singleton j }
    | L.Eq (L.Var i, L.DisjUnion (L.Sing j, L.Var k)) ->
        u_add_lin u i { sl_sets = IntSet.singleton k;
                        sl_elts = IntSet.singleton j }
    | L.Eq (L.Var i, e) ->
        begin
          match linearize e with
          | Some lin -> u_add_lin u i lin
          | None ->
              Log.warn "constrain: linearization failed";
              u
        end
    | L.SubEq (L.Var i, L.Var j) ->
        u_add_inclusion u i j
    | _ ->
        (* otherwise, we just drop the constraint *)
        Log.info "constrain,ignored: %s" (L.to_string pp_sym c);
        u in
  lift u_constrain


(* Helper functions to check basic constraints *)
exception Stop of bool
(* a closure function: inputs Si, and returns all Sj found to be
 *  contained in Si, using equality and inclusion constraints *)
let closure_subsets (u: u) (i: int): IntSet.t =
  let add acc s =
    IntSet.fold
      (fun i (nvs, acc) ->
        if IntSet.mem i acc then nvs, acc
        else i :: nvs, IntSet.add i acc
      ) s ([ ], acc) in
  let rec aux acc s =
    let nvs, acc = add acc s in
    if nvs = [ ] then acc
    else
      let acc, next =
        List.fold_left
          (fun (old, n) j ->
            IntSet.add j old,
            IntSet.union (u_get_eqs u j) (IntSet.union (u_get_sub u j) n)
          ) (acc, IntSet.empty) nvs in
      aux acc next in
  aux IntSet.empty (IntSet.singleton i)
(* does u entail that i \in j ? *)
let u_sat_mem (u: u) i j =
  try
    if IntSet.mem i (u_get_mem u j) then raise (Stop true);
    (* look at sets equal to j, and gather their known elements *)
    let smems = closure_subsets u j in
    let elems =
      IntSet.fold
        (fun i acc -> IntSet.union (u_get_mem u i) acc) smems IntSet.empty in
    if IntSet.mem i elems then raise (Stop true);
    if IntSet.mem i (IntMap.find j u.u_lin).sl_elts then raise (Stop true);
    false
  with
  | Stop b -> b
  | Not_found -> false
(* does u entail i <= j ? (i subset of j) *)
let u_sat_sub (u: u) i j =
  let i0 = u_get_eqs u i and j0 = u_get_eqs u j in
  let jsubsets =
    IntSet.fold (fun jj acc -> IntSet.union acc (u_get_sub u jj)) j0
      IntSet.empty in
  IntSet.inter i0 jsubsets != IntSet.empty
(* does u entail that i in ex *)
let u_sat_mem_ex (u: u) i ex =
  let rec aux_mem = function
    | L.Empty -> false
    | L.Sing j -> i = j
    | L.Var j -> u_sat_mem u i j
    | L.DisjUnion (e0, e1) | L.Union (e0, e1) -> aux_mem e0 || aux_mem e1
    | _ -> false in
  if aux_mem ex then true
  else
    match linearize ex with
    | Some lin ->
        (* we look for sets that include this linearized expression,
         * and try to verify membership on them *)
        begin
          try
            IntMap.iter
              (fun j sl ->
                if sl_subset lin sl && u_sat_mem u i j then raise (Stop true)
              ) u.u_lin;
            false
          with Stop b -> b
        end
    | None -> false (* we give up *)
(* can we find a constraint that ensures i is empty ? *)
let u_has_empty_ctr (u: u) (i: int): bool =
  try
    let sl = IntMap.find i u.u_lin in
    sl.sl_elts = IntSet.empty && sl.sl_sets = IntSet.empty
  with Not_found -> false
(* is i empty ? *)
let u_sat_empty (u: u) i =
  IntSet.exists (fun i -> u_has_empty_ctr u i) (u_get_eqs u i)
(* does u entail i=j ? *)
let u_sat_eq (u: u) i j =
  IntSet.mem i (u_get_eqs u j) || IntSet.mem j (u_get_eqs u i)
(* does constraint "i=sl" exist in u ? *)
let u_sat_lin (u: u) i sl =
  try (* NB: precision can be improved by looking at set equalities *)
    let c = IntMap.find i u.u_lin in
    sl_eq c sl
  with Not_found ->
    if IntSet.is_empty sl.sl_elts then
      let sl_sets =
        IntSet.fold
          (fun i acc ->
            if u_sat_empty u i then acc
            else IntSet.add i acc
          ) sl.sl_sets IntSet.empty in
      if IntSet.cardinal sl_sets = 1 then
        u_sat_eq u (IntSet.choose sl_sets) i
      else false
    else false

(* Sat operator, checks whether a constraint is implied by an abstract state *)
let sat () (x: t) (c: cnstr): bool =
  match x with
  | None -> true (* any constraint valid under _|_ *)
  | Some u ->
      (* trying to support the same constraints as in guard *)
      match c with
      | L.In (i, ex) -> u_sat_mem_ex u i ex
      | L.Eq (L.Var i, L.Var j) -> u_sat_eq u i j
      | L.SubEq (L.Var i, L.Var j) -> u_sat_sub u i j
      | L.Eq (L.Var i, ex) | L.Eq (ex, L.Var i) ->
          begin
            match linearize ex with
              | None -> false
              | Some lin -> u_sat_lin u i lin
          end
      | _ -> false

let serialize () (x: t): output =
  Log.info "WARN: serialize will return default, imprecise result";
  L.True


(** Reduction *)

(* The functions below try to rewrite constraints about a symbol about to
 * be projected out, so as to preserved as much information as possible.
 * However, they were written for MemCAD where symbols are projected out
 * one by one, and a more efficient way would make these functions take
 * a set of symbols about to be removed. *)

(* Selection of the most general set_lin: (1) fewer elts, (2) fewer sets *)
let sl_more_gen (sl0: set_lin) (sl1: set_lin): set_lin =
  let default ( ) = sl1 (* a default, possibly unfortunate choice *) in
  let ce0 = IntSet.cardinal sl0.sl_elts
  and ce1 = IntSet.cardinal sl1.sl_elts in
  if ce0 < ce1 then sl0
  else if ce0 > ce1 then sl1
  else
    let cs0 = IntSet.cardinal sl0.sl_sets
    and cs1 = IntSet.cardinal sl1.sl_sets in
    if cs0 < cs1 then sl0
    else if cs0 > 0 then
      let m0 = IntSet.max_elt sl0.sl_sets
      and m1 = IntSet.max_elt sl1.sl_sets in
      if m0 > m1 then sl0
      else if m0 < m1 then sl1
      else default ( )
    else default ( )

(* Reduction of the linear part (replace a variable by lin expr if any) *)
let u_reduce_lin (setv: int) (u: u): u =
  if IntMap.mem setv u.u_lin then
    let lin0 = IntMap.find setv u.u_lin in
    let nlins =
      IntMap.fold
        (fun i lin acc ->
          if IntSet.mem setv lin.sl_sets then (* do the reduction *)
            let lin =
              sl_add lin0
                { lin with sl_sets = IntSet.remove setv lin.sl_sets } in
            IntMap.add i lin acc
          else (* nothing changes *) acc
        ) u.u_lin u.u_lin in
    { u with u_lin = nlins }
  else u

(* Replacing a setv by an equal setv if there is one *)
let u_reduce_eq (setv: int) (u: u): u =
  if IntMap.mem setv u.u_eqs then
    let others = IntSet.remove setv (IntMap.find setv u.u_eqs) in
    if IntSet.cardinal others > 0 then
      let setv0 = IntSet.min_elt others in
      (* replace setv by setv0 everywhere if possible *)
      let nlins =
        IntMap.fold
          (fun i l acc ->
            if IntSet.mem setv l.sl_sets then
              let s = IntSet.add setv0 (IntSet.remove setv l.sl_sets) in
              let nl = { l with sl_sets = s } in
              IntMap.add i nl acc
            else acc
          ) u.u_lin u.u_lin in
      let nsubs =
        IntMap.fold
          (fun i s acc ->
            if i = setv then
              let s = IntSet.union s (u_get_sub u setv0) in
              IntMap.add setv s acc
            else if IntSet.mem setv s then
              let s = IntSet.add setv0 (IntSet.remove setv s) in
              IntMap.add setv s acc
            else acc
          ) u.u_sub u.u_sub in
      let nmems =
        if IntMap.mem setv u.u_mem then
          let s = IntMap.find setv u.u_mem in
          let s0 = u_get_mem u setv0 in
          IntMap.add setv0 (IntSet.union s s0) u.u_mem
        else u.u_mem in
      let nlins =
        if IntMap.mem setv nlins then
          if IntMap.mem setv0 nlins then
            let sl0 = IntMap.find setv0 nlins
            and sl  = IntMap.find setv  nlins in
            Log.info "WARN, reduce: choice between two set_lin eqs";
            IntMap.add setv0 (sl_more_gen sl sl0) nlins
          else IntMap.add setv0 (IntMap.find setv nlins) nlins
        else nlins in
      { u with
        u_lin = nlins;
        u_sub = nsubs;
        u_mem = nmems; }
    else u
  else u

(* Group reduction *)
let u_reduce (syms: IntSet.t) (u: u): u =
  IntSet.fold (fun i u -> u_reduce_eq i (u_reduce_lin i u)) syms u


(** Manipulating symbols *)

(* Remove all constraints over a group of symbols in one shot;
 * function fv maps a sym to true if it should be dropped (as a set or
 * as an element), and to false otherwise *)
let u_drop_syms (fv: int -> bool) (u: u): u =
  let fset s = IntSet.exists fv s in
  let filter_set s =
    if fset s then IntSet.filter (fun i -> not (fv i)) s
    else s in
  let lin = (* remove constraints where a removed sym appears as an element *)
    IntMap.fold
      (fun i c acc ->
        let b = IntSet.exists fv c.sl_elts in
        if b then IntMap.remove i acc else acc
      ) u.u_lin u.u_lin in
  let lin, rem = (* do the same for set, but try to preserve constraints *)
    IntMap.fold
      (fun i c (acc, rem) ->
        if fv i || fset c.sl_sets then IntMap.remove i acc, (i,c) :: rem
        else acc, rem
      ) lin (lin, [ ]) in
  let lin =
    if List.length rem > 1 then
      let f (i,c) =
        (i,c), IntSet.cardinal c.sl_elts + IntSet.cardinal c.sl_sets in
      let rem = List.map f rem in
      let rem = List.sort (fun (_,i) (_,j) -> i - j) rem in
      let rem = List.map fst rem in
      match rem with
      | (i0, sl0) :: (i1, sl1) :: _ -> (* tries to preserves a constraint *)
          if sl_subset sl0 sl1 then
            let sl = sl_add (sl_sub sl1 sl0) (sl_one_set i0) in
            IntMap.add i1 sl lin
          else lin
      | _ -> lin
    else lin in
  let sub =
    IntMap.fold
      (fun i sub acc ->
        if fv i then acc
        else IntMap.add i (filter_set sub) acc
      ) u.u_sub IntMap.empty in
  let eqs =
    IntMap.fold
      (fun i s acc ->
        if fv i then IntMap.remove i acc
        else if fset s then
          let fs = filter_set s in
          if IntSet.cardinal fs = 1 && IntSet.mem i fs then
            IntMap.remove i acc
          else IntMap.add i fs acc
        else acc
      ) u.u_eqs u.u_eqs in
  let mem =
    IntMap.fold
      (fun i c acc ->
        let b = IntSet.exists fv c in
        if b then IntMap.remove i acc else acc
      ) u.u_mem u.u_mem in
  let mem = IntMap.filter (fun i _ -> not (fv i)) mem in
  { u_lin = lin;
    u_sub = sub;
    u_mem = mem;
    u_eqs = eqs }

(* Removal of all the constraints on a set of symbols *)
let forget () (l: sym list): t -> t =
  let u_forget (u: u): u =
    let svset = List.fold_left (fun a i -> IntSet.add i a) IntSet.empty l in
    (* do some reduction *)
    let u = u_reduce svset u in
    (* perform the removal *)
    u_drop_syms (fun i -> IntSet.mem i svset) u in
  lift u_forget

(* Renaming *)
(* Nb: this function is a lot simpler than the MemCAD one, since it does not
 *     also have to manage duplication and removal of symbols *)
let rename_symbols () (r: sym R.t): t -> t =
  let u_rename (u: u): u =
    let do_sym (i: int): int =
      try R.get r i
      with Not_found -> failwith "rename_symbols: do_sv fails" in
    let do_sym_set (s: IntSet.t): IntSet.t =
      IntSet.fold (fun i acc -> IntSet.add (do_sym i) acc) s IntSet.empty in
    let do_sym_set_map (ms: IntSet.t IntMap.t): IntSet.t IntMap.t =
      IntMap.fold (fun setv s -> IntMap.add (do_sym setv) (do_sym_set s))
        ms IntMap.empty in
    let do_set_lin (sl: set_lin): set_lin =
      { sl_elts  =  do_sym_set sl.sl_elts;
        sl_sets  =  do_sym_set sl.sl_sets } in
    let lin =
      IntMap.fold (fun setv sl -> IntMap.add (do_sym setv) (do_set_lin sl))
        u.u_lin IntMap.empty in
    { u_lin = lin;
      u_mem = do_sym_set_map u.u_mem;
      u_sub = do_sym_set_map u.u_sub;
      u_eqs = do_sym_set_map u.u_eqs } in
  lift u_rename


(** Lattice binary operations *)

(* Join returns an abstract over-approx of the lub *)
let join () (x0: t) (x1: t): t =
  let u_lub (u0: u) (u1: u): u =
    (* A useful generalization:
     *   (S0 = S1 /\ S2 = empty) \/ (S0 = {x} + S1 /\ S2 = {x})
     *           = (S0 = S2 + S1)
     * To do it, we first compute singletons in both sides
     * Then, we compute lists of generalized constraints
     *
     * List of equalities that could be added *)
    let generalize_sngs (u: u): (int * set_lin) list =
      (* singletons: set => { elt } *)
      let compute_singletons (u: u): int IntMap.t * set_lin IntMap.t =
        IntMap.fold
          (fun i sl (acc, rem) ->
            if sl.sl_sets = IntSet.empty
                && IntSet.cardinal sl.sl_elts = 1 then
              IntMap.add (IntSet.min_elt sl.sl_elts) i acc,
              IntMap.remove i rem
            else acc, rem
          ) u.u_lin (IntMap.empty, u.u_lin) in
      let sngs, rem = compute_singletons u in
      let l =
        IntMap.fold
          (fun i sl acc ->
            if IntSet.cardinal sl.sl_elts = 1 then
              let x = IntSet.min_elt sl.sl_elts in
              try
                let j = IntMap.find x sngs in
                (i, { sl_elts = IntSet.remove x sl.sl_elts;
                      sl_sets = IntSet.add j sl.sl_sets; } ) :: acc
              with Not_found -> acc
            else acc
          ) rem [ ] in
      if debug_module then
        Log.debug "reduced constraints: %d" (List.length l);
      l in
    let compute_emptys (u: u) =
      IntMap.fold
        (fun i sl acc -> if sl_is_empty sl then IntSet.add i acc else acc)
        u.u_lin IntSet.empty in
    let gen0 = generalize_sngs u0 and gen1 = generalize_sngs u1 in
    let emp0 = compute_emptys u0 and emp1 = compute_emptys u1 in
    (* generalized equalities of set a, emptys of set b, element of side b *)
    let generalize (gena: (int * set_lin) list) (empb: IntSet.t) (ub: u) =
      List.fold_left
        (fun acc (i, sl) ->
          if sl.sl_elts = IntSet.empty then
            let rec_sets =
              IntSet.fold
                (fun i acc ->
                  if IntSet.mem i empb then IntSet.remove i acc else acc
                ) sl.sl_sets sl.sl_sets in
            if IntSet.cardinal rec_sets = 1 then
              let x = IntSet.min_elt rec_sets in
              (* means we have equality x = i *)
              let b = u_sat_eq ub i x in
              if debug_module then
                Log.debug "suggests equality S%d = S%d => %b" i x b;
              (i, sl) :: acc
            else acc
          else acc
        ) [ ] gena in
    let lineqs_to_add = generalize gen0 emp1 u1 @ generalize gen1 emp0 u0 in
    let lin =
      IntMap.fold
        (fun i sl0 acc ->
          try
            let sl1 = IntMap.find i u1.u_lin in
            if sl_eq sl0 sl1 then IntMap.add i sl0 acc else acc
          with Not_found -> acc
        ) u0.u_lin IntMap.empty in
    let lin =
      List.fold_left
        (fun acc (i, sl) ->
          if IntMap.mem i acc then
            failwith "join: cannot add two lin constraints for a same variable!"
          else IntMap.add i sl acc
        ) lin lineqs_to_add in
    let lin =
      IntMap.fold
        (fun i sl acc ->
          if not (IntMap.mem i lin) && u_sat_lin u0 i sl then
            IntMap.add i sl acc
          else acc
        ) u1.u_lin lin in
    let eqs =
      IntMap.fold
        (fun i eqs0 acc ->
          let eqs = IntSet.inter eqs0 (u_get_eqs u1 i) in
          if IntSet.cardinal eqs <= 1 then acc (* only i ! *)
          else IntMap.add i eqs acc
        ) u0.u_eqs IntMap.empty in
    let mem =
      IntMap.fold
        (fun i mem0 acc ->
          let mem = IntSet.inter mem0 (u_get_mem u1 i) in
          if mem = IntSet.empty then acc
          else IntMap.add i mem acc
        ) u0.u_mem IntMap.empty in
    let sub =
      IntMap.fold
        (fun i sub0 acc ->
          let sub = IntSet.inter sub0 (u_get_sub u1 i) in
          if sub = IntSet.empty then acc
          else IntMap.add i sub acc
        ) u0.u_sub IntMap.empty in
    { u_lin = lin;
      u_eqs = eqs;
      u_mem = mem;
      u_sub = sub } in
  match x0, x1 with
  | None, _ -> x1
  | _, None -> x0
  | Some u0, Some u1 -> Some (u_lub u0 u1)

(* Join also acts as a widening *)
let widening (): t -> t -> t = join ()

(* Intersection *)
let meet () (x0: t) (x1: t): t =
  Log.info "WARN: meet will return default, imprecise result (1st arg)";
  x0

(* Inclusion checking *)
let le () (x0: t) (x1: t): bool =
  let module M = struct exception Abort end in
  (* are all constraints of u1 true in u0 ? *)
  let u_is_le (u0: u) (u1: u): bool =
    try
      IntMap.iter
        (fun i sl1 ->
          if not (sl_eq sl1 (IntMap.find i u0.u_lin)) then raise M.Abort
        ) u1.u_lin;
      IntMap.iter
        (fun i elts1 ->
          if not (IntSet.subset elts1 (u_get_mem u0 i)) then raise M.Abort
        ) u1.u_mem;
      IntMap.iter
        (fun i sub1 ->
          if not (IntSet.subset sub1 (u_get_sub u0 i)) then raise M.Abort
        ) u1.u_sub;
      IntMap.iter
        (fun i eqs1 ->
          if not (IntSet.subset eqs1 (u_get_eqs u0 i)) then raise M.Abort
        ) u1.u_eqs;
      true
    with
    | Not_found -> false
    | M.Abort -> false in
  match x0, x1 with
  | None, _ -> true
  | Some _, None -> false
  | Some u0, Some u1 -> u_is_le u0 u1


(** Interface for reduction *)

(* For now, this domain still offers no facility for reduction *)
let query () (x: t): query =
  Log.info "WARN: query will return default, imprecise result";
  { L.get_eqs     = (fun ( ) -> [ ]);
    L.get_eqs_sym = (fun _ -> [ ]); }
let combine () (q: query) (x: t) =
  Log.info "WARN: combine will return default, imprecise result";
  x
