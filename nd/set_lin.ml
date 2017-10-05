(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: set_lin.ml
 **       An experiment around the set domain
 ** Xavier Rival, Huisong Li, 2015/03/09 *)
open Data_structures
open Lib

open Nd_sig
open Set_sig
open Svenv_sig

open Nd_utils
open Set_utils


(** Error handling *)
module Log =
  Logger.Make(struct let section = "s_lin___" and level = Log_level.DEBUG end)

(* Local debugging *)
let debug_module = true

(* Future improvements:
 *  - set up another version of this domain, with several lin
 *    constraints per SETV
 *)

type sv = int

module Set_lin =
  (struct
    let module_name = "set_lin"
    let config_2str (): string =
      "" (* leaf module *)

    (** Type of abstract values *)

    (* Linear constraints correspond to an equality of the form
     *     S = { x_0, x_1, ..., x_n } \uplus S_0 \uplus ... \uplus S_k
     * sl_elts is the set of SVs        x_0, x_1, ..., x_n
     * sl_sets is the set of SETVs      S_0, S_1, ..., S_k             *)
    type set_lin =
        { sl_elts: IntSet.t; (* elements *)
          sl_sets: IntSet.t  (* sets *) }

    (* Underlying type for constraints:
     *  u_lin maps S to the linear constraint mentioned above, if any
     *                  (at most one lin constraint per SETV)
     *  u_sub maps S to a set of sets S_0, ..., S_k known to be subsets of S
     *  u_mem maps S to a set of elements x_0, ..., x_n known to belong to S
     *  u_eqs maps S to a set of sets S_0, ..., S_k known to be equal to S 
     *)
    type u =
        { u_lin:   set_lin IntMap.t;  (* Si = a linear constraint (if any) *)
          u_sub:   IntSet.t IntMap.t; (* Si => set of subsets of Si *)
          u_mem:   IntSet.t IntMap.t; (* Si => set of elements *)
          u_eqs:   IntSet.t IntMap.t  (* Si => set of equal sets *) }

    (* The type of abstract elements (bottom or non bottom) *)
    type t =
        { t_t:     u option; (* None if _|_, Some u if non bot constraints u *)
          t_roots: IntSet.t; (* set of root set variables *) }


    (** Printing *)
    let gen_set_2str (c: string) (f: int -> string) (s: IntSet.t): string =
      let _, str =
        (IntSet.fold
           (fun i (b, acc) ->
             false, Printf.sprintf "%s%s%s" acc (if b then "" else c) (f i)
           ) s (true, "")) in
      str
    let sv_2str (sn: string IntMap.t) (sv: int): string =
      try IntMap.find sv sn with Not_found -> Printf.sprintf "N[%d]" sv
    let set_setv_2str = gen_set_2str ", " (Printf.sprintf "S[%d]")
    let set_sv_2str (sn: string IntMap.t) (s: IntSet.t): string =
      gen_set_2str ", " (sv_2str sn) s


    (** Some basic functions over set_lin *)
    (* Failure to preserve linearity *)
    exception Lin_error of string
    (* Basic values *)
    let sl_empty: set_lin =
      { sl_elts = IntSet.empty;
        sl_sets = IntSet.empty }
    let sl_one_set (i: int) = { sl_empty with sl_sets = IntSet.singleton i }
    let sl_one_elt (i: int) = { sl_empty with sl_elts = IntSet.singleton i }
    (* Empty *)
    let sl_is_empty (sl: set_lin): bool =
      sl.sl_elts = IntSet.empty && sl.sl_sets = IntSet.empty
    (* Display *)
    let sl_2str (sn: string IntMap.t) (sl: set_lin): string =
      let lin_setv_2str = gen_set_2str " + " (Printf.sprintf "S[%d]") in
      if sl.sl_elts = IntSet.empty && sl.sl_sets = IntSet.empty then
        Printf.sprintf " = empty\n"
      else
        Printf.sprintf " = { %s } + %s\n" (set_sv_2str sn sl.sl_elts)
          (lin_setv_2str sl.sl_sets)
    (* Equality of set constraints *)
    let sl_eq c sl =
      IntSet.equal c.sl_elts sl.sl_elts && IntSet.equal c.sl_sets sl.sl_sets
    (* Disjoint union of two set_lin *)
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
    let linearize (ex: set_expr): set_lin option =
      let rec aux = function
        | S_empty -> sl_empty
        | S_node i -> sl_one_elt i
        | S_var i -> sl_one_set i
        | S_union (_, _) -> raise (Lin_error "union")
        | S_uplus (e0, e1) -> sl_add (aux e0) (aux e1) in
      try Some (aux ex) with Lin_error _ -> None
    (* Selection of the most general set_lin (to select which one to drop):
     *  (1) fewer elts;
     *  (2) fewer sets;
     *  (3) higher max SETV (this is a bit a random choice)
     *  (4) second argument if none of the above applies *)
    let sl_more_gen (sl0: set_lin) (sl1: set_lin): set_lin =
      let default ( ) = Log.warn "bad case"; sl1 in
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


    (** General utility functions *)

    (* map over the option type encoding bottom / non bottom *)
    let t_map (f: u -> u) (t: t): t =
      match t.t_t with
      | None -> t
      | Some u -> { t with t_t = Some (f u) }

    (* Empty element *)
    let empty (uo: u option): t = (* corresponds to top in fact *)
      { t_t     = uo;
        t_roots = IntSet.empty; }

    (* Remove all constraints over a group of SVs in one shot;
     * function f maps a symbolic variable to true if it should be dropped,
     * and to false otherwise. *)
    let drop_symb_svs (f: int -> bool) (x: t): t =
      let find_eq set_lin c ele_sets i =
        let m, l = IntMap.fold (fun key lin (accm, accs) ->
            if key <> i && IntSet.subset lin.sl_elts c.sl_elts
               && IntSet.subset lin.sl_sets c.sl_sets &&
               IntSet.inter lin.sl_elts ele_sets <> IntSet.empty
            then
              IntMap.add key lin accm,
              IntSet.union accs lin.sl_elts
            else
              accm, accs
          ) set_lin (IntMap.empty, IntSet.empty) in
        if IntSet.subset ele_sets l then Some m else None in
      let replace map_eq set_lin elts =
        let sl_sets, sl_elts, elts =
          IntMap.fold
            (fun key lin (accs, acce, acct) ->
              if IntSet.subset lin.sl_sets accs
                  && IntSet.subset lin.sl_elts acce
              then
                IntSet.add key (IntSet.diff accs lin.sl_sets),
                IntSet.diff acce lin.sl_elts,
                IntSet.diff acct lin.sl_elts
              else accs, acce, acct
            ) map_eq (set_lin.sl_sets, set_lin.sl_elts, elts) in
        if elts = IntSet.empty then
          Some { sl_elts = sl_elts;
                 sl_sets = sl_sets }
        else None in
      match x.t_t with
      | None -> x
      | Some u ->
          let lin =
            IntMap.fold
              (fun i c acc ->
                let b = IntSet.exists f c.sl_elts in
                if b then
                  let elts = IntSet.filter f c.sl_elts in
                  let m = find_eq u.u_lin c elts i in
                  match m with
                  | None -> IntMap.remove i acc
                  | Some map ->
                      match replace map c elts with
                      | Some c ->  IntMap.add i c acc
                      | None -> IntMap.remove i acc
                else acc
              ) u.u_lin u.u_lin in
          let mem =
            IntMap.fold
              (fun i c acc ->
                let nc = IntSet.filter (fun j -> not (f j)) c in
                if nc == c then acc else IntMap.add i nc acc
              ) u.u_mem u.u_mem in
          { x with t_t = Some { u with u_lin = lin; u_mem = mem } }

    (* Remove all constraints over a group of SETVs in one shot;
     * function fv maps a SETV to true if it should be dropped, and to false
     * otherwise *)
    let drop_setvs (fv: int -> bool) (x: t): t =
      let fset s = IntSet.exists fv s in
      let filter_set s = IntSet.filter (fun i -> not (fv i)) s in
      match x.t_t with
      | None -> x
      | Some u ->
          (* for the lin part, we try to recover some constraints *)
          let lin, rem =
            IntMap.fold
              (fun i c (acc, rem) ->
                if fv i || fset c.sl_sets then IntMap.remove i acc, (i,c) :: rem
                else acc, rem
              ) u.u_lin (u.u_lin, [ ]) in
          let lin =
            if List.length rem > 1 then
              let f (i,c) =
                (i,c), IntSet.cardinal c.sl_elts + IntSet.cardinal c.sl_sets in
              let rem = List.map f rem in
              let rem = List.sort (fun (_,i) (_,j) -> i - j) rem in
              let rem = List.map fst rem in
              match rem with
              | (i0, sl0) :: (i1, sl1) :: _ -> (* tries to save a constraint *)
                  if not (fv i1) && sl_subset sl0 sl1 then
                    let sl = sl_add (sl_sub sl1 sl0) (sl_one_set i0) in
                    if debug_module then
                      Log.debug "producing: %d :> %s" i1
                        (sl_2str IntMap.empty sl);
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
                else
                  let fs = filter_set s in
                  if IntSet.cardinal fs = 1 && IntSet.mem i fs then
                    IntMap.remove i acc
                  else IntMap.add i fs acc
              ) u.u_eqs u.u_eqs in
          let mem = IntMap.filter (fun i _ -> not (fv i)) u.u_mem in
          { x with t_t = Some { u_lin = lin;
                                u_sub = sub;
                                u_mem = mem;
                                u_eqs = eqs } }

    (* Topification *)
    let topify (msg: string) (t: t): t =
      let cons =
        match t.t_t with
        | None -> None
        | Some u ->
            Log.warn "%s" msg;
            Some { u_lin = IntMap.empty;
                   u_sub = IntMap.empty;
                   u_mem = IntMap.empty;
                   u_eqs = IntMap.empty } in
      { t with t_t = cons }

    (* Is an abstract value top (empty of constraints);
     * this is useful to diagnose precision losses *)
    let u_is_top (u: u): bool =
      u.u_lin = IntMap.empty && u.u_sub = IntMap.empty
        && u.u_mem = IntMap.empty && u.u_eqs = IntMap.empty
    let is_top (t: t): bool =
      match t.t_t with
      | None -> false
      | Some u -> u_is_top u

    (* Fast access to constraints *)
    let u_get_sub (u: u) (i: int): IntSet.t = (* subsets of i *)
      try IntMap.find i u.u_sub with Not_found -> IntSet.empty
    let u_get_mem (u: u) (i: int): IntSet.t = (* elements of i *)
      try IntMap.find i u.u_mem with Not_found -> IntSet.empty
    let u_get_eqs (u: u) (i: int): IntSet.t = (* sets equal to i *)
      try IntMap.find i u.u_eqs with Not_found -> IntSet.singleton i

    (* Adding some constraints *)
    (* Possible improvement: add some reduction here (none for now) *)
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
      if IntMap.mem i u.u_lin then Log.warn "over-writing constraint";
      { u with u_lin = IntMap.add i sl u.u_lin }

    (* Checking whether an abstract value entails some constraint *)
    exception Stop of bool
    (* a closure function: inputs Si, and returns all Sj found to be
     *  contained in Si, using equality and inclusion constraints *)
    let closure_subsets (u: u) (i: int): IntSet.t =
      let add acc s = IntSet.diff s acc, IntSet.union s acc in
      let rec aux acc s =
        let nvs, acc = add acc s in
        if nvs = IntSet.empty then acc
        else
          let acc, next =
            IntSet.fold
              (fun j (old, n) ->
                IntSet.add j old,
                IntSet.union (u_get_eqs u j) (IntSet.union (u_get_sub u j) n)
              ) nvs (acc, IntSet.empty) in
          aux acc next in
      aux IntSet.empty (IntSet.singleton i)
    (* does u entail that i \in j ? *)
    let u_sat_mem (u: u) i j =
      if debug_module then
        Log.debug "looking for membership(N[%d] in S[%d])" i j;
      try
        if IntSet.mem i (u_get_mem u j) then raise (Stop true);
        (* look at sets equal to j, and gather their known elements *)
        let smems = closure_subsets u j in
        if debug_module then
          Log.debug "subsets: %s" (intset_2str smems);
        IntSet.iter
          (fun j -> if IntSet.mem i (u_get_mem u j) then raise (Stop true))
          smems;
        if IntSet.mem i (IntMap.find j u.u_lin).sl_elts then raise (Stop true);
        false
      with
      | Stop b -> b
      | Not_found -> false
    (* can we find a constraint that ensures i is empty ? *)
    let u_has_empty_ctr (u: u) (i: int): bool =
      try
        let sl = IntMap.find i u.u_lin in
        sl.sl_elts = IntSet.empty && sl.sl_sets = IntSet.empty
      with Not_found -> false
    (* is i empty ? *)
    let u_sat_empty (u: u) i =
      IntSet.fold (fun i acc -> acc || u_has_empty_ctr u i)
        (u_get_eqs u i) false
    (* does u entail i=j ? *)
    let u_sat_eq (u: u) i j =
      IntSet.mem i (u_get_eqs u j) || IntSet.mem j (u_get_eqs u i)
    (* does constraint "i=sl" exist in u ? *)
    let u_sat_lin (u: u) i sl =
      try (* Possible improvement: utilize set equality constraints *)
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
        | S_empty -> false
        | S_node j -> i = j
        | S_var j -> u_sat_mem u i j
        | S_uplus (e0, e1) | S_union (e0, e1) -> aux_mem e0 || aux_mem e1 in
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
                    if sl_subset lin sl && u_sat_mem u i j then
                      raise (Stop true)
                  ) u.u_lin;
                false
              with Stop b -> b
            end
        | None -> false (* we give up *)


    (** Lattice elements *)

    (* Bottom element (empty context) *)
    let bot: t = empty None
    let is_bot (x: t): bool = x.t_t = None

    (* Top element (empty context) *)
    let top: t = empty (Some { u_lin   = IntMap.empty;
                               u_sub   = IntMap.empty;
                               u_mem   = IntMap.empty;
                               u_eqs   = IntMap.empty })

    (* Pretty-printing, with indentation *)
    let t_2stri (sn: string IntMap.t) (ind: string) (t: t): string =
      match t.t_t with
      | None -> Printf.sprintf "%sBOT\n" ind
      | Some u ->
          let lin_setv_2str = gen_set_2str " + " (Printf.sprintf "S[%d]") in
          let acc =
            IntMap.fold
              (fun i c acc ->
                if c.sl_elts = IntSet.empty && c.sl_sets = IntSet.empty then
                  Printf.sprintf "%s%sS[%d] = empty\n" acc ind i
                else
                  Printf.sprintf "%s%sS[%d] = { %s } + %s\n" acc ind i
                    (set_sv_2str sn c.sl_elts) (lin_setv_2str c.sl_sets)
              ) u.u_lin "" in
          let acc =
            IntMap.fold
              (fun i s acc ->
                if s = IntSet.empty || i > IntSet.min_elt s then acc
                else
                  let s = IntSet.remove i s in
                  let plur = if IntSet.cardinal s > 1 then "s" else "" in
                  Printf.sprintf "%s%sS[%d] equal to set%s %s\n" acc ind i
                    plur (set_setv_2str s)
              ) u.u_eqs acc in
          let acc =
            IntMap.fold
              (fun i s acc ->
                let plur = if IntSet.cardinal s > 1 then "s" else "" in
                Printf.sprintf "%s%sS[%d] contains set%s: %s\n" acc ind i
                  plur (set_setv_2str s)
              ) u.u_sub acc in
          IntMap.fold
            (fun i s acc ->
              let plur = if IntSet.cardinal s > 1 then "s" else "" in
              Printf.sprintf "%s%sS[%d] contains element%s: %s\n" acc ind i
                plur (set_sv_2str sn s)
            ) u.u_mem acc


    (** A bit of reduction, for internal use only *)
    (* Notes:
     *  - we would need less reduction with an equality functor
     *  - we could share code with iterators
     *)
    (* Reduction of the linear part (replace a variable by lin expr if any) *)
    let t_reduce_lin (setv: int) (t: t): t =
      let u_aux (u: u): u =
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
        else u in
      t_map u_aux t
    (* Replacing a SETV by an equal SETV if there is one *)
    let t_reduce_eq (setv: int) (t: t): t =
      let u_aux (u: u): u =
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
                  Log.warn "choice between two set_lin equalities";
                  IntMap.add setv0 (sl_more_gen sl sl0) nlins
                else IntMap.add setv0 (IntMap.find setv nlins) nlins
              else nlins in
            { u with
              u_lin = nlins;
              u_sub = nsubs;
              u_mem = nmems; }
          else u
        else u in
      t_map u_aux t


    (** Management of symbolic variables *)

    (* For sanity check *)
    let check_nodes (s: IntSet.t) (x: t): bool = Log.todo_exn "check_nodes"

    (* Symbolic variables *)
    let sv_add (sv: sv) (t: t): int * t = sv, t
    let sv_rem (sv: sv) (t: t): t =
      drop_symb_svs ((=) sv) t

    (* check if a set var root *)
    let setv_is_root (setv: sv) (t: t): bool =
      IntSet.mem setv t.t_roots

    (* collect root set variables *)
    let setv_col_root (t: t): IntSet.t = t.t_roots

    (* Set variables *)
    let setv_add ?(root: bool = false) ?(kind: set_par_type option = None)
        ?(name: string option = None) (setv: int) (t: t): t =
      { t with
        t_roots = if root then IntSet.add setv t.t_roots else t.t_roots }
    let setv_rem (setv: int) (t: t): t =
      (* attempts to do some reduction, and removes *)
      if debug_module then
        Log.debug "removing setv S[%d] in\n%s" setv
          (t_2stri IntMap.empty "  " t);
      let t = t_reduce_lin setv t in
      let t = t_reduce_eq setv t in
      if debug_module then
        Log.debug "reduction done:\n%s"
          (t_2stri IntMap.empty "  " t);
      let t = drop_setvs ((=) setv) t in
      let t = { t with t_roots = IntSet.remove setv t.t_roots } in
      if debug_module then
        Log.debug "removed setv S[%d]:\n%s" setv
          (t_2stri IntMap.empty "  " t);
      t


    (** Comparison and join operators *)

    (* Comparison *)
    exception Abort
    (* are all constraints of u1 true in u0 ? *)
    let u_is_le (u0: u) (u1: u): bool =
      (* Possible improvements:
       *  - do some reduction before attempting is_le;
       *  - utilize the sat functions (they are a bit more clever) *)
      try
        IntMap.iter
          (fun i sl1 ->
            if not (sl_eq sl1 (IntMap.find i u0.u_lin)) then raise Abort
          ) u1.u_lin;
        IntMap.iter
          (fun i elts1 ->
            if not (IntSet.subset elts1 (u_get_mem u0 i)) then raise Abort
          ) u1.u_mem;
        IntMap.iter
          (fun i sub1 ->
            if not (IntSet.subset sub1 (u_get_sub u0 i)) then raise Abort
          ) u1.u_sub;
        IntMap.iter
          (fun i eqs1 ->
            if not (IntSet.subset eqs1 (u_get_eqs u0 i)) then raise Abort
          ) u1.u_eqs;
        true
      with
      | Not_found -> false
      | Abort -> false
      
    let is_le (t0: t) (t1: t): bool =
      if debug_module then
        Log.debug "Calling set inclusion on:\n%sand:\n%s"
          (t_2stri IntMap.empty "   " t0) (t_2stri IntMap.empty "   " t1);
      match t0.t_t, t1.t_t with
      | None, _ -> true
      | Some _, None -> false
      | Some u0, Some u1 -> u_is_le u0 u1

    (* Lower upper bound *)
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
        let compute_singletons (u: u): (int, int) Bi_fun.t * set_lin IntMap.t =
          IntMap.fold
            (fun i sl (acc, rem) ->
              if sl.sl_sets = IntSet.empty
                  && IntSet.cardinal sl.sl_elts = 1 then
                Bi_fun.add i (IntSet.min_elt sl.sl_elts) acc,
                IntMap.remove i rem
              else acc, rem
            ) u.u_lin (Bi_fun.empty, u.u_lin) in
        let sngs, rem = compute_singletons u in
        let l =
          IntMap.fold
            (fun i sl acc ->
              if IntSet.cardinal sl.sl_elts = 1 then
                let x = IntSet.min_elt sl.sl_elts in
                match Bi_fun.inverse_opt x sngs with
                | None -> acc
                | Some j -> (i, { sl_elts = IntSet.remove x sl.sl_elts;
                                  sl_sets = IntSet.add j sl.sl_sets; } ) :: acc
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
              (* compute the difference or intersection of two set expression 
               *  that equal to a same setvariable, as example, let
               *  sl0 = E + X+ {\alpha} , sl1 = F + X + {\beta},
               *  then, lin0 = E + {\alpha}, lin1 = F + {\beta},
               *  lin_r = X *)
              let f_com f sl sr =
                { sl_elts = f sl.sl_elts sr.sl_elts;
                  sl_sets = f sl.sl_sets sr.sl_sets } in
              let lin0 = f_com IntSet.diff sl0 sl1 in
              let lin1 = f_com IntSet.diff sl1 sl0 in
              let lin_r = f_com IntSet.inter sl1 sl0 in
              (* deal with the difference part: as example, lin0 = E+{\alpha},
               * lin1 = F + {\beta}, then, if u1 => E = {\beta}, we can reduce
               * lin0 = {\alpha}, lin1 = F, lin_r = X + E *)
              let reduce_diff l0 l1 l_r =
                IntSet.fold
                  (fun s (acc0, acc1, accr) ->
                    try
                      let ls = IntMap.find s u1.u_lin in
                      if IntSet.subset ls.sl_elts acc1.sl_elts &&
                        IntSet.subset ls.sl_sets acc1.sl_sets then
                        { acc0 with sl_sets = IntSet.remove s acc0.sl_sets },
                        f_com IntSet.diff acc1 ls,
                        { accr with sl_sets = IntSet.add s accr.sl_sets }
                      else acc0, acc1, accr
                    with Not_found -> acc0, acc1, accr
                  ) l0.sl_sets (l0, l1, l_r) in
              let lin0, lin1, lin_r = reduce_diff lin0 lin1 lin_r in
              let lin1, lin0, lin_r = reduce_diff lin1 lin0 lin_r in
              if lin0 = sl_empty && lin1 = sl_empty then
                IntMap.add i lin_r acc
              else acc
            with Not_found -> acc
          ) u0.u_lin IntMap.empty in
      let lin =
        List.fold_left
          (fun acc (i, sl) ->
            if IntMap.mem i acc then Log.fatal_exn "already here!"
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
        u_sub = sub }
    let t_lub (t0: t) (t1: t): t =
      if not (IntSet.equal t0.t_roots t1.t_roots) then
        Log.fatal_exn "lub: inputs do not have the same roots";
      match t0.t_t, t1.t_t with
      | None, _ -> t1
      | _, None -> t0
      | Some u0, Some u1 -> { t0 with t_t = Some (u_lub u0 u1) }

    (* Weak bound: serves as widening *)
    let weak_bnd (t0: t) (t1: t): t = t_lub t0 t1
    (* Upper bound: serves as join and widening *)
    let upper_bnd (t0: t) (t1: t): t = t_lub t0 t1


    (** Set satisfiability *)
    let set_sat (c: set_cons) (t: t): bool =
      if debug_module then
        Log.debug "Set sat called: %s\n%s" (Set_utils.set_cons_2str c)
          (t_2stri IntMap.empty "    " t);
      let fail ( ) =
        Log.info "Set state:\n%s" (t_2stri IntMap.empty "   " t);
        Log.warn "Sat constraint dropped: %s" (set_cons_2str c);
        false in
      let r =
        match t.t_t with
        | None -> true (* any constraint valid under _|_ *)
        | Some u ->
            (* trying to support the same constraints as in guard *)
            match c with
            | S_mem (i, ex) -> u_sat_mem_ex u i ex
            | S_eq (S_var i, S_var j) -> u_sat_eq u i j
            | S_subset (S_var i, S_var j) -> u_sat_sub u i j
            | S_eq (S_var i, ex) | S_eq (ex, S_var i) ->
                begin
                  match linearize ex with
                  | None -> fail ( )
                  | Some lin -> u_sat_lin u i lin
                end
            | _ -> fail ( ) in
      if debug_module then
        Log.debug "set_sat returns: %b" r;
      r


    (** Set condition test *)
    let set_guard_aux (c: set_cons) (t: t): t =
      match t.t_t with
      | None -> t
      | Some u ->
          let u =
            (* Basic constraints added using the utility functions:
             *  all constraints needed in the graph examples are supported,
             *  except the S0 = S1 \cup S2 (not \uplus), as I believe such
             *  constraints should just not arise here! *)
            match c with
            | S_mem (i, S_var j) ->
                u_add_mem u i j
            | S_eq (S_var i, S_empty) | S_eq (S_empty, S_var i) ->
                if IntMap.mem i u.u_lin then Log.warn "lin, already here";
                let cons = { sl_elts = IntSet.empty; sl_sets = IntSet.empty } in
                let u_lin =
                  IntMap.map
                    (fun sl ->
                      { sl with sl_sets = IntSet.remove i sl.sl_sets }
                    ) u.u_lin in
                let u_lin, u_eqs =
                  IntMap.fold
                    (fun i sl (accl, acce) ->
                      if sl.sl_elts = IntSet.empty
                          && IntSet.cardinal sl.sl_sets = 1 then
                        let elt = IntSet.choose sl.sl_sets in
                        let eqs =
                          try IntMap.find i acce
                          with Not_found -> IntSet.empty in
                        IntMap.remove i accl,
                        IntMap.add i (IntSet.add elt eqs) acce
                      else accl, acce
                    ) u_lin (u_lin, u.u_eqs) in
                { u with
                  u_lin = IntMap.add i cons u_lin;
                  u_eqs = u_eqs }
            | S_eq (S_var i, S_var j) ->
                u_add_eq u i j
            | S_eq (S_var i, S_uplus (S_var j, S_var k))
            | S_eq (S_uplus (S_var j, S_var k), S_var i) ->
                u_add_lin u i { sl_sets = IntSet.add j (IntSet.singleton k);
                                sl_elts = IntSet.empty }
            | S_eq (S_var i, S_node j) | S_eq (S_node j, S_var i)
            | S_eq (S_var i, S_uplus (S_empty, S_node j))
            | S_eq (S_var i, S_uplus (S_node j, S_empty)) ->
                u_add_lin u i { sl_sets = IntSet.empty;
                                sl_elts = IntSet.singleton j }
            | S_eq (S_var i, S_uplus (S_node j, S_var k)) ->
                u_add_lin u i { sl_sets = IntSet.singleton k;
                                sl_elts = IntSet.singleton j }
            | S_eq (S_var i, e) ->
                begin
                  match linearize e with
                  | Some lin -> u_add_lin u i lin
                  | None ->
                      Log.warn "Set_guard: linearization failed; dropping";
                      u
                end
            | S_subset (S_var i, S_var j) ->
                if debug_module then
                  Log.debug "inclusion: %d <= %d" i j;
                u_add_inclusion u i j
            | _ ->
                (* otherwise, we just drop the constraint *)
                Log.warn "Set_guard ignored: %s" (set_cons_2str c);
                u in
          { t with t_t = Some u }
    let set_guard (c: set_cons) (t: t): t =
      let gt = set_guard_aux c t in
      if debug_module then
        Log.debug "Guard: %s\n%sResult:\n%s" (Set_utils.set_cons_2str c)
          (t_2stri IntMap.empty "   " t) (t_2stri IntMap.empty "   " gt);
      gt


    (** Forget (if the meaning of the SV changes, e.g., for an assignment) *)
    let sv_forget (sv: int) (t: t): t = (* will be used for assign *)
      let f i = i = sv in
      drop_symb_svs f t


    (** Renaming (e.g., post join) *)
    let symvars_srename
        (om: (Offs.t * int) Offs.OffMap.t)
        (nm: (int * Offs.t) node_mapping)
        (svmo: setv_mapping option)
        (t: t)
        : t =
      let optmap fs x =
        match svmo with
        | None -> x
        | Some svm -> fs svm x in
      (* Initial status *)
      if debug_module then
        Log.debug "begin:\n%s" (t_2stri IntMap.empty "  " t); 
      if om != Offs.OffMap.empty then
        Log.fatal_exn "rename: should get empty OffMap";
      (* Dropping SVs and SETVs that should be dropped *)
      let t = drop_symb_svs (fun i -> IntSet.mem i nm.nm_rem) t in
      let t =
        optmap (fun svm -> drop_setvs (fun i -> IntSet.mem i svm.sm_rem)) t in
      (* Basic transformation functions *)
      let do_sv (i: int): int =
        try fst (IntMap.find i nm.nm_map)
        with Not_found -> Log.fatal_exn "do_sv fails" in
      let do_sv_set (s: IntSet.t): IntSet.t =
        IntSet.fold (fun i acc -> IntSet.add (do_sv i) acc) s IntSet.empty in
      let do_setv =
        let fs svm (i: int): int =
          try fst (IntMap.find i svm.sm_map)
          with Not_found ->
            Log.warn "do_setv fails: %d" i;
            i in
        optmap fs in
      let do_setv_set =
        let fs _ (s: IntSet.t): IntSet.t =
          IntSet.fold (fun i a -> IntSet.add (do_setv i) a) s IntSet.empty in
        optmap fs in
      let do_set_lin (sl: set_lin): set_lin =
        { sl_elts  =  do_sv_set sl.sl_elts;
          sl_sets  =  do_setv_set sl.sl_sets } in
      (* Transformation function for type "u" *)
      let do_u (u: u): u =
        let fmap f m = (* rename everything *)
          IntMap.fold (fun setv x -> IntMap.add (do_setv setv) (f x))
            m IntMap.empty in
        let u = { u_lin = fmap do_set_lin u.u_lin;
                  u_mem = fmap do_sv_set u.u_mem;
                  u_sub = optmap (fun _ -> fmap do_setv_set) u.u_sub;
                  u_eqs = optmap (fun _ -> fmap do_setv_set) u.u_eqs } in
        optmap
          (fun svm u ->
            IntMap.fold (* adding equalities from the mapping *)
              (fun _ (setv0, s) acc ->
                IntSet.fold (fun j acc -> u_add_eq acc setv0 j) s acc
              ) svm.sm_map u
          ) u in
      let u =
        match t.t_t with
        | None -> None
        | Some u ->
            if debug_module then
              begin
                Log.debug "argument:\n%snode mapping:\n%s"
                  (t_2stri IntMap.empty "  " t) (node_mapping_2str nm);
                match svmo with
                | None -> ( )
                | Some svm ->
                    Log.debug "set mapping:\n%s" (setv_mapping_2str svm)
              end;
            Some (do_u u) in
      (* Roots should never be modified; fail if they do *)
      IntSet.iter
        (fun i ->
          if do_setv i != i then
            Log.fatal_exn "rename should not modify SETV root"
        ) t.t_roots;
      let tr = { t with t_t     = u } in
      if debug_module then
        Log.debug "renaming result:\n%s" (t_2stri IntMap.empty "   " tr);
      tr

    (* Synchronization of the SV environment*)
    let sve_sync_top_down (sve: svenv_mod) (t: t): t =
      (* do nothing for add; remove constraints over mod and rem *)
      let f i = PSet.mem i sve.svm_rem || PSet.mem i sve.svm_mod in
      drop_symb_svs f t

    (* Removes all symbolic vars that are not in a given set *)
    let symvars_filter (skeep: IntSet.t) (setvkeep: IntSet.t) (t: t): t =
      (* Removals are done by the generic removal functions *)
      drop_symb_svs (fun i -> not (IntSet.mem i skeep))
        (drop_setvs (fun i -> not (IntSet.mem i setvkeep)) t)
  end: DOMSET)
