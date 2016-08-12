(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: off_linexpr.ml
 **       simple implementations of various forms of offsets
 ** Xavier Rival, Pascal Sotin, 2012/04/23 *)
open Apron
open Data_structures
open Lib
open Nd_sig
open Off_sig

(** Error report *)
module Log =
  Logger.Make(struct let section = "off_lxpr" and level = Log_level.DEBUG end)

(** Implementation with linear expressions over node ids.
 ** This is now the default implementation of offsets. *)
module Off_Linexpr =
  (struct
    type key = int (* node ids *)
    (* Linear expressions over type key *)
    type linexpr =
        { l_cons:   int; (* constant part *)
          l_linear: int IntMap.t; (* linear part coefficients *) }

    (** Offsets and sizes are linear expressions *)
    type t = linexpr
    type size = linexpr

    (** Printing *)
    let linexpr_2str (l: linexpr): string =
      let scons =
        if l.l_cons = 0 then None
        else Some (string_of_int l.l_cons) in
      let slin =
        IntMap.fold
          (fun is co acc_o ->
            if co = 0 then acc_o
            else
              match acc_o with
              | None -> Some (Printf.sprintf "%d * N|%d|" co is)
              | Some s -> Some (Printf.sprintf "%s + %d * N|%d|" s co is)
          ) l.l_linear scons in
      match slin with
      | None -> "0"
      | Some s -> s
    let t_2str (o: t): string = Printf.sprintf "@{%s}" (linexpr_2str o)
    let size_2str (s: size): string = Printf.sprintf "{%s}" (linexpr_2str s)

    (** Constructors and conversions *)
    (* Null offset *)
    let zero: t = { l_cons   = 0;
                    l_linear = IntMap.empty }
    let size_zero: size = zero
    (* Integer offset *)
    let of_int (i: int): t = { l_cons   = i;
                               l_linear = IntMap.empty }
    (* String offset *)
    let of_string (s: string): t =
      Log.fatal_exn "Off_Linexpr impl, of_string (%s)" s
    (* Field (string+int) offset *)
    let of_field ((_,i): string * int): t = of_int i
    (* Size, from an integer *)
    let size_of_int (i: int): size = of_int i

    (** Conversion into other data types *)
    (* Size, from offset *)
    let to_size (o: t): size = o
    (* Offset, from size *)
    let of_size (s: size): t = s
    (* Turning an offset into an integer, if possible *)
    let to_int_opt (o: t): int option =
      if o.l_linear = IntMap.empty then Some o.l_cons
      else None
    let to_int (o: t): int =
      match to_int_opt o with
      | Some i -> i
      | None -> failwith "to_int: None"
    let size_to_int_opt (s: size): int option = to_int_opt s
    (* Turning an offset into an n_expr *)    
    let to_n_expr (o: t): n_expr =
      let f map init =
        IntMap.fold
          (fun is co acc ->
            Ne_bin (Texpr1.Add, acc, Ne_bin (Texpr1.Mul, Ne_csti co, Ne_var is))
          ) map init in
      if o.l_cons = 0 then
        if o.l_linear = IntMap.empty then Ne_csti 0
        else
          (* extract an element from the map, removes it and fold *)
          let is, co =
            let opt = IntMap.fold (fun i c _ -> Some (i,c)) o.l_linear None in
            match opt with
            | None -> Log.fatal_exn "map should be non empty"
            | Some (i, c) -> i, c in
          f (IntMap.remove is o.l_linear)
            (Ne_bin (Texpr1.Mul, Ne_csti co, Ne_var is))
      else f o.l_linear (Ne_csti o.l_cons)
    let size_to_n_expr: size -> n_expr = to_n_expr

    (** Comparisons *)
    (* Whether an offset is constant *)
    let t_is_const (o: t): bool = o.l_linear = IntMap.empty
    (* Whether an offset is constant *)
    let size_is_const (s: size): bool = s.l_linear = IntMap.empty
    (* Compare, syntactic on AST, to build sets *)
    let compare (o0: t) (o1: t): int =
      let c = o0.l_cons - o1.l_cons in
      if c != 0 then c
      else
        let c = IntMap.cardinal o0.l_linear - IntMap.cardinal o1.l_linear in
        if c != 0 then c
        else
          let set_is =
            let f i _ = IntSet.add i in
            IntMap.fold f o0.l_linear
              (IntMap.fold f o1.l_linear IntSet.empty) in
          let module Stop =
            struct
              exception E of int
              let run c a b = try a b with Not_found -> raise (E c)
            end in
          try
            IntSet.iter
              (fun is ->
                let co0 = Stop.run (-1) (IntMap.find is) o0.l_linear in
                let co1 = Stop.run 1    (IntMap.find is) o1.l_linear in
                let c = co0 - co1 in if c != 0 then raise (Stop.E c)
              ) set_is;
            0
          with Stop.E c -> c
    (* Equality test *)
    let eq (o0: t) (o1: t): bool = compare o0 o1 = 0
    let size_eq: size -> size -> bool = eq
    (* Compare, semantic *)
    let leq (sat: n_cons -> bool) (o0: t) (o1: t): bool =
      if o0.l_linear = IntMap.empty && o1.l_linear = IntMap.empty then
        o0.l_cons <= o1.l_cons
      else
        let e0 = to_n_expr o0 in
        let e1 = to_n_expr o1 in
        let r = sat (Nc_cons (Tcons1.SUPEQ, e1, e0)) in
        Log.info "Trying ofleq %s <= %s: %b" (t_2str o0) (t_2str o1) r;
        r
    (* Nullness test *)
    let is_zero (o: t): bool =
      IntMap.fold (fun _ co acc -> acc && co = 0) o.l_linear (o.l_cons = 0)
    (* Semantic comparison of linear expressions:
     *  - returns Some i (i \in {-1,0,1}) if it can be decided
     *  - otherwise, returns None *)
    let lin_order (sat: n_cons -> bool) (sz0: size) (sz1: size): int option =
      if sz0.l_linear = IntMap.empty && sz1.l_linear = IntMap.empty then
        Some (sz0.l_cons - sz1.l_cons)
      else if eq sz0 sz1 then Some 0
      else
        let e0 = to_n_expr sz0 in
        let e1 = to_n_expr sz1 in
        if sat (Nc_cons (Tcons1.EQ, e0, e1)) then Some 0
        else if sat (Nc_cons (Tcons1.SUPEQ, e0, e1)) then Some 1
        else if sat (Nc_cons (Tcons1.SUPEQ, e1, e0)) then Some (-1)
        else None
    (* Semantic comparison of sizes; attempts to prove that s0 <= s1 *)
    let size_leq (sat: n_cons -> bool) (sz0: size) (sz1: size): bool =
      if sz0.l_linear = IntMap.empty && sz1.l_linear = IntMap.empty then
        sz0.l_cons <= sz1.l_cons
      else
        let e0 = to_n_expr sz0 in
        let e1 = to_n_expr sz1 in
        sat (Nc_cons (Tcons1.SUPEQ, e1, e0))
    (* Semantic comparisons of sizes and offsets:
     * search for fields in physical placement order *)
    let size_order: (n_cons -> bool) -> size -> size -> int option = lin_order
    let t_order: (n_cons -> bool) -> t -> t -> int option = lin_order

    (** Arithmetics *)
    let add_int (o: t) (i: int): t = { o with l_cons = o.l_cons + i }
    let bin_addl (op: int -> int -> int) (o0: t) (o1: t): t =
      let m_lin =
        IntMap.fold
          (fun is co1 acc ->
            let co =
              try op (IntMap.find is o0.l_linear) co1
              with Not_found -> op 0 co1 in
            if co = 0 then IntMap.remove is acc else IntMap.add is co acc
          ) o1.l_linear o0.l_linear in
      { l_cons   = op o0.l_cons o1.l_cons;
        l_linear = m_lin }
    let add: t -> t -> t = bin_addl (+)
    let add_size: t -> size -> t = add
    let size_add_size: size -> size -> size = add
    let sub: t -> t -> size = bin_addl (-)
    let sub_t: t -> t -> t = sub
    let size_sub_size: size -> size -> size = sub
    let mul_int (o: t) (i: int): t =
      { l_cons   = i * o.l_cons;
        l_linear = IntMap.map (fun k -> k * i) o.l_linear }
    (* Split an offset modulo some given stride *)
    let modulo_split (stride: int) (x: t): t * t (* aligned + bias *) =
      (* decomposition of an integer *)
      let f (i: int): int * int =
        let m = i mod stride in i - m, m in
      let i_lin, m_lin =
        IntMap.fold
          (fun is co (acci, accm) ->
            let ci, cm = f co in
            let nmi = if ci = 0 then acci else IntMap.add is ci acci in
            let nmm = if cm = 0 then accm else IntMap.add is cm accm in
            nmi, nmm
          ) x.l_linear (IntMap.empty, IntMap.empty) in
      let i_cons, m_cons = f x.l_cons in
      { l_cons   = i_cons;
        l_linear = i_lin },
      { l_cons   = m_cons;
        l_linear = m_lin }
    (* Checks whether is aligned on stride *)
    let is_on_stride (stride: int) (o: t): bool =
      let _, m = modulo_split stride o in
      is_zero m

    (** Construction from a numerical domain expression *)
    let rec of_n_expr (e: n_expr): t =
      match e with
      | Ne_csti i -> of_int i
      | Ne_var i -> { l_cons   = 0;
                      l_linear = IntMap.add i 1 IntMap.empty }
      | Ne_bin (Texpr1.Add, e0, e1) ->
          add (of_n_expr e0) (of_n_expr e1)
      | Ne_bin (Texpr1.Mul, Ne_csti n, e)
      | Ne_bin (Texpr1.Mul, e, Ne_csti n) ->
          mul_int (of_n_expr e) n
      | _ -> Log.fatal_exn"Off_Linexpr, bin"

    (** Utilities *)
    (* Ids of symbolic variables *)
    let lin_sym_var_ids_add (acc: IntSet.t) (l: linexpr): IntSet.t =
      IntMap.fold (fun is _ -> IntSet.add is) l.l_linear acc
    let t_sym_var_ids_add: IntSet.t -> t -> IntSet.t = lin_sym_var_ids_add
    let size_sym_var_ids_add: IntSet.t -> size -> IntSet.t = lin_sym_var_ids_add

    (** Unification *)
    let linexpr_unify (o0: linexpr) (o1: linexpr)
        : ((int * int * int) list * linexpr) option =
      (* for now, very restricted scope *)
      let sz0 = IntMap.cardinal o0.l_linear
      and sz1 = IntMap.cardinal o1.l_linear in
      if sz0 = sz1 then
        match sz0 with
        | 0 -> (* constants *)
            if o0.l_cons = o1.l_cons then Some ([ ], o0)
            else None
        | 1 -> (* expressions with a single term *)
            let sv0, co0 = IntMap.min_binding o0.l_linear
            and sv1, co1 = IntMap.min_binding o1.l_linear in
            if o0.l_cons = o1.l_cons && co0 = co1 then (* unifiable *)
              let l_unif, var = [ sv0, sv1, 0 ], 0 in
              Some (l_unif,
                    { l_cons   = o0.l_cons;
                      l_linear = IntMap.add var co0 IntMap.empty })
            else (* no possible unification *)
              None
        | _ -> None (* too many elements, we currently do not unify *)
      else None
    let t_unify: t -> t -> ((int * int * int) list * t) option =
      linexpr_unify
    let size_unify: size -> size -> ((int * int * int) list * size) option =
      linexpr_unify

    (** Renaming *)
    exception Stop (* aborts attempts to rename if an atom is not found *)
    let opt_linexpr_rename (index: int IntMap.t) (o: linexpr): linexpr option =
      try
        let lin =
          IntMap.fold
            (fun sv co acc ->
              let nsv =
                try IntMap.find sv index with Not_found -> raise Stop in
              if IntMap.mem nsv acc then
                Log.fatal_exn "sym_var already there in rename";
              IntMap.add nsv co acc
            ) o.l_linear IntMap.empty in
        Some { o with l_linear = lin }
      with Stop -> None
    let linexpr_rename (index: int IntMap.t) (o: linexpr): linexpr =
      match opt_linexpr_rename index o with
      | None -> Log.fatal_exn "not found in rename"
      | Some lin -> lin
    let t_rename: int IntMap.t -> t -> t = linexpr_rename
    let size_rename: int IntMap.t -> size -> size = linexpr_rename
    let t_rename_opt: int IntMap.t -> t -> t option = opt_linexpr_rename
  end: OFF_SIG)
