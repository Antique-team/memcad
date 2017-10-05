(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_val_pack.ml
 **       lifting of a numerical domain into one with dynamic packing *)
open Data_structures
open Lib
open Offs

open Dom_sig
open Graph_sig
open Ind_sig
open Nd_sig
open Svenv_sig

open Nd_utils

open Apron

(** Error report *)
module Log =
  Logger.Make(struct let section = "dv_pack_" and level = Log_level.DEBUG end)

(* a unique id for each avatar dimension of a variable *)
let unique: int ref = ref 0
let get_unique () =
  unique := !unique + 1;
  !unique

(** Lift functor *)
module Make_num_dy_pack = functor (Dn: DOM_NUM) ->
  (struct
    (** Type of abstract values *)
    type t =
        { t_packNum: Dn.t IntMap.t;    (* pack number -> abstract value *)
          t_idPack:  int Union_find.t; (* SV -> pack number *) }

    (** Domain initialization *)
    (* Domain initialization to a set of inductive definitions *)
    let init_inductives (g: Keygen.t) (_: StringSet.t): Keygen.t =
      g (* this domain generates no keys *)

    (** Lattice elements *)
    (* Bottom element *)
    let bot: t =
      { t_packNum = IntMap.singleton (-1) Dn.bot;
        t_idPack  = Union_find.add (-1) Union_find.empty; }
    (* Equality to Bottom *)
    let is_bot (x: t): bool =
      IntMap.fold (fun _ num acc -> Dn.is_bot num || acc) x.t_packNum false

    (** Top element **)
    let top: t =
      { t_packNum = IntMap.singleton (-1) Dn.top;
        t_idPack  = Union_find.add (-1) Union_find.empty; }

    (** Pretty-printing **)
    let t_2stri (sn: sv_namer) (ind: string) (x: t): string =
      let s0 = Union_find.t_2stri "" (Printf.sprintf " %d ") x.t_idPack in
      let s1 =
        IntMap.fold
          (fun key dv acc->
            Printf.sprintf "key is %d\n%s\n%s" key (Dn.t_2stri sn ind dv) acc
          ) x.t_packNum "\n\n\n" in
      s0 ^ s1

    (** Node addition and removal **)
    (* Add a node to a specific pack, if the pack does not exist, create one *)
    let add_node_to_pack (id: int) (pack_id: int) (x: t): t =
      if is_bot x then (* bot carries no pack *)
        bot
      else if Union_find.mem pack_id x.t_idPack then
        (* add to existing pack *)
        let rep, nidpack = Union_find.find pack_id x.t_idPack in
        let newpack = Dn.add_node id (IntMap.find rep x.t_packNum) in
        { t_packNum = IntMap.add rep newpack x.t_packNum ;
          t_idPack  = Union_find.add id ~rep: pack_id nidpack; }
      else (* create a new pack *)
        { t_packNum = IntMap.add id (Dn.add_node id Dn.top) x.t_packNum;
          t_idPack  = Union_find.add id x.t_idPack; }

    (* By default, each variable will be the in a new invidual pack *)
    let add_node (id: int) (x: t): t =
      add_node_to_pack id id x
    let rem_node (id: int) (x: t): t =
      if is_bot x then bot
      else
        let rep, nidpack = Union_find.find id x.t_idPack in
        let num = IntMap.find rep x.t_packNum in
        let nepo, uf = Union_find.rem id nidpack in
        let npackN =
          if IntSet.cardinal (Dn.get_svs num) = 1 then
          IntMap.remove rep x.t_packNum
        else
          let nep =
            match nepo with
            | Some e -> e
            | None -> error "non consitent pack with union find" in
          IntMap.add nep (Dn.rem_node id num) (IntMap.remove rep x.t_packNum) in
        { t_packNum = npackN;
          t_idPack  = uf }

    (** Utils functions **)
    (* Merge two numeric elements *)
    let num_union (l: Dn.t) (r: Dn.t): Dn.t =
      let lvars = Dn.get_svs l in
      let rvars = Dn.get_svs r in
      let nl = IntSet.fold Dn.add_node rvars l in
      let nr = IntSet.fold Dn.add_node lvars r in
      Dn.meet nl nr

    (* Merge two packs *)
    let pack_union (l: int) (r: int) (x: t): t =
      let lrep, _ = Union_find.find l x.t_idPack in
      let rrep, _ = Union_find.find r x.t_idPack in
      if lrep = rrep then (* same pack physically, nothing to do *)
        x
      else
        let nnum =
          num_union (IntMap.find lrep x.t_packNum)
            (IntMap.find rrep x.t_packNum) in
        let npackN = IntMap.add lrep nnum (IntMap.remove rrep x.t_packNum) in
        { t_packNum = npackN;
          t_idPack  = Union_find.union lrep rrep x.t_idPack }

    (* Move a set of variables from rrep to lrep
     * not used now as it will cause a loss of precision!!!!! *)
    let move_set (lrep: int) (rrep: int) (set: IntSet.t) (x: t): t =
      let rnum = IntMap.find rrep x.t_packNum in
      let lnum = IntMap.find lrep x.t_packNum in
      let rvars = Dn.get_svs rnum in
      let diff = IntSet.diff rvars set in
      let tnum = IntSet.fold Dn.rem_node diff rnum in
      let lnum = num_union lnum tnum in
      let npackNum = IntMap.add lrep lnum x.t_packNum in
      let nrp,nidPack =
        IntSet.fold
          (fun key (irp,iIdPack) ->
            let com,uf = Union_find.rem key iIdPack in
            match com with
            | Some rp -> rp, uf
            | None -> irp, uf
          ) set (rrep, x.t_idPack) in
      let npackNum =
        if set = rvars then
          IntMap.remove rrep npackNum
        else
          let rnum = IntSet.fold Dn.rem_node set rnum in
          IntMap.add nrp rnum (IntMap.remove rrep npackNum) in
      let nidPack =
        IntSet.fold (fun key -> Union_find.add key ~rep:lrep) set nidPack in
      { t_packNum = npackNum;
        t_idPack  = nidPack }

    (* Gather variables in transfer functions.
     * The pack containing these varaiables will be merged  *)
    let gather_cons (c: n_cons) (x: t) : int * t =
      let vset = n_cons_fold IntSet.add c IntSet.empty in
      if IntSet.is_empty vset then
        -1, x
      else
        let base = IntSet.choose vset in
        let vset = IntSet.remove base vset in
        let x = IntSet.fold (pack_union base) vset x in
        base, x

    let gather_expr (id: int) (e: n_expr) (x: t) :  t =
      let vset = n_expr_fold IntSet.add e IntSet.empty in
      IntSet.fold (pack_union id) vset x

    (* Unify the packing of two abstract states, for join or inclusion check *)
    let unify (l: t) (r: t) : t * t =
      IntMap.fold
        (fun key _ (accl, accr) ->
          if key = -1 then accl, accr
          else
            let lrep, _ = Union_find.find key accl.t_idPack in
            let rrep, _ = Union_find.find key accr.t_idPack in
            let rnum = IntMap.find rrep accr.t_packNum in
            let accr =
              let packnum =
                IntMap.add lrep rnum (IntMap.remove rrep accr.t_packNum) in
              { t_idPack  = Union_find.lift_rep lrep accr.t_idPack;
                t_packNum = packnum } in
            let rrep = lrep in
            let lvars =
              IntSet.of_list (Union_find.find_class lrep accl.t_idPack) in
            let rvars =
              IntSet.of_list (Union_find.find_class rrep accr.t_idPack) in
            let rec fixp (vs0: IntSet.t) (vs1: IntSet.t)
                (x0: t) (x1: t): t * t =
              if IntSet.equal vs0 vs1 then
                x0,x1
              else
                (* find the least common packing  *)
                let ele_trans  (trep: int) (s: IntSet.t)  (vs: IntSet.t) (x: t)  =
                  let v = IntSet.choose s in
                  let rep, _ = Union_find.find v x.t_idPack in
                  let vars =
                    IntSet.of_list (Union_find.find_class rep x.t_idPack) in
                  let vs = IntSet.union vs vars in
                  let x = pack_union trep rep x in
                  vs, x in
                let dv01 = IntSet.inter (IntSet.diff vs0 vs1) vs0 in
                if not (IntSet.is_empty dv01) then
                  let vs1, x1 = ele_trans rrep dv01 vs1 x1 in
                  fixp vs0 vs1 x0 x1
                else
                  let dv10 = IntSet.inter (IntSet.diff vs1 vs0) vs1 in
                  let vs0, x0 = ele_trans lrep dv10 vs0 x0 in
                  fixp vs0 vs1 x0 x1 in
            fixp lvars rvars accl accr
        ) l.t_packNum (l, r)

    (* Temporary implementation, it is ugly wrt it utilizes tmp keys *)
    (* which are negative integers *)
    let vars_srename (nr: 'a node_mapping) (x: t) =
      if is_bot x then
        bot
      else
        let x = IntSet.fold rem_node nr.nm_rem x in
        let nr = { nr with nm_rem = IntSet.empty } in
        let tmp_key (key: int) = -(key + 10) in
        let name_phase (o: int) (n: int) (s: IntSet.t) (tx: t) =
          let rep, _ = Union_find.find o tx.t_idPack in
          let num = IntMap.find rep tx.t_packNum in
          let num =
            Dn.vars_srename
              { nr with nm_map = IntMap.singleton o (n, s) } num in
          let nidP =
            IntSet.fold
              ( fun key -> Union_find.add key ~rep:rep) s tx.t_idPack in
          let nidP = Union_find.var_rename o n nidP in
          let npackN = if o = rep then
            IntMap.add n num (IntMap.remove rep tx.t_packNum)
          else
            IntMap.add rep num tx.t_packNum in
          { t_packNum = npackN;
            t_idPack  = nidP } in
        let x =
          IntMap.fold
            (fun old (frsh, set) acc ->
              if old = frsh && IntSet.is_empty set then acc
              else
                let frsh = tmp_key frsh in
                name_phase old frsh IntSet.empty acc
            ) nr.nm_map x in
        IntMap.fold
          (fun old (frsh, set) acc ->
            if old = frsh && IntSet.is_empty set then acc
            else
              let old = tmp_key frsh in
              name_phase old frsh set acc
           ) nr.nm_map x

    (* Symbolic variables in the abstract state *)
    let get_svs (x: t): IntSet.t =
      if is_bot x then  error "Bot in get_svs"
      else
        IntMap.fold
          (fun _ num  -> IntSet.union (Dn.get_svs num))
          x.t_packNum IntSet.empty

    (* For sanity check *)
    let check_nodes (s: IntSet.t) (x: t): bool =
      if is_bot x then false
      else
        let vars = get_svs x in IntSet.equal s vars

    (* Filter all variables not in nkeep *)
    let nodes_filter (nkeep: IntSet.t) (x: t): t =
      if is_bot x then bot
      else
        let vars = get_svs x in
        let diff = IntSet.diff vars nkeep in
        IntSet.fold rem_node diff x

    (** Comparison and Join operators *)
    let is_le (x0: t) (x1: t): bool =
      if is_bot x0 then true
      else if is_bot x1 then false
      else
        let nx0,nx1 = unify x0 x1 in
        IntMap.fold
          (fun key num acc ->
            let num1 = IntMap.find key nx1.t_packNum in
            Dn.is_le num num1 && acc
          ) nx0.t_packNum true

    let upper_bnd (akind: join_kind) (x0: t) (x1: t) =
      if is_bot x0 then x1
      else if is_bot x1 then x0
      else
        let nx0, nx1 = unify x0 x1 in
        IntMap.fold
          (fun key num acc ->
            let num1 = IntMap.find key nx1.t_packNum in
            let npacknum =
              match akind with
              | Jjoin -> IntMap.add key (Dn.join num num1) acc.t_packNum
              | Jwiden -> IntMap.add key (Dn.widen num num1) acc.t_packNum
              | _ -> error "unsupproted join kind" in
            { acc with t_packNum = npacknum }
          ) nx0.t_packNum nx0

    let join (x0: t) (x1: t): t =
      upper_bnd Jjoin x0 x1

    let widen (x0: t) (x1: t): t =
      upper_bnd Jwiden x0 x1

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (c: n_cons) (x: t): bool =
      if is_bot x then true
      else
        let base, x = gather_cons c x in
        let num =
          if base = -1 then
            snd (IntMap.max_binding x.t_packNum)
          else
            let rep, _ = Union_find.find base x.t_idPack in
            IntMap.find rep x.t_packNum in
        Dn.sat c num

    (** Transfer functions *)
   let guard (b: bool) (c: n_cons) (x: t): t =
      if is_bot x then  bot
      else
        let base, x = gather_cons c x in
        let key, num =
          if base = -1 then
            IntMap.max_binding x.t_packNum
          else
            let rep,_ = Union_find.find base x.t_idPack in
            let num = IntMap.find rep x.t_packNum in
            rep,num in
        { x with t_packNum = IntMap.add key (Dn.guard b c num) x.t_packNum }

    (** Now we have two versions of transfer functions for assignments, this
     ** one is supposed slower in theory, but actually is faster in practice *)
    let assign (dst: int) (expr: n_expr) (x:t): t =
      if is_bot x then bot
      else
        let x = gather_expr dst expr x in
        let rep, _ = Union_find.find dst x.t_idPack in
        let num = IntMap.find rep x.t_packNum in
        { x with
          t_packNum = IntMap.add rep (Dn.assign dst expr num) x.t_packNum }

    (** Another version of assignment supposed to be more efficient  *
     ** This one is supposed to be more  efficient, which is not shown by the
     ** experiments *)
    let gather_expr (id: int) (e: n_expr) (x: t) :  t =
      let vset = n_expr_fold (fun var ->IntSet.add var) e IntSet.empty in
      let x =
        if IntSet.mem id vset then x
        else
          let x = rem_node id x in add_node id x in
      IntSet.fold
        (fun var acc ->
          pack_union id var acc
        ) vset x

    let assign (dst: int) (expr: n_expr) (x:t): t =
      if is_bot x then  bot
      else
        let x = gather_expr dst expr x in
        let rep,_ = Union_find.find dst x.t_idPack in
        let num = IntMap.find rep x.t_packNum in
        { x with
          t_packNum = IntMap.add rep (Dn.assign dst expr num) x.t_packNum}

    (** Utilities for the abstract domain *)
    let simplify_n_expr (x: t) (e: n_expr): n_expr =
      if is_bot x then e
      else
        let vset = n_expr_fold IntSet.add e IntSet.empty in
        if IntSet.is_empty vset then
          error "no variable in n_expr in simplify_n_expr"
        else
          let base = IntSet.choose vset in
          let vset = IntSet.remove base vset in
          let x = IntSet.fold (pack_union base) vset x in
          let rep,_ = Union_find.find base x.t_idPack in
          let num = IntMap.find rep x.t_packNum in
          Dn.simplify_n_expr num e

    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another *)
    let expand (id: int) (nid: int) (x: t) : t =
      if is_bot x then bot
      else
        let rep, _ = Union_find.find id x.t_idPack in
        let num = IntMap.find rep x.t_packNum in
        { t_idPack  = Union_find.add nid ~rep:rep x.t_idPack;
          t_packNum = IntMap.add rep (Dn.expand id nid num) x.t_packNum }

    (* Merge two variables *)
    let compact (lid: int) (rid: int) (x: t): t =
     if is_bot x then bot
     else
      let x = pack_union lid rid x in
      let rep, _ = Union_find.find lid x.t_idPack in
      let num = IntMap.find rep x.t_packNum in
      let num = Dn.compact lid rid num in
      let _, nidPack = Union_find.rem rid x.t_idPack in
      { t_packNum = IntMap.add rep num x.t_packNum;
        t_idPack  = nidPack }

    (* Conjunction *)
    let meet (x0: t) (x1: t): t =
      let nx0,nx1 = unify x0 x1 in
      IntMap.fold
        (fun key num acc ->
          let num1 = IntMap.find key nx1.t_packNum in
          { acc with
            t_packNum = IntMap.add key (Dn.meet num num1) acc.t_packNum }
         ) nx0.t_packNum nx0

    (* Forget the information on a dimension *)
    let forget (id: int) (x:t): t =
      if is_bot x then bot
      else
        let rep, _ = Union_find.find id x.t_idPack in
        let num = IntMap.find rep x.t_packNum in
        let num = Dn.forget id num in
        { x with t_packNum = IntMap.add rep num x.t_packNum }

    (** Export of range information *)
    (* bound of a variable  *)
    let bound_variable (dim: int) (x: t): interval =
      if is_bot x then
        error "BOT IN BOUND VARIABLE"
      else
        let rep,_ = Union_find.find dim x.t_idPack in
        let num = IntMap.find rep x.t_packNum in
        Dn.bound_variable dim num

    (* Get all variables that equal to a given SV *)
    let get_eq_class (var: int) (x: t): IntSet.t =
       if is_bot x then
        error "BOT IN GET EQ CLASS"
      else
        let rep,_ = Union_find.find var x.t_idPack in
        let num = IntMap.find rep x.t_packNum in
        Dn.get_eq_class var num
  end: DOM_NUM)
