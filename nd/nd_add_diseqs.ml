(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_add_diseqs.ml
 **       addition of disequalities to a numerical domain
 **         (without bottom interface)
 ** Xavier Rival, 2011/08/08 *)
open Apron
open Data_structures
open Lib
open Nd_sig
open Nd_utils

(** Error handling *)
module Log =
  Logger.Make(struct let section = "nd_+dise" and level = Log_level.DEBUG end)

(** Data-structures: maps over atoms standing for variables and constants *)

(* Triangular representation of constraints on pairs of atoms:
 *  Example: if a0 != a1, a1 != a2 we get:
 *    a0 => { a1 }
 *    a1 => { a2 } *)
type amap = AtomSet.t AtomMap.t
(* Find constraints *)
let amap_find_diff (a: atom) (am: amap): AtomSet.t =
  try AtomMap.find a am
  with Not_found -> AtomSet.empty
(* Join *)
let amap_join (am0: amap) (am1: amap): amap =
  AtomMap.fold
    (fun a s0 acc ->
      let s1 = try AtomMap.find a am1 with Not_found -> AtomSet.empty in
      AtomMap.add a (AtomSet.inter s0 s1) acc
    ) am0 AtomMap.empty
(* Removal of all constraints about atom a *)
let amap_forget (aforget: atom) (am: amap): amap =
  AtomMap.fold
    (fun a s acc ->
      AtomMap.add a (AtomSet.remove aforget s) acc
    ) (AtomMap.remove aforget am) AtomMap.empty
(* Addition of new disequality constraint a0 != a1 *)
let amap_add_constraint (a0: atom) (a1: atom) (am: amap): amap =
  let add_aux (aa0: atom) (aa1: atom): amap =
    let s = try AtomMap.find aa0 am with Not_found -> AtomSet.empty in
    AtomMap.add aa0 (AtomSet.add aa1 s) am in
  (* raises bottom if a0 = a1 *)
  let c = AtomOrd.compare a0 a1 in
  if c = 0 then raise Bottom
  else if c > 0 then add_aux a0 a1
  else add_aux a1 a0
(* Checks whether a relation belongs to an amap *)
let amap_mem (a0: atom) (a1: atom) (am: amap): bool =
  let mem_aux (aa0: atom) (aa1: atom): bool =
    try AtomSet.mem aa1 (AtomMap.find aa0 am)
    with Not_found -> false in
  let c = AtomOrd.compare a0 a1 in
  if c = 0 then false (* the atom is equal to itself *)
  else if c > 0 then mem_aux a0 a1
  else mem_aux a1 a0

(* Checks whether an atom is constrained not be null *)
let a_diff_null (a: atom) (am: amap): bool =
  amap_mem (Acst 0) a am

(* Computes all atoms in relation with another atom *)
let atoms_in_rel_to (a0: atom) (am: amap): AtomSet.t =
  AtomMap.fold
    (fun a1 aset acc ->
      if AtomSet.mem a0 aset then AtomSet.add a1 acc
      else acc
    ) am (amap_find_diff a0 am)


(** Module adding disequality constraints on top of another numerical domain *)

module Add_diseqs = functor (M: DOM_NUM_NB) ->
  (struct
    let module_name = "nd_add_diseqs"
    let config_2str (): string =
      Printf.sprintf "%s -> %s\n%s"
        module_name M.module_name (M.config_2str ())

    type t =
        { t_u: M.t ; (* underlying: equalities, inequalities *)
          t_d: amap  (* disequalities *) }
    (* Bottom element (might be detected) *)
    let is_bot (t: t): bool =
      (* Conflicting equalities and disequalities get reduced to _|_
       *  incrementally, via "raise Bottom" *)
      M.is_bot t.t_u
    (* Top element *)
    let top: t =
      { t_u = M.top ;
        t_d = AtomMap.empty }
    (* Pretty-printing *)
    let t_2stri (sn: sv_namer) (ind: string) (t: t): string =
      let sineqs =
        AtomMap.fold
          (fun a s acc ->
            Printf.sprintf "%s%s%s != {%s}\n" acc ind (atom_2str sn a)
              (atomset_2str sn s)
          ) t.t_d "" in
      Printf.sprintf "%s%s" sineqs (M.t_2stri sn ind t.t_u)

    (* Variables managemement *)
    let add_node (i: int) (t: t): t =
      { t with t_u = M.add_node i t.t_u }
    let rem_node (i: int) (t: t): t =
      { t_u = M.rem_node i t.t_u;
        t_d = amap_forget (Anode i) t.t_d }
    (* Renaming *)
    let vars_srename (nr: 'a node_mapping) (t: t): t =
      let do_atom_acc (acc: AtomSet.t) (a: atom): AtomSet.t =
        match a with
        | Acst _ -> AtomSet.add a acc
        | Anode i ->
            try
              if IntSet.mem i nr.nm_rem then acc
              else
                let k, s = IntMap.find i nr.nm_map in
                IntSet.fold
                  (fun j -> AtomSet.add (Anode j))
                  s (AtomSet.add (Anode k) acc)
            with Not_found -> AtomSet.add a acc in
      let do_atom = do_atom_acc AtomSet.empty in
      let do_atomset (s: AtomSet.t): AtomSet.t =
        AtomSet.fold (fun a acc -> do_atom_acc acc a) s AtomSet.empty in
      let do_amap (m: amap): amap =
        AtomMap.fold
          (fun a s acc ->
            let na = do_atom a in
            let ns = do_atomset s in
            AtomSet.fold
              (fun a0 ->
                AtomSet.fold (amap_add_constraint a0) ns
              ) na acc
          ) m AtomMap.empty in
      { t_u = M.vars_srename nr t.t_u ;
        t_d = do_amap t.t_d }
    let check_nodes (s: IntSet.t) (t: t): bool =
      let do_atom (a: atom): bool =
        match a with
        | Acst _ -> true
        | Anode i ->
            if IntSet.mem i s then true
            else
              begin
                Log.warn "check fails: %s" (atom_2str IntMap.empty a);
                false
              end in
      let do_atomset (s: AtomSet.t): bool =
        AtomSet.fold (fun a acc -> acc && do_atom a) s true in
      let do_amap (m: amap): bool =
        AtomMap.fold
          (fun a s acc ->
            acc && do_atom a && do_atomset s
          ) m true in
      do_amap t.t_d && M.check_nodes s t.t_u
    let nodes_filter (nkeep: IntSet.t) (t: t): t =
      let n_d =
        let keep_atom: atom -> bool = function
          | Acst _ -> true
          | Anode i -> IntSet.mem i nkeep in
        AtomMap.fold
          (fun a s acc ->
            if keep_atom a then
              AtomMap.add a (AtomSet.filter keep_atom s) acc
            else acc
          ) t.t_d AtomMap.empty in
      { t_u = M.nodes_filter nkeep t.t_u ;
        t_d = n_d }

    (** Comparison, Join and Widening operators *)
    let is_le (t0: t) (t1: t) (sat_diseq: int-> int -> bool): bool =
      let b_i =
        try
          AtomMap.fold
            (fun a s1 acc ->
              let s0 = amap_find_diff a t0.t_d in
              let res =
                match a with
                | Anode id ->
                    let sl = AtomSet.diff s1 s0 in
                    AtomSet.for_all
                      (fun ele ->
                        match ele with
                        | Anode i -> sat_diseq id i
                        | Acst _ -> false
                      ) sl
                | Acst _ -> AtomSet.subset s1 s0
              in acc && res
            ) t1.t_d true
        with Not_found -> false in
      b_i && M.is_le t0.t_u t1.t_u sat_diseq
    let join (t0: t) (t1: t): t =
      { t_u = M.join t0.t_u t1.t_u ;
        t_d = amap_join t0.t_d t1.t_d }
    let widen (t0: t) (t1: t): t =
      { t_u = M.widen t0.t_u t1.t_u ;
        t_d = amap_join t0.t_d t1.t_d }

    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (cons: n_cons) (t: t): bool =
      match cons with
      | Nc_cons (Tcons1.DISEQ, Ne_var vi, Ne_csti ci)
      | Nc_cons (Tcons1.DISEQ, Ne_csti ci, Ne_var vi) ->
          let b =
            let set = M.get_eq_class vi t.t_u in
            IntSet.fold
              (fun key acc ->
                (amap_mem (Acst ci) (Anode key) t.t_d || acc)
              ) set false in
          b || M.sat cons t.t_u
      | Nc_cons (Tcons1.DISEQ, Ne_var v0, Ne_var v1) ->
          let b =
            let aset = M.get_eq_class v0 t.t_u in
            let bset = M.get_eq_class v1 t.t_u in
            IntSet.fold
              (fun akey acc ->
                IntSet.fold
                  (fun bkey iac ->
                    (amap_mem (Anode akey) (Anode bkey) t.t_d || iac)
                  ) bset acc
              ) aset false in
          b || M.sat cons t.t_u
      | _ -> (* send to underlying domain *)
          M.sat cons t.t_u

    (** Transfer functions *)
    let assign (dst: int) (expr: n_expr) (t: t): t =
      { t_u = M.assign dst expr t.t_u ;
        t_d = amap_forget (Anode dst) t.t_d }
    let guard (b: bool) (cons: n_cons) (t: t): t =
      assert b;
      (* simplification on offset expressions *)
      let cons =
        let s_cons = Nd_utils.n_cons_simplify cons in
        if !Flags.flag_debug_guard && not (cons == s_cons) then
          Log.force "guard:add_diseqs[%b]:\n %s\n   => %s"
            (cons == s_cons) (n_cons_2str cons) (n_cons_2str s_cons);
        s_cons in
      match cons with
      | Nc_cons (Tcons1.DISEQ, Ne_var v0, Ne_var v1) ->
          (* Incremental reduction:
           *  -> if the equality is trivially satisfied or satisfied in num,
           *     then we reduce to _|_ immediately *)
          if v0 = v1 then raise Bottom
          else if sat (Nc_cons (Tcons1.EQ, Ne_var v0, Ne_var v1)) t then
            raise Bottom
          else
            { t with t_d = amap_add_constraint (Anode v0) (Anode v1) t.t_d }
      | Nc_cons (Tcons1.DISEQ, Ne_var vi, Ne_csti ci)
      | Nc_cons (Tcons1.DISEQ, Ne_csti ci, Ne_var vi) ->
          (* Incremental reduction:
           *  -> if the equality is satisfied in the num domain, we
           *     reduce to _|_ immediately *)
          if sat (Nc_cons (Tcons1.EQ, Ne_var vi, Ne_csti ci)) t then
            raise Bottom
          else
            { t with t_d = amap_add_constraint (Acst ci) (Anode vi) t.t_d }
      | Nc_cons (Tcons1.EQ, e0, e1) ->
          (* Incremental reduction:
           *  -> if the inequality is satisfied we reduce to _|_ immediately *)
          begin
            match n_expr_2atom e0, n_expr_2atom e1 with
            | None, _ | _, None ->
                { t with t_u = M.guard b cons t.t_u }
            | Some a0, Some a1 ->
                if Flags.do_raise_on_bottom && amap_mem a0 a1 t.t_d then
                  raise Bottom
                else
                  match a0, a1 with
                  | Anode i0, Anode i1 ->
                      let f_red i j =
                        if a_diff_null (Anode i) t.t_d
                            && sat (Nc_cons (Tcons1.EQ, Ne_var j, Ne_csti 0)) t
                        then
                          raise Bottom in
                      let f_ext a b ineqs =
                        let nrel = atoms_in_rel_to a ineqs in
                        AtomSet.fold (amap_add_constraint b) nrel ineqs in
                      f_red i0 i1;
                      f_red i1 i0;
                      (* saturation of inequality constraints *)
                      { t_d = f_ext a0 a1 (f_ext a1 a0 t.t_d);
                        t_u = M.guard b cons t.t_u }
                  | _ -> { t with t_u = M.guard b cons t.t_u }
          end
      (* new case: reduction "e0 >= e1" to "e0 > e1" *)
      | Nc_cons (Tcons1.SUPEQ, e0, e1) ->
          let new_cons =
            match n_expr_2atom e0, n_expr_2atom e1 with
            | None, _ | _, None -> cons
            | Some a0, Some a1 ->
	        if amap_mem a0 a1 t.t_d then Nc_cons (Tcons1.SUP, e0, e1) 
	        else cons in
	  { t with t_u = M.guard b new_cons t.t_u }        
      | _ ->
          if !Flags.flag_debug_guard then
            Log.force "guard:add_diseqs: no change";
          { t with t_u = M.guard b cons t.t_u }

    (** Utilities for the abstract domain *)
    let simplify_n_expr (t: t): n_expr -> n_expr = M.simplify_n_expr t.t_u
  
    (** Summarizing dimensions related operations *)
    (* Expand the constraints on one dimension to another *)
    let expand (id: int) (nid: int) (x: t): t = 
      { x with t_u = M.expand id nid x.t_u }
    (* Upper bound of the constraits of two dimensions *)
    let compact (lid: int) (rid: int) (x: t): t = 
      { x with t_u = M.compact lid rid x.t_u }
    (* Conjunction *)
    let meet (lx: t) (rx: t): t =
      { lx with t_u = M.meet lx.t_u rx.t_u }
    (* Forget the information on a dimension *)
    let sv_forget (id: int) (x: t): t =
      { t_d = amap_forget (Anode id) x.t_d;
        t_u = M.sv_forget id x.t_u }

    (** Export of range information *)
    (* bound of a variable  *)
    let bound_variable (dim: int) (x: t): interval =
      M.bound_variable dim x.t_u

    (** Extract the set of all SVs *)
    let get_svs (x: t) : IntSet.t =
      M.get_svs x.t_u

    (** Extract all SVs that are equal to a given SV *)
    let get_eq_class (i: int) (x: t): IntSet.t =
      M.get_eq_class i x.t_u
  end: DOM_NUM_NB)

