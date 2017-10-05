(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_val_npack.ml
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
  Logger.Make(struct let section = "dv_pack__" and level = Log_level.DEBUG end)

(* a unique id for each avatar dimension of a variable *)
let pack_counter: int ref = ref 0
let get_pack_counter () =
  pack_counter := !pack_counter + 1;
  !pack_counter

let num_counter: int ref = ref 0
let get_num_counter () =
  num_counter := !num_counter + 1;
  !num_counter


let max_ratio = 1
let max_pack  = 10000
let ad_length = 3


(** Lift functor *)

module Make_num_dy_pack = functor (Dn: DOM_NUM_NB) ->
  (struct
    (** Type of abstract values *)
    type t =
        { (* graph for variables in adjacent statements*)
          t_adGraph: IntSet.t IntMap.t;
          (* constraint graph for variables *)
          t_reGraph: IntSet.t IntMap.t;
          (* numeric id, numeric value, the set of variables*)
          t_pack: (int * Dn.t * IntSet.t) IntMap.t;
          (* Maps a pack to a pack_id, the packs with same
           * pack_id are with same set of variables *)
          t_groupPack: int IntMap.t;
          (* Maps a var to the packs it is in *)
          t_varGroup: IntSet.t IntMap.t;
          (* Free variables *)
          t_freeVar: IntSet.t;
          (* Variables appear in last statements *)
          t_lastVar: IntSet.t list }

    (* Equality to Bottom *)
    let is_bot (x: t) =
      IntMap.exists
        (fun key elt -> let (_, nele, _) = elt in Dn.is_bot nele) x.t_pack

    (** Top element **)
    let top =
      { t_adGraph = IntMap.empty;
        t_reGraph = IntMap.empty;
        t_pack = IntMap.empty;
        t_groupPack = IntMap.empty;
        t_varGroup = IntMap.empty;
        t_freeVar = IntSet.empty;
        t_lastVar = [];}

    (** Pretty-printing **)
    let t_2stri (sn: sv_namer) (ind: string) (x: t) =
      let set2str  (ind: string)  (set: IntSet.t) =
        IntSet.fold
          (fun elt acc ->
            Printf.sprintf "%s %d " acc elt
          ) set ind in
      let graph2str (graph: IntSet.t IntMap.t) (ind: string) =
        IntMap.fold
          (fun key set acc ->
            let sets = set2str  "" set in
            Printf.sprintf "%s \n %d -> %s \n " acc key sets
          ) graph ind in
      let pack_s =
        IntMap.fold
          (fun key (num_id, num, set) acc->
            (Printf.sprintf "\n pack_id is %d num_id is %d\n" key num_id )
            ^(Dn.t_2stri sn ind num)^"\n"^
            (IntSet.fold (Printf.sprintf "%d %s")
               (Dn.get_svars num) "is in real set\n")^
            (IntSet.fold (Printf.sprintf "%d %s") set "is in set\n")^acc
          ) x.t_pack "\n\n\n" in
      let lastVars = List.fold_left set2str "\n LastVar is \n" x.t_lastVar in
      let adgraphs = graph2str x.t_adGraph "\n adGraph is \n" in
      let regraphs = graph2str x.t_reGraph "\n reGraph is \n" in
      let varGroup = graph2str x.t_varGroup "\n varGroup is \n" in
      let groupPack =
        IntMap.fold (Printf.sprintf "%d -> %d \n %s") x.t_groupPack "" in
      let groupPack = Printf.sprintf "\n\n\n groupPack is \n %s" groupPack in
      let freeVars = set2str "FreeVars are " x.t_freeVar in
      lastVars^freeVars^regraphs ^varGroup^groupPack^pack_s

    (* A value of a node is updated, thus remove that node from
     * the constraints graph *)
    let rem_node_in_graph (id: int) (adgraph: IntSet.t IntMap.t)
        (regraph: IntSet.t IntMap.t)
        : (IntSet.t IntMap.t) * (IntSet.t IntMap.t) * IntSet.t =
      let set = IntMap.find_err "rem_node_in_graph 1" id adgraph in
      let adgraph = IntMap.add id IntSet.empty adgraph in
      let adgraph =
        IntSet.fold
          (fun elt acc ->
            let iset = IntMap.find_err "rem_node_in_graph 2" elt acc in
            IntMap.add elt (IntSet.remove id iset) acc
           ) set adgraph in
      let set = IntMap.find_err "rem_node_in_graph 3" id regraph in
      let regraph = IntMap.add id IntSet.empty regraph in
      let regraph =
        IntSet.fold
          (fun key acc ->
            let iset = IntMap.find_err "rem_node_in_graph 4" key acc in
            let iset = IntSet.union iset set in
            let iset = IntSet.remove id iset in
            let iset = IntSet.remove key iset in
            IntMap.add key iset acc
           ) set regraph in
      adgraph, regraph, set

    (* Add a set of variables in the two graphs *)
    let add_set_in_graph (set: IntSet.t) (x: t) =
      let ssmap (ls: IntSet.t) (rs: IntSet.t) (graph: IntSet.t IntMap.t) =
        IntSet.fold
          (fun lelt acc ->
            IntSet.fold
              (fun relt iacc ->
                if lelt = relt then iacc
                else
                  let lset = IntMap.find_err "add_set_in_graph 1" lelt iacc in
                  let iacc = IntMap.add lelt (IntSet.add relt lset) iacc in
                  let rset = IntMap.find_err "add_set_in_graph 2" relt iacc in
                  IntMap.add relt (IntSet.add lelt rset) iacc
               ) rs acc
           ) ls graph in
      let lastVars =
        List.fold_left
          (fun acc elt -> IntSet.union elt acc) IntSet.empty x.t_lastVar in
      let adgraph = ssmap set lastVars x.t_adGraph in
      let regraph = ssmap set set x.t_reGraph in
      let lastVar =
        if List.length x.t_lastVar > 2  then
          List.tl x.t_lastVar
        else x.t_lastVar in
      let lastVar = List.append lastVar (set::[]) in
      { x with
        t_adGraph = adgraph;
        t_reGraph = regraph;
        t_lastVar = lastVar }

    (* Add a set of variables to a set of packs *)
    let add_vars_in_nums (vs: IntSet.t) (ns: IntSet.t) (x: t) =
      let vsnum = IntSet.fold Dn.add_node vs Dn.top in
      let vsnum =
        IntSet.fold
          (fun elt acc ->
            if IntSet.mem elt x.t_freeVar then acc
            else
              let (_, num, vset) =
                IntMap.find_err "add_vars_in_nums 1"
                  (IntMap.find_err "add_vars_in_nums 2"
                     (IntSet.min_elt
                        (IntMap.find_err "addvar in num 3" elt x.t_varGroup))
                     x.t_groupPack) x.t_pack in
              let inter = IntSet.inter vset vs in
              let num = IntSet.fold Dn.rem_node (IntSet.diff vset inter) num in
              let num = IntSet.fold Dn.add_node (IntSet.diff vs inter) num in
              (* some nums may be visited more than once,
               * performance can be improved *)
              Dn.meet acc num
          ) vs vsnum in
      let x =
        IntSet.fold
          (fun group acc ->
            if IntMap.mem group acc.t_groupPack then
              let pack_id =
                IntMap.find_err "add_vars_in_nums 3" group acc.t_groupPack in
              let (num_id, num, vset) =
                IntMap.find_err "add_vars_in_nums 4" pack_id acc.t_pack in
              if IntSet.subset vs vset then acc
              else
                let inter = IntSet.inter vset vs in
                let num = IntSet.fold Dn.add_node (IntSet.diff vs inter) num in
                let tvsnum =
                  IntSet.fold Dn.add_node (IntSet.diff vset inter) vsnum in
                let num = Dn.meet num tvsnum in
                let nnum_id = get_num_counter () in
                let npack_id = get_pack_counter () in
                let vset = IntSet.union vset vs in
                let npack =
                  IntMap.add npack_id (nnum_id, num, vset) acc.t_pack in
                let npack = IntMap.remove pack_id npack in
                let ngroupPack = IntMap.add group npack_id acc.t_groupPack in
                { acc with
                  t_pack = npack;
                  t_groupPack = ngroupPack }
            else acc
          ) ns x in
      let nfreeVar = IntSet.fold IntSet.remove vs x.t_freeVar in
      let nvarGroup =
        IntSet.fold
          (fun elt acc ->
            if IntMap.mem elt acc then
              let aset = IntMap.find_err "add_vars_in_nums 5" elt acc in
              let aset = IntSet.union aset ns in
              IntMap.add elt aset acc
            else
              IntMap.add elt ns acc
          ) vs x.t_varGroup in
      { x with
        t_freeVar = nfreeVar;
        t_varGroup = nvarGroup; }

    (* Remove a set of variables in a set of packs *)
    let rem_vars_in_nums (vs: IntSet.t) (ns: IntSet.t) (x: t) =
      if IntSet.is_empty vs then x
      else
        IntSet.fold
          (fun n acc ->
            if IntMap.mem n acc.t_groupPack then
              let pack_id =
                IntMap.find_err "rem_vars_in_nums 1" n acc.t_groupPack in
              let (num_id, num, vset) =
                IntMap.find_err "rem_vars_in_nums 2" pack_id acc.t_pack in
              let vars_to_remove = IntSet.inter vset vs in
              if IntSet.is_empty vars_to_remove then acc
              else
                let num = IntSet.fold Dn.rem_node vars_to_remove num in
                let vset = IntSet.diff vset vars_to_remove in
                let npack, ngroupPack =
                  if IntSet.is_empty vset then
                    let npack = IntMap.remove pack_id acc.t_pack in
                    let ngroupPack = IntMap.remove n acc.t_groupPack in
                    npack, ngroupPack
                  else
                    let nnum_id = get_num_counter () in
                    let npack_id = get_pack_counter () in
                    let npack =
                      IntMap.add npack_id (nnum_id, num, vset) acc.t_pack in
                    let npack = IntMap.remove pack_id npack in
                    let ngroupPack = IntMap.add n npack_id acc.t_groupPack in
                    npack, ngroupPack in
                let nvarGroup =
                  IntMap.fold
                    (fun key groups iacc ->
                      let groups =
                        if IntSet.mem key vars_to_remove then
                          IntSet.remove n groups
                      else groups in
                      if IntSet.is_empty groups then
                        IntMap.remove key iacc
                      else IntMap.add key groups iacc
                    ) acc.t_varGroup acc.t_varGroup in
                let nfreeVar = IntSet.filter
                  (fun elt -> not (IntMap.mem elt nvarGroup)) vars_to_remove in
                let nfreeVar = IntSet.union nfreeVar acc.t_freeVar in
                { acc with
                  t_pack = npack;
                  t_groupPack = ngroupPack;
                  t_varGroup = nvarGroup;
                  t_freeVar = nfreeVar; }
            else acc
          ) ns x

    (* Rename a node in the graph *)
    let rename_in_graph (old: int) (frh: int) (x: t) =
      let rename_in_one (o: int) (f: int) (graph: IntSet.t IntMap.t) =
        let dsts = IntMap.find_err "rename_in_graph 1" o graph in
        let graph = IntSet.fold
            (fun elt acc ->
              let set = IntMap.find_err "rename_in_graph 2" elt acc in
              let set = IntSet.add f (IntSet.remove o set) in
              IntMap.add elt set acc
             ) dsts graph in
        IntMap.add f dsts (IntMap.remove o graph) in
      let adgraph = rename_in_one old frh x.t_adGraph in
      let regraph = rename_in_one old frh x.t_reGraph in
      { x with
        t_adGraph = adgraph;
        t_reGraph = regraph;}

    (* Get the upper bound for two graphs *)
    let unify_graph (lx: t) (rx: t) =
      let edge_join f =
        IntMap.merge
          (fun _ aset bset ->
            match aset,bset with
            | Some iaset, Some ibset -> Some (f iaset ibset)
            | _, _ -> error "non-consistent nodes in unify graph" ) in
      let nadgraph = edge_join IntSet.union lx.t_adGraph rx.t_adGraph in
      let nregraph = edge_join IntSet.inter lx.t_reGraph rx.t_reGraph in
      { lx with
        t_adGraph = nadgraph;
        t_reGraph = nregraph },
      { rx with
        t_adGraph = nadgraph;
        t_reGraph = nregraph }

    (* Get the upper bound for two packs.
     * The right side pack is renormalized by the left one *)
    let unify_num (model_x: t) (mater_x: t) =
      let mater_x =
        IntMap.fold
          (fun pack_id (num_id, num, vset) acc ->
            if IntMap.mem pack_id acc.t_pack then acc
            else
              let set_distance (a: IntSet.t) (b: IntSet.t) =
                let diff_a = IntSet.diff a b in
                let diff_b = IntSet.diff b a in
                IntSet.cardinal (IntSet.union diff_a diff_b) in
              let opGroup, opRvset =
                IntMap.fold
                  (fun agroup apck (ac_group, acrvset) ->
                    if IntMap.mem apck model_x.t_pack then (ac_group, acrvset)
                    else
                      let _, _, iset =
                        IntMap.find_err "unify_num 2" apck acc.t_pack in
                      match acrvset with
                      | None -> Some agroup, Some iset
                      | Some set ->
                          if set_distance set vset > set_distance vset iset then
                            Some agroup, Some iset
                          else ac_group,acrvset
                  ) acc.t_groupPack (None, None) in
              match opGroup, opRvset with
              | Some agroup, Some aset ->
                  let acc =
                    add_vars_in_nums (IntSet.diff vset aset)
                      (IntSet.singleton agroup) acc in
                  let npack_id =
                    IntMap.find_err "unify_num 4" agroup acc.t_groupPack in
                  let nnum_id, nnum, nset =
                    IntMap.find_err "unify_num 5" npack_id acc.t_pack in
                  { acc with
                    t_groupPack = IntMap.add agroup pack_id acc.t_groupPack;
                    t_pack = IntMap.add pack_id (nnum_id, nnum, nset)
                      (IntMap.remove npack_id acc.t_pack) }
              | None, None ->
                  let ngroup_id = get_pack_counter () in
                  let nnum_id = get_num_counter () in
                  let acc =
                    { acc with
                      t_groupPack = IntMap.add ngroup_id pack_id
                        acc.t_groupPack;
                      t_pack = IntMap.add pack_id
                        (nnum_id, Dn.top, IntSet.empty) acc.t_pack } in
                  let acc =
                    add_vars_in_nums vset (IntSet.singleton ngroup_id) acc in
                  let npack_id =
                    IntMap.find_err "unify_num 8" ngroup_id acc.t_groupPack in
                  let nnum_id, nnum, nset =
                    IntMap.find_err "unify_num 9" npack_id acc.t_pack in
                  { acc with
                    t_groupPack = IntMap.add ngroup_id pack_id acc.t_groupPack;
                    t_pack = IntMap.add pack_id (nnum_id, nnum, nset)
                      (IntMap.remove npack_id acc.t_pack) }
              | _, _ -> error "unexpected case in unify form"
          ) model_x.t_pack mater_x in
      IntMap.fold
        (fun agroup apid acc ->
          let (_, _, vset) = IntMap.find_err "unify_num 6" apid acc.t_pack in
          if IntMap.mem apid model_x.t_pack then
            let (_, _, mset) =
              IntMap.find_err "unify_num 7" apid model_x.t_pack in
            let acc =
              rem_vars_in_nums (IntSet.diff vset mset)
                (IntSet.singleton agroup) acc in
            let npack_id =
              IntMap.find_err "unify_num 10" agroup acc.t_groupPack in
            let nnum_id, nnum, nset =
              IntMap.find_err "unify_num 11" npack_id acc.t_pack in
            { acc with
              t_groupPack = IntMap.add agroup apid acc.t_groupPack;
              t_pack = IntMap.add apid (nnum_id, nnum, nset)
                (IntMap.remove npack_id acc.t_pack) }
          else
            rem_vars_in_nums vset (IntSet.singleton agroup) acc
        ) mater_x.t_groupPack mater_x

    (* Project a variable *)
    let project_var (v: int) (x: t) =
      if IntSet.mem v x.t_freeVar then x
      else
        begin
          assert (IntMap.mem v x.t_varGroup);
          let adgraph, regraph, set =
            rem_node_in_graph v x.t_adGraph x.t_reGraph in
          let allgroups = IntMap.find_err "project_var 1" v x.t_varGroup in
          let realgroups =
            IntSet.filter
              (fun elt ->
                let pack_id =
                  IntMap.find_err "groups pack" elt x.t_groupPack in
                let (_, _, vset) =
                  IntMap.find_err "groups revise" pack_id  x.t_pack in
                not (IntSet.cardinal vset = 1)
              ) allgroups in
          let x = { x with
                    t_adGraph = adgraph;
                    t_reGraph = regraph } in
          let x = rem_vars_in_nums (IntSet.singleton v) allgroups x in
          if IntSet.cardinal realgroups > 1 then
            add_vars_in_nums set realgroups x
          else x
        end

    (* Add or remove a variable *)
    let add_node (id: int) (x: t) =
      { x with
        t_freeVar = IntSet.add id x.t_freeVar;
        t_adGraph = IntMap.add id IntSet.empty x.t_adGraph;
        t_reGraph = IntMap.add id IntSet.empty x.t_reGraph; }

    let rem_node (id: int) (x: t) =
      let x = project_var id x in
      let nlastVar = List.map (fun elt -> IntSet.remove id elt) x.t_lastVar in
      assert (IntSet.mem id x.t_freeVar);
      let x = { x with
                t_freeVar = IntSet.remove id x.t_freeVar;
                t_lastVar = nlastVar;
                t_adGraph = IntMap.remove id  x.t_adGraph;
                t_reGraph = IntMap.remove id  x.t_reGraph;} in
      x

    (* Upper bound of two abstract states *)
    let upper_bnd (f: Dn.t -> Dn.t -> Dn.t) (lx: t) (rx: t) =
      let lx,rx = unify_graph lx rx in
      let rx = unify_num lx rx in
      assert (IntMap.cardinal lx.t_pack = IntMap.cardinal rx.t_pack);
      let p =
        IntMap.merge
          (fun _  lpack rpack ->
            match lpack, rpack with
            | Some (lnum_id, lnum, vset), Some (rnum_id, rnum, _) ->
                if lnum_id = rnum_id then
                  Some (lnum_id, lnum, vset)
                else
                  Some (get_num_counter (), f lnum rnum, vset)
            | _, _ -> error "non compatible case in upper_bnd"
          ) lx.t_pack rx.t_pack in
      { lx with t_pack = p }

    let join (lx: t) (rx: t) =
      upper_bnd Dn.join lx rx

    let widen (lx: t) (rx: t) =
      upper_bnd Dn.widen lx rx

    let meet (lx: t) (rx: t) =
      upper_bnd Dn.meet lx rx

    (* Comparisons *)
    let is_le (lx: t) (rx: t) =
      let lx = unify_num rx lx in
      assert (IntMap.cardinal lx.t_pack = IntMap.cardinal rx.t_pack);
      not
        (IntMap.exists
           (fun pack_id (lnum_id, lnum, vset) ->
             let rnum_id, rnum, _ =
               IntMap.find_err "is_le 1" pack_id rx.t_pack in
             if lnum_id = rnum_id then
               false
             else
               not (Dn.is_le lnum rnum)
           ) lx.t_pack)

    (* Gather a set of variables to a single set *)
    let gather_vars (set: IntSet.t) (x: t) (maxp: int): t * int =
      assert (not (IntSet.is_empty set));
      let create_pack (var: int) (x: t) =
        let group_id = get_pack_counter () in
        let pack_id = get_pack_counter () in
        let num_id = get_num_counter () in
        { x with
          t_freeVar = IntSet.remove var x.t_freeVar;
          t_varGroup = IntMap.add var (IntSet.singleton group_id) x.t_varGroup;
          t_groupPack = IntMap.add group_id pack_id x.t_groupPack;
          t_pack = IntMap.add pack_id
            (num_id, (Dn.add_node var Dn.top), IntSet.singleton var)
            x.t_pack} in
      let subset = IntSet.filter
          (fun elt -> IntMap.mem elt x.t_varGroup
          ) set in
      let avar, x =
        if IntSet.is_empty subset then
          let avar = IntSet.min_elt set in
          avar, create_pack avar x
        else
          let avar = IntSet.min_elt subset in
          let group =
            IntSet.min_elt
              (IntMap.find_err "gather_vars 1" avar x.t_varGroup) in
          let pack_id =
            IntMap.find_err "gather_vars 2"  group x.t_groupPack in
          let _, _, vset = IntMap.find_err "gather vars 3" pack_id x.t_pack in
          if IntSet.cardinal vset < maxp then
            avar, x
          else
            avar, create_pack avar x in
      let set = IntSet.remove avar set in
      let group =
        IntSet.min_elt (IntMap.find_err "gather_vars 1" avar x.t_varGroup) in
      (add_vars_in_nums set (IntSet.singleton group) x), group

     (* Gurad and Assignment *)
    let guard (b: bool) (cons: n_cons) (x: t) =
      let set = n_cons_fold IntSet.add cons IntSet.empty in
      let x, group = gather_vars set x max_pack in
      let pack_id = IntMap.find_err "guard 1" group x.t_groupPack in
      let num_id, num, vset = IntMap.find_err "guard 2" pack_id x.t_pack in
      let npack =
        IntMap.add pack_id
          (get_num_counter (), Dn.guard b cons num, vset) x.t_pack in
      let x = { x with t_pack = npack } in
      add_set_in_graph set x

    let assign (dst: int) (expr: n_expr) (x: t) =
      let set = n_expr_fold IntSet.add expr IntSet.empty in
      if IntSet.mem dst set then
        let adgraph, regraph, nset =
          rem_node_in_graph dst x.t_adGraph x.t_reGraph in
        let set = IntSet.union nset set in
        let x, group = gather_vars set x max_pack in
        let groups = IntMap.find_err "assign 1" dst x.t_varGroup in
        let groups = IntSet.remove group groups in
        let x = rem_vars_in_nums (IntSet.singleton dst) groups x in
        let x = { x with
                  t_adGraph = adgraph;
                  t_reGraph = regraph } in
        let x = add_set_in_graph set x in
        let pack_id = IntMap.find_err "assign 2" group x.t_groupPack in
        let (num_id, num, vset) = IntMap.find_err "assign 3" pack_id x.t_pack in
        let npack =
          IntMap.add pack_id
            (get_num_counter (), Dn.assign dst expr num, vset) x.t_pack in
        { x with t_pack = npack }
      else
        let x = project_var dst x in
        let set = IntSet.add dst set in
        let x, group = gather_vars set x max_pack in
        let x = add_set_in_graph set x in
        let pack_id = IntMap.find_err "assign 4" group x.t_groupPack in
        let num_id, num, vset = IntMap.find_err "assign 5" pack_id x.t_pack in
        let npack =
          IntMap.add pack_id
            (get_num_counter (), Dn.assign dst expr num, vset) x.t_pack in
        { x with t_pack = npack }

    (* Renaming *)
    let vars_srename (nr: 'a node_mapping) (x: t) =
      let x = IntSet.fold rem_node nr.nm_rem x in
      let nr = { nr with nm_rem = IntSet.empty } in
      IntMap.fold
        (fun old (frsh, set) acc ->
          let acc = rename_in_graph old frsh acc in
          let acc =
            if IntSet.mem old acc.t_freeVar then
              { acc with
                t_freeVar = IntSet.add frsh (IntSet.remove old acc.t_freeVar) }
            else
              let lastVar =
                List.map
                  (fun s ->
                    if IntSet.mem old s then
                      IntSet.add frsh (IntSet.remove old s)
                    else s
                  ) acc.t_lastVar in
              let groups =
                IntMap.find_err "vars_srename 1" old acc.t_varGroup in
              let npack, ngroupPack =
                IntSet.fold
                  (fun group (ipack, igroupPack) ->
                    let pack_id =
                      IntMap.find_err "vars_srename 2" group igroupPack in
                    let num_id, num, vset =
                      IntMap.find_err "vars_srename 3" pack_id ipack in
                    let num =
                      Dn.vars_srename
                        { nr with
                          nm_map = IntMap.singleton old (frsh,IntSet.empty) }
                        num in
                    let vset = IntSet.add frsh (IntSet.remove old vset) in
                    let npack_id = get_pack_counter () in
                    let ipack =
                      IntMap.add npack_id (num_id, num, vset)
                        (IntMap.remove pack_id ipack) in
                    let igroupPack = IntMap.add group npack_id igroupPack in
                    ipack, igroupPack
                  ) groups (acc.t_pack, acc.t_groupPack) in
              let nvarGroup =
                IntMap.add frsh groups (IntMap.remove old acc.t_varGroup) in
              { acc with
                t_pack = npack;
                t_groupPack = ngroupPack;
                t_varGroup = nvarGroup;
                t_lastVar = lastVar } in
          IntSet.fold
            (fun elt iacc ->
              let iacc = add_node elt iacc in
              guard true (Nc_cons (Tcons1.EQ, (Ne_var elt), (Ne_var frsh))) iacc
            ) set acc
         ) nr.nm_map x

    (* Get all nodes in the graphs *)
    let all_nodes (x: t) =
      IntMap.fold (fun key _ acc -> IntSet.add key acc) x.t_adGraph IntSet.empty

    let check_nodes (set: IntSet.t) (x: t) =
      let all = all_nodes x in
      IntSet.is_empty (IntSet.diff set all)

    let nodes_filter (set: IntSet.t) (x: t) =
      let all = all_nodes x in
      let toremove = IntSet.diff all set in
      IntSet.fold rem_node toremove x

    (** Comparison, Join and Widening operators *)
    (** Checks a constraint is satisfied (i.e., attempts to prove it) *)
    let sat (cons: n_cons) (x: t) =
      let set = n_cons_fold IntSet.add cons IntSet.empty in
      let x, group = gather_vars set x 1000 in
      let pack_id = IntMap.find_err "sat 1" group x.t_groupPack in
      let (_, num, _) = IntMap.find_err "sat 2" pack_id x.t_pack in
      Dn.sat cons num

    (** Transfer functions *)
    (** Utilities for the abstract domain *)
    let simplify_n_expr  x expr = expr

    let get_svars (x: t) =
      all_nodes x

    (** Summarizing dimensions related operations *)
    let expand (old: int) (frsh: int) (x: t) =
      let x = add_node frsh x in
      guard true (Nc_cons (Tcons1.EQ, (Ne_var old), (Ne_var frsh))) x

    let compact (old: int) (frsh: int) (x: t) =
      let x, group =
        gather_vars (IntSet.add frsh (IntSet.singleton old)) x max_pack in
      let oldgroups = IntMap.find_err "compact 1" old x.t_varGroup in
      let frshgroups = IntMap.find_err "compact 2" frsh x.t_varGroup in
      let x =
        rem_vars_in_nums
          (IntSet.singleton old) (IntSet.remove group oldgroups) x in
      let x =
        rem_vars_in_nums
          (IntSet.singleton frsh) (IntSet.remove group frshgroups) x in
      let pack_id = IntMap.find_err "compact 3" group x.t_groupPack in
      let (num_id, num, vset) = IntMap.find_err "compact 4" pack_id x.t_pack in
      let num = Dn.compact old frsh num in
      let npack_id = get_pack_counter () in
      let vset = IntSet.remove frsh vset in
      let nnum_id = get_num_counter () in
      let npack =
        IntMap.add npack_id (nnum_id, num, vset)
          (IntMap.remove pack_id x.t_pack) in
      let ngroupPack = IntMap.add group npack_id x.t_groupPack in
      let nvarGroup = IntMap.remove frsh x.t_varGroup in
      let nlastVar = List.map (fun elt -> IntSet.remove frsh elt) x.t_lastVar in
      { x with
        t_pack = npack;
        t_groupPack = ngroupPack;
        t_varGroup = nvarGroup;
        t_lastVar = nlastVar }

    (* Forget constraints on a variable *)
    let forget (id: int) (x: t) =
      project_var id x

    (** Export of range information *)
    let bound_variable (id: int) (x: t) =
      if IntSet.mem id x.t_freeVar then
        { intv_inf = None; intv_sup = None }
      else
        let group =
          IntSet.min_elt (IntMap.find_err "bound_variable 1" id x.t_varGroup) in
        let pack_id = IntMap.find_err "bound_variable 2" group x.t_groupPack in
        let _, num, _ = IntMap.find_err "bound_variable 3" pack_id x.t_pack in
        Dn.bound_variable id num

    (* Get the set of variables that equal to a given variable *)
    let get_eq_class (id: int) (x: t) =
      if IntSet.mem id x.t_freeVar then
        IntSet.empty
      else
        let groups = IntMap.find_err "get_eq_class 1" id x.t_varGroup in
        IntSet.fold
          (fun group acc ->
            let pack_id =
              IntMap.find_err "get_eq_class 2" group x.t_groupPack in
            let _, num, _ = IntMap.find_err "get_eq_class 3" pack_id x.t_pack in
            let iset = Dn.get_eq_class id num in
            IntSet.union iset acc
          ) groups IntSet.empty
  end: DOM_NUM_NB)
