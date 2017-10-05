(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: nd_timing.ml
 **       Timing of value abstract domains (numeric, set)
 ** Xavier Rival, 2016/07/19 *)
open Nd_sig
open Set_sig

open Timer

(**  Timing support for numeric domains (layount NUM_NB),
 **  including Apron *)
module Dom_num_nb_timing = functor (Dn: DOM_NUM_NB) ->
  (struct 
    module T = Timer.Timer_Mod( struct let name = "Apron" end )
    type t = Dn.t
    let module_name = "dom_num_nb_timing"
    let config_2str = T.app1 "Apron.config_2str" Dn.config_2str
    let top = Dn.top
    let is_bot = T.app1 "Apron.is_bot" Dn.is_bot
    let bound_variable = T.app2 "Apron.bound_variable" Dn.bound_variable
    let vars_srename x y = T.app2 "Apron.vars_srename" Dn.vars_srename x y
    let expand = T.app3 "Apron.expand" Dn.expand
    let compact = T.app3 "Apron.compact" Dn.compact
    let meet = T.app2 "Apron.meet" Dn.meet
    let sv_forget = T.app2 "Apron.forget" Dn.sv_forget
    let simplify_n_expr = T.app1 "Apron.simplify_n_expr" Dn.simplify_n_expr
    let sat = T.app2 "Apron.sat" Dn.sat
    let assign = T.app3 "Apron.assign" Dn.assign
    let guard = T.app3 "Apron.guard" Dn.guard
    let widen = T.app2 "Apron.widen" Dn.widen
    let join = T.app2 "Apron.join" Dn.join
    let nodes_filter = T.app2 "Apron.nodes_filter" Dn.nodes_filter
    let is_le = T.app2 "Apron.is_le" Dn.is_le
    let check_nodes = T.app2 "Apron.check_nodes" Dn.check_nodes
    let get_svs = T.app1 "Apron.get_svs" Dn.get_svs
    let add_node = T.app2 "Apron.add_node" Dn.add_node
    let rem_node = T.app2 "Apron.rem_node" Dn.rem_node
    let t_2stri = T.app3 "Apron.t_2stri" Dn.t_2stri
    let get_eq_class = T.app2 "get_eq_class" Dn.get_eq_class
  end: DOM_NUM_NB)

(** Timing support for set domains *)
module Dom_set_timing = functor (S: DOMSET) ->
  (struct
    module T = Timer.Timer_Mod( struct let name = "SET" end )
    let module_name = "dom_set_timing"
    let config_2str = T.app1 "config_2str" S.config_2str
    type t = S.t
    let bot = S.bot
    let is_bot = T.app1 "is_bot" S.is_bot
    let top = S.top
    let t_2stri = T.app3 "t_2stri" S.t_2stri
    let check_nodes = T.app2 "check_nodes" S.check_nodes
    let sv_add = T.app2 "sv_add" S.sv_add
    let sv_rem = T.app2 "sv_rem" S.sv_rem
    let setv_is_root = T.app2 "setv_is_root" S.setv_is_root
    let setv_col_root = T.app1 "setv_col_root" S.setv_col_root
    let setv_add ?(root = false) ?(kind = None) ?(name = None) =
      T.app2 "setv_add" (S.setv_add ~root:root ~kind:kind ~name:name)
    let setv_rem = T.app2 "setv_rem" S.setv_rem
    let is_le = T.app2 "is_le" S.is_le
    let weak_bnd = T.app2 "weak_bnd" S.weak_bnd
    let upper_bnd = T.app2 "upper_bnd" S.upper_bnd
    let set_guard = T.app2 "set_guard" S.set_guard
    let set_sat = T.app2 "set_sat" S.set_sat
    let sv_forget = T.app2 "sv_forget" S.sv_forget
    let symvars_srename = T.app4 "symvars_srename" S.symvars_srename
    let sve_sync_top_down = T.app2 "sve_sync_top_down" S.sve_sync_top_down
    let symvars_filter = T.app3 "symvars_filter" S.symvars_filter
  end: DOMSET)
