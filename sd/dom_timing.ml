(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: dom_timing.ml
 **       Timing of abstract domains
 ** Xavier Rival, 2013/08/31 *)
open Data_structures
open Dom_sig
open Graph_sig
open Set_sig

open Timer


(** Timing support for value+set domains *)
module Dom_valset_timing =
  functor (D: DOM_VALSET) ->
  (struct
    module T = Timer.Timer_Mod( struct let name = "Valset" end )
    type t = D.t
    let init_inductives = T.app2 "init_inductives" D.init_inductives
    let bot = D.bot
    let is_bot = T.app1 "is_bot" D.is_bot
    let top = D.top
    let t_2stri = T.app3 "t_2stri" D.t_2stri
    let check_nodes = T.app2 "check_nodes" D.check_nodes
    let sv_add ?(mark: bool = true) = T.app2 "sv_add" (D.sv_add ~mark: mark)
    let sv_rem = T.app2 "sv_rem" D.sv_rem
    let setv_add ?(root = false) ?(kind = None) ?(name = None) =
      T.app2 "setv_add" (D.setv_add ~root:root ~kind:kind ~name:name)
    let setv_rem = T.app2 "setv_rem" D.setv_rem
    let setv_is_root = T.app2 "setv_is_root" D.setv_is_root
    let setv_col_root = T.app1 "setv_col_root" D.setv_col_root
    let symvars_srename ?(mark: bool = true) o n =
      T.app2 "symvars_srename"
        (D.symvars_srename ~mark: mark o n)
    let sve_sync_top_down = T.app2 "sve_sync_top_down" D.sve_sync_top_down
    let symvars_check = T.app2 "symvars_check" D.symvars_check
    let symvars_filter a ?(set_vars: IntSet.t = IntSet.empty) b =
      T.app1 "symvars_filter" (D.symvars_filter a ~set_vars: set_vars) b
    let symvars_merge = T.app6 "symvars_merge" D.symvars_merge
    let is_le = T.app2 "is_le" D.is_le
    let upper_bnd = T.app3 "upper_bnd" D.upper_bnd
    let sat = T.app2 "sat" D.sat
    let set_sat = T.app2 "set_sat" D.set_sat
    let guard = T.app3 "guard" D.guard
    let set_guard = T.app2 "set_guard" D.set_guard
    let assign = T.app3 "assign" D.assign
    let write_sub = T.app4 "write_sub" D.write_sub
    let simplify_n_expr = T.app2 "simplify_n_expr" D.simplify_n_expr
    let sv_array_add = T.app4 "sv_array_add" D.sv_array_add
    let sv_array_address_add =
      T.app2 "sv_array_address_add" D.sv_array_address_add
    let is_array_address = T.app2 "is_array_address" D.is_array_address
    let sv_array_deref = T.app3 "sv_array_deref" D.sv_array_deref
    let sv_array_materialize =
      T.app3 "sv_array_materialize" D.sv_array_materialize
    let is_submem_address = T.app2 "is_submem_address" D.is_submem_address
    let is_submem_content = T.app2 "is_submem_content" D.is_submem_content
    let submem_read = T.app5 "submem_read" D.submem_read
    let submem_deref = T.app5 "submem_deref" D.submem_deref
    let submem_localize = T.app2 "submem_localize" D.submem_localize
    let submem_bind = T.app4 "submem_bind" D.submem_bind
    let check = T.app2 "check" D.check
    let unfold = T.app4 "unfold" D.unfold
    let assume = T.app2 "assume" D.assume
  end: DOM_VALSET)

(** Timing support for memory_low domains *)
module Dom_mem_low_timing =
  functor (D: DOM_MEM_LOW) ->
  (struct
    module T = Timer.Timer_Mod( struct let name = D.module_name end )
    let module_name = D.module_name
    type t = D.t
    let init_inductives = T.app2 "init_inductives" D.init_inductives
    let inductive_is_allowed = T.app1 "ind_is_allowed"D.inductive_is_allowed
    let sve_sync_bot_up = T.app1 "sve_sync_bot_up" D.sve_sync_bot_up
    let bot = D.bot
    let is_bot = T.app1 "is_bot" D.is_bot
    let top = T.app1 "top" D.top
    let t_2stri = T.app2 "t_2stri" D.t_2stri
    let t_2str = T.app1 "t_2str" D.t_2str
    let ext_output = T.app4 "ext_output" D.ext_output
    let sv_is_allowed ?(attr: node_attribute = Attr_none) =
      T.app3 "sv_is_allowed" (D.sv_is_allowed ~attr: attr)
    let sv_add_fresh ?(attr: node_attribute = Attr_none) ?(root: bool = false) =
      T.app3 "sv_add_fresh" (D.sv_add_fresh ~attr: attr ~root: root)
    let sv_get_info = T.app2 "sv_get_info" D.sv_get_info
    let gc = T.app2 "gc" D.gc
    let encode = T.app3 "encode" D.encode
    let is_le = T.app4 "is_le" D.is_le
    let join = T.app7 "join" D.join
    let directed_weakening = T.app5 "weaken" D.directed_weakening
    let local_abstract = T.app2 "local_abstract" D.local_abstract
    let cell_create ?(attr:node_attribute = Attr_none) =
      T.app4 "cell_create" (D.cell_create ~attr:attr)
    let cell_delete ?(free: bool = false) ?(root: bool = false) =
      T.app2 "cell_delete" (D.cell_delete ~free:free ~root:root)
    let cell_read = T.app3 "cell_read" D.cell_read
    let cell_resolve = T.app3 "cell_resolve" D.cell_resolve
    let cell_write = T.app5 "cell_write" D.cell_write
    let guard = T.app2 "guard" D.guard
    let sat = T.app2 "sat" D.sat
    let setv_add_fresh = T.app3 "setv_add_fresh" (D.setv_add_fresh)
    let setv_delete = T.app2 "setv_delete" (D.setv_delete)
    let check = T.app2 "check" D.check
    let assume = T.app2 "assume" D.assume
    let ind_unfold = T.app3 "ind_unfold" D.ind_unfold
  end: DOM_MEM_LOW)

module Dom_maya_timing = functor (Dm: DOM_MAYA) ->
  (struct
    module T = Timer.Timer_Mod(struct let name = "Maya" end)
    type t = Dm.t
    let bot = Dm.bot
    let t_2stri = T.app3 "t_stri" Dm.t_2stri
    let is_bot = T.app1 "is_bot" Dm.is_bot
    let assert_non_empty = T.app2 "assert_non_empty" Dm.assert_non_empty
    let rem_node = T.app2 "rem_node" Dm.rem_node
    let add_node = T.app5 "add_noe" Dm.add_node
    let bound_variable = T.app2 "bound_variable" Dm.bound_variable
    let scalar_to_single = T.app2 "scalar_to_single" Dm.scalar_to_single
    let scalar_to_exist = T.app2 "scalar_to_exist" Dm.scalar_to_exist
    let size_assign = T.app3 "size_assign" Dm.size_assign
    let size_guard = T.app2 "size_guard" Dm.size_guard
    let upper_bnd = T.app3 "upper_bnd" Dm.upper_bnd
    let is_le = T.app2 "is_le" Dm.is_le
    let guard_s = T.app3 "guard_s" Dm.guard_s
    let guard_w = T.app3 "guard_w" Dm.guard_w
    let sat_s = T.app2 "sat_s" Dm.sat_s
    let sat_w = T.app2 "sat_w" Dm.sat_w
    let update_subs_set = T.app3 "update_subs_set" Dm.update_subs_set
    let update_subs_elt = T.app3 "update_subs_elt" Dm.update_subs_elt
    let update_add = T.app3 "update_add" Dm.update_add
    let update_rem = T.app3 "update_rem" Dm.update_rem
    let expand = T.app3 "expand" Dm.expand
    let compact = T.app3 "compact" Dm.compact
    let rename_var = T.app3 "rename_var" Dm.rename_var
    let symvars_filter = T.app2 "symvars_filter" Dm.symvars_filter
    let forget = T.app2 "forget" Dm.forget
    let is_incl = T.app2 "is_incl" Dm.is_incl
    let narrow_set_vars = T.app1 "narrow_set_vars" Dm.narrow_set_vars
    let top = Dm.top
  end: DOM_MAYA)
