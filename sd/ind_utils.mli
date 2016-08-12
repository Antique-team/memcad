(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ind_utils.mli
 **       basic operations on inductive definitions
 ** Xavier Rival, 2011/06/30 *)
open Data_structures
open Ind_sig
open Sv_sig

(** This file stores the sets of inductive definitions to use for a given
 ** analysis; those sets should be made dynamic if the analysis tries to
 ** infer or refine inductive definitions *)


(** To string *)
(* Node types *)
val ntyp_2str: ntyp -> string
(* Parameters *)
val formal_arg_2str: formal_arg -> string
val formal_main_arg_2str: formal_main_arg -> string
val formal_ptr_arg_2str: formal_ptr_arg -> string
val formal_int_arg_2str: formal_int_arg -> string
val formal_set_arg_2str: formal_set_arg -> string
val formal_ptr_args_2str: formal_ptr_args -> string
val formal_int_args_2str: formal_int_args -> string
val formal_set_args_2str: formal_set_args -> string
val indcall_2str: indcall -> string
(* Heap formulas *)
val cell_2str: cell -> string
val heapatom_2str: heapatom -> string
val hform_2str: hform -> string
(* Pure formulas *)
val sexpr_2str: sexpr -> string
val aexpr_2str: aexpr -> string
val sform_2str: sform -> string
val aform_2str: aform -> string
val pform_atom_2str: pformatom -> string
val pform_2str: pform -> string
(* Rules *)
val ir_kind_2str: ir_kind -> string
val irule_2str: irule -> string
(* Inductive definitions *)
val ind_2str: ind -> string
val rules_to_string: ind -> string
val rules_to_file: string -> ind list -> unit


(** Visitor *)
val visitor: ('a -> int -> 'a) -> ('a -> int -> 'a) -> ('a -> int -> 'a)
    -> ('a -> hform -> 'a) * ('a -> pform -> 'a)
val visitor_hform: ('a -> int -> 'a) -> ('a -> int -> 'a) -> ('a -> int -> 'a)
    -> 'a -> hform -> 'a
val visitor_pform: ('a -> int -> 'a) -> ('a -> int -> 'a) -> ('a -> int -> 'a)
    -> 'a -> pform -> 'a

(** Equality test *)
val compare: ind -> ind -> int

(** Operations on ntyp *)
val ntyp_merge: ntyp -> ntyp -> ntyp

(** Nodes analysis: instantiation of types *)
val indnodes_analysis: ind -> ind


(** Inductive definitions analyses:
 *  We list their interfaces below for the sake of documentation
 *  (the functions below probably never need be called in the rest
 *   of the code) *)

(** Inductive parameters use analysis:
 *  For each rule, we compute the set of parameters that are NOT used,
 *  so as to allow for parameters weakening later in join *)
val indpar_use_analysis: ind -> ind
(* Functions to query the result of this analysis *)
val par_may_use_rules_emp: formal_aux_arg -> ind -> bool
val par_may_use_rules_notemp: formal_aux_arg -> ind -> bool
val no_par_use_rules_emp: ind -> bool
val no_par_use_rules_notemp: ind -> bool

(** Nodes analysis: populates the map of types
 *  - either checks the types are coherent if the map is already full;
 *  - or populates map ir_typ with "Ntraw" record (no type assumption) *)
val indnodes_analysis: ind -> ind

(** Inductive "direction", that is paths traversed from one ind call to
 *  the next one:
 *  This analysis is very incomplete
 *  it considers only paths of the form this.f->$i * $i.ind(...) *)
val inddir_analysis: ind -> ind

(** Inductive definition parameters analysis
 *  This analysis aims at inferring whether parameters of inductive
 *  definitions may be constant or additive, which helps algorithms
 *  (non local unfolding, join...) *)
val pars_rec_top: pars_rec
val par_rec_2str: par_rec -> string
val pars_rec_2str: pars_rec -> string
val indpars_analysis: ind -> ind

(** Computation of the inductives that have ONE rule corresponding to:
 *  - an empty region;
 *  - and a null pointer.
 *  This information can be used in order to speed up materialization. *)
val empty_heap_rule_analysis: ind -> ind

(** Computation of parameters which may denote prev pointers.
 *  This information is important for backward unfolding. *)
val bwdpar_analysis: ind -> ind

(** Computation of rules that are useful for segments:
 *  only rules that have at least one recursive call need be considered
 *  for segments *)
val ind_calc_segrules: ind -> ind

(** Computation of fields that are equal to parameters *)
val ind_field_pars: ind -> ind

(** Computation of ir_kind fields
 *  i.e., when a rule is either necessary null (emp) or non null (non emp) *)
val ind_rules_kind: ind -> ind

(** Checks whether an inductive definition resembles a list inductive def
 ** (this is used in order to feed data into the list domain) *)
val ind_list_check: ind -> ind


(** Set of inductive definitions *)
val ind_defs: ind StringMap.t ref
val ind_bind: string StringMap.t ref
val ind_prec: string list ref

(* Initialization from parsing *)
val ind_init: p_iline list -> unit

(* Extraction of an inductive *)
val ind_find: string -> ind

(* Retrieve an inductive name from type *)
val indname_find: string -> string
