(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ind_sig.ml
 **       data-types for the inductive definitions.
 ** Xavier Rival, 2011/06/29 *)
open Data_structures
open Ast_sig
open Sv_sig


(** Parameter types *)
type indpar_type =
  | It_ptr (* pointer: node not bound by the inductive *)
  | It_num (* numeric: node bound by the inductive; info in the under domain *)
  | It_set (* set:     special range of variable; bound in the under domain *)


(** Parameters in inductive calls *)
(* Occurrence of a variable in an inductive
 * we use various types, depending on the position of the occurence *)
type formal_arg = [
  | `Fa_this           (* main parameter *)
  | `Fa_var_new of int (* new variable *)
  | `Fa_par_int of int (* integer type parameter *)
  | `Fa_par_ptr of int (* pointer type parameter *)
  | `Fa_par_set of int (* set type parameter *) ]
type formal_main_arg = [
  | `Fa_this           (* main parameter *)
  | `Fa_var_new of int (* new variable *) ]
type formal_aux_arg = [
  | `Fa_par_int of int (* integer type parameter *)
  | `Fa_par_ptr of int (* pointer type parameter *)
  | `Fa_par_set of int (* set type parameter *) ]
type formal_ptr_arg = [
  | `Fa_this           (* main parameter *)
  | `Fa_var_new of int (* new variable *)
  | `Fa_par_ptr of int (* pointer type parameter *) ]
type formal_int_arg = [
  | `Fa_var_new of int (* new variable *)
  | `Fa_par_int of int (* integer type parameter *) ]
type formal_set_arg = [
  | `Fa_var_new of int (* new set variable *)
  | `Fa_par_set of int (* set type parameter *) ]
type formal_arith_arg = [ (* pointer or integer *)
  | `Fa_this           (* main parameter *)
  | `Fa_var_new of int (* new variable *)
  | `Fa_par_int of int (* integer type parameter *)
  | `Fa_par_ptr of int (* pointer type parameter *) ]
(* Arguments of a call *)
type formal_ptr_args = formal_ptr_arg list
type formal_int_args = formal_int_arg list
type formal_set_args = formal_set_arg list
(* Inductive call *)
type indcall =
    { ii_maina: formal_main_arg;  (* main parameter *)
      ii_ind:   string;           (* name of called inductive *)
      ii_argp:  formal_ptr_args;  (* list of pointer arguments *)
      ii_argi:  formal_int_args;  (* list of integer arguments *)
      ii_args:  formal_set_args;  (* list of set arguments *) }


(** Cells in inductive definitions *)
(* Cell *)
type cell =
    { ic_off:  Offs.t;          (* offset *)
      ic_size: int;             (* size, in bytes *)
      ic_dest: formal_arith_arg (* destination *) }
(* Heap atom *)
type heapatom =
  | Hacell of cell    (* a cell, to unfold into a points-to edge *)
  | Haind of indcall  (* an inductive, to unfold into segment of inductive *)
(* Heap formula; separating conjunction of heap atoms *)
type hform = heapatom list (* separating conjunction *)


(** Pur formulas, expressions, etc *)
(* set expression (very limited for now; to extend later) *)
type sexpr =
  | Se_var of formal_set_arg                (* a set repr. by a variable *)
  | Se_uplus of formal_set_arg list * formal_arith_arg (* X \uplus { y } *)
  | Se_union of formal_set_arg list * formal_arith_arg (* X \cup Y *)
(* arith expression *)
type aexpr =
  | Ae_cst of int
  | Ae_var of formal_arith_arg
  | Ae_plus of aexpr * aexpr
(* set formula *)
type sform =
  | Sf_mem of formal_arith_arg * formal_set_arg  (* membership *)
  | Sf_equal of formal_set_arg * sexpr           (* equality *)
  | Sf_empty of formal_set_arg                   (* emptiness *)
(* arith formula *)
type aform =
  | Af_equal of aexpr * aexpr
  | Af_noteq of aexpr * aexpr
  | Af_sup of aexpr * aexpr
  | Af_supeq of aexpr * aexpr
(* path expression *)
type pathstr =
  | Pe_epsilon                     (* empty string *)
  | Pe_seg of Offs.t list          (* star pattern access path *)
  | Pe_single of Offs.t list       (* single step access path *)
(* path formula *)
type apath = formal_ptr_arg * pathstr * formal_ptr_arg
(* pure formula *)
type pformatom =
  | Pf_alloc of int   (* size allocated bytes from root pointer *)
  | Pf_set of sform   (* set predicates *)
  | Pf_arith of aform (* arithmethic predicates *)
  | Pf_path of apath  (* access path predicates *)
type pform = pformatom list (* conjunction *)


(** Rules *)
(* Rule kind *)
type ir_kind =
  | Ik_unk                  (* unknown type (no hint available for this rule) *)
  | Ik_empz                 (* empty heap fragment, null ptr *)
  | Ik_range of int * int   (* non null ptr, non empty frag, range [n,m[ *)
(* Rule of an inductive definition *)
type irule =
    { (** Components of the rule *)
      ir_num:  int;           (* number of new SVs *)
      ir_nnum: IntSet.t;      (* number of new int SVs *)
      ir_snum: IntSet.t;      (* number of new SETVs *)
      ir_typ:  ntyp IntMap.t; (* types of the new variables *)
      ir_heap: hform;         (* heap part *)
      ir_pure: pform;         (* pure part *)
      ir_kind: ir_kind;       (* kind of the rule *)
      (** Elements derived by inductive definition analysis *)
      ir_uptr: IntSet.t;      (* unused ptr parameters *)
      ir_uint: IntSet.t;      (* unused int parameters *)
      ir_uset: IntSet.t;      (* unused set parameters *)
      ir_unone: bool;         (* true iff it uses no parameter at all *)
      ir_cons: aform option;  (* guard condition of this rule *) }


(** General inductive definition properties to be found by analysis *)
(* Whether parameters can be viewed as:
 *  - constant across all calls;
 *  - of additive kind (for integers and sets)
 *    (this kind is very useful on segments *)
type par_rec =
    { pr_const: bool (* constant over recursive calls *) ;
      pr_add:   bool (* additive over recursive calls *) }
type pars_rec =
    { (* whether a pointer field is constant or not *)
      pr_ptr_const:  bool IntMap.t ;
      pr_int:        par_rec IntMap.t ;
      (* set parameter field (const/head/add) *)
      pr_set:        Set_sig.set_par_type IntMap.t; }


(* The type of parameters of an inductive definition, that can be
 * used in the weakening of inductive edges *)
type set_op =
  | Uplus
  | Union
type wk_typ = [
  | `Eq                         (* a_l = a_r *)
  | `Non                        (* a_l has no relation with a_r *)
  | `Leq                        (* a_l \leq a_r *)
  | `Geq                        (* a_l \geq a_r *)
  (* a_l = a_r for inductive edge, for segments,
   * \alpha(a_l) *= \beta(a_l') and \alpha(a_r) *= \beta(a_r'),
   * a_l = a_l' + x and a_r = a_r' + x *)
  | `Add
  (* additive type for set parameters *)
  | `SAdd of set_op]
type ptr_wk_typ = [
  | `Eq
  | `Non]
type int_wk_typ = [
  | `Eq
  | `Non
  | `Leq
  | `Geq
  | `Add]
type set_wk_typ = [
  | `Eq
  | `Non
  | `SAdd of set_op]
type pars_wk_typ =
  { (* weaken type for pointer parameters *)
    ptr_typ:  ptr_wk_typ IntMap.t ;
    (* weaken type for integer parameters *)
    int_typ:  int_wk_typ IntMap.t ;
    (* weaken type for set parameters *)
    set_typ:  set_wk_typ IntMap.t; }


(** Inductive definitions *)
type ind =
    { (** Components of the definition *)
      i_name:    string;     (* name *)
      i_ppars:   int;        (* number of int parameters *)
      i_ipars:   int;        (* number of ptr parameters *)
      i_spars:   int;        (* number of set parameters *)
      i_rules:   irule list; (* rules *)
      i_srules:  irule list; (* subset of i_rules: only for segments *)

      (** Elements that should help the analysis (derived by ind. analysis) *)
      i_mt_rule: bool;       (* existence of a rule with null ptr, emp heap *)
      i_emp_ipar: int;       (* existence of rule with emp heap and int param *)
      i_reds0:   bool;       (* may a segment with root=0 be reduced to empty *)

      (* set of "directions" for induction, that is offset that can lead to
       * the next inductive call *)
      i_dirs:    Offs.OffSet.t;
      (* offset which may lead to same ind. def *)
      i_may_self_dirs: Offs.OffSet.t;
      i_pr_pars: IntSet.t;       (* set of parameters for prev fields *)
      i_fl_pars: int IntMap.t;   (* parameter => field storing it *)
      i_pr_offs: Offs.OffSet.t;  (* set of prev fields *)
      i_list:    (int * int) option; (* next off+size for list like defs *)

      (* constraints of inductive definition parameters, such as, i=0, i!=0,
       * this constraints could be used to perform reductions, like,
       *  i=0 ==> E = \emptyset *)
      i_rules_cons:  (aform * aform list * sform list) list;
      (* behavior of inductive definition parameters:
       *  - ptr parameters may be constant
       *  - int and set parameters may be constant or additive *)
      i_pkind:   pars_rec;
      (* behavior of inductive definition parameters:
       *  - a ptr parameter may reach another ptr parameter following
       * a path *)
      i_ppath: apath list ;
      (* weaken type of inductive definition parameters *)
      i_pars_wktyp:  pars_wk_typ;
      (* weaken type of parameters of inductive definition emp rule*)
      i_emp_pars_wktyp: pars_wk_typ;
    }


(** Parsing of inductive definitions *)
(* A line in a file may be either an inductive, a binding to a C type,
 * or some precedence information among inductive definitions *)
type p_iline =
  | Piind of ind                (* inductive definition *)
  | Pibind of string * string   (* definition associated to a type *)
  | Piprec of string list       (* precedence information *)
