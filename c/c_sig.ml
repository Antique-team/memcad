(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: c_sig.ml
 **       a micro C frontend
 ** Xavier Rival, 2011/07/09 *)
open Data_structures
open Flags
open Lib

(** A reduced C subset, without control flow inside expressions
 **   . function calls and procedure calls as statements
 **   . assignments as statements
 **   . no more non assignment, non function call expression statement *)

(** Improvements to consider:
 ** - localisation should be done with a notion of extent ?
 ** - simplify the language as much as possible (clean subset of C) *)

(** Localisation *)
(* Localisation information is just a line number now
 * (depending on context, first or last line of statement) *)
type c_loc = int

(** Types *)
type c_type =
  | Ctint
  | Ctchar
  | Ctvoid
  | Ctnamed of c_named
  | Ctstruct of c_aggregate_def
  | Ctunion  of c_aggregate_def
  | Ctptr of c_type option (* None when what is pointed to is unknown *)
  | Ctarray of c_type * int option (* None when the array size is unknown *)
  | Ctstring of int (* type of string constant, with its length *)
and c_aggregate_def =
  | Cad_def of c_aggregate (* Def. of an aggregate (with or without name) *)
  | Cad_named of string    (* Named aggregate without its definition *)
and c_aggregate =
    { cag_name:   string option;   (* name of the aggregate, if any *)
      cag_align:  int;
      cag_size:   int;
      cag_fields: c_agg_field list (* fields of the aggregate *) }
and c_agg_field = (* field aggregate (used for unions and structures) *)
    { caf_typ:  c_type;
      caf_off:  int;
      caf_size: int;
      caf_name: string }
and c_named =
    { cnt_name:         string (* name of the type *) ;
      mutable cnt_type: c_type (* type pointed *) }
(** Operators *)
type c_uniop =
  | Cuneg
  | Culnot
  | Cubnot (* bitwise not *)
type c_binop =
  | Cbeq
  | Cbne
  | Cbge | Cbgt | Cble | Cblt
  | Cbadd | Cbsub | Cbmul | Cbmod | Cbdiv
  | Cbland | Cblor (* logical operators *)
  | Cbband | Cbbor (* bitwise operators *)
  | Cbbslft | Cbbsrgh (* bitwise shift operators *)
(** Variables *)
type c_var =
    { cv_name:     string (* name *) ;
      cv_uid:      int    (* unique ID *) ;
      cv_type:     c_type (* type *) ;
      cv_volatile: bool   (* whether it is volatile *) }
(** Constants *)
type c_const =
  | Ccint of int
  | Ccchar of char
  | Ccstring of string
  | Ccnull       (* null pointer, for the sake of typing *)
(** Expressions *)
type c_exprk =
  | Ceconst of c_const
  | Celval of c_lval
  | Ceaddrof of c_lval
  | Ceuni of c_uniop * c_expr
  | Cebin of c_binop * c_expr * c_expr
and c_expr =
    { cek: c_exprk (* the actual expression *) ;
      cet: c_type  (* type *) }
and c_lvalk =
  | Clvar of c_var
  | Clfield of c_lval * string
  | Clindex of c_lval * c_expr
  | Clderef of c_expr
and c_lval =
    { clk: c_lvalk (* the actual l-value *) ;
      clt: c_type  (* type *) }
(** MemCAD commands (share with dom_sig stuff ?) *)
type c_memcad_iparam =
  | Cmp_const of int
  | Cmp_lval of c_lval
type c_memcad_setvar =
    { mc_setvar_name: string;     (* name *)
      mc_setvar_uid:  int;        (* unique ID *) }
type c_memcad_iparams =
    { mc_pptr:  c_memcad_iparam list ;
      mc_pint:  c_memcad_iparam list ;
      mc_pset:  c_memcad_setvar list } 
type c_memcad_setexpr =
  | Cmp_subset of c_memcad_setvar * c_memcad_setvar
  | Cmp_mem of c_lval * c_memcad_setvar
  | Cmp_empty of c_memcad_setvar
  | Cmp_euplus of c_memcad_setvar * c_lval * c_memcad_setvar 
type c_num_expr = c_binop * c_lval * c_memcad_iparam
type c_memcad_com =
  (** asserting/verifying inductives and associated assumptions *)
  (* assumption *)
  | Mc_add_inductive of c_lval * string option * c_memcad_iparams option
  | Mc_add_segment of c_lval * string * c_memcad_iparams option 
        * c_lval * string * c_memcad_iparams option
  | Mc_add_setexprs of c_memcad_setexpr list
  | Mc_decl_setvars of c_memcad_setvar list
  | Mc_assume of c_num_expr list
  (* a semantic equivalent to assert *)
  | Mc_check_setexprs of c_memcad_setexpr list
  | Mc_check_inductive of c_lval * string option * c_memcad_iparams option
  | Mc_check_segment of c_lval * string * c_memcad_iparams option 
        * c_lval * string * c_memcad_iparams option
  (* checks the current flow is (not) _|_ (non-_|_ not sound, for testing) *)
  | Mc_check_bottomness of bool
  (** manual management of unfolding *)
  (* provokes unfolding of an inductive *)
  | Mc_unfold of c_lval
  (* provokes backward unfolding of a segment towards some node *)
  | Mc_unfold_bseg of c_lval
  (** output the current abstract state *)
  (* to external file, in specific format *)
  | Mc_output_ext of output_format
  (* to standard output *)
  | Mc_output_stdout
  (** disjunctions management *)
  (* unrolling of a loop, over-riding the main parameter *)
  | Mc_unroll of int
  (* provokes merging of all disjuncts (if using the disjunctive domain) *)
  | Mc_merge
  (* (experimental) select disjuncts that might be easy to join *)
  | Mc_sel_merge of c_var list
  (** manual control of analysis operations *)
  (* forces a variable be considered live *)
  | Mc_force_live of c_var list
  (* kill current flow into _|_ (unsound, convenient to investigate) *)
  | Mc_kill_flow
  (* XR: where are the array properties passed through the AST ?
   * using global references would be a very dirty way to get
   * this to work *)
  (* check properties specific for array properties *)
  | Mc_array_check
  (* build a state satisfying the array properties *)
  | Mc_array_assume
  (** reduction *)
  (* provokes the re-localization of a node, after reduction *)
  | Mc_reduce_localize of c_lval
  (* eager reduction *)
  | Mc_reduce_eager
  (** unparsed *)
  (* status of the string while yet unparsed *)
  | Mc_comstring of string
(** Calls *)
type c_call =
    { cc_fun:  c_expr ;
      cc_args: c_expr list }
(** Statements *)
type c_statk =
  (* variables declaration *)
  | Csdecl of c_decl
  (* procedure calls and function calls *)
  | Cspcall of c_call (* procedure, does not have a return value *)
  | Csfcall of c_lval * c_call (* function, returns a value *)
  (* assignment statement *)
  | Csassign of c_lval * c_expr
  (* block *)
  | Csblock of c_block
  (* condition *)
  | Csif of c_expr * c_block * c_block
  (* while loop *)
  | Cswhile of c_expr * c_block * int option (* number of unrolls *)
  (* jump statements *)
  | Csreturn of c_expr option
  | Csbreak
  | Cscontinue
  (* parameterization of the analysis *)
  | Cs_memcad of c_memcad_com (* MemCAD command *)
  | Csassert of c_expr (* conventional C assert *)
  (* memory management *)
  | Csalloc of c_lval * c_expr (* allocation of a number of bytes *)
  | Csfree of c_lval
and c_stat =
    { csk: c_statk (* the actual statement *) ;
      csl: c_loc   (* localization information; line number for now *) }
and c_block = c_stat list
and c_decl = c_var
type c_fun =
    { cf_type: c_type ;
      cf_uid:  int ; (* notion of uid for functions *)
      cf_name: string ;
      cf_args: c_var list ;
      cf_body: c_block }
type c_prog =
    { cp_vars:  c_var StringMap.t ;
      cp_funs:  c_fun StringMap.t ;
      cp_types: c_type StringMap.t ;
      cp_aggs:  c_aggregate StringMap.t}

(** Helper types, for parsing only *)
type parsed_declaration =
  | Pcd_var of c_var * int
  | Pcd_type of string * c_type
type parsed_fun = c_type * string * c_var list * c_block
type parsed_init_declarator = string * c_var list option

(** Sets and maps of variables *)
module CVarOrd =
  struct
    type t = c_var
    let compare (v0: c_var) (v1: c_var): int =
      let ci = v0.cv_uid - v1.cv_uid in
      if ci = 0 then
        begin
          assert (String.compare v0.cv_name v1.cv_name = 0);
          ci
        end
      else ci
    let t_2str (v: c_var) = v.cv_name
  end
module CVarSet = SetMake( CVarOrd )
module CVarMap = MapMake( CVarOrd )

(** Access paths, used for the pre-analysis and the hints to the analyzer *)
type a_path =
    | Deref
    | Field of string 
type path = a_path list
      
module PathOrd =
  struct
    type t = path * c_lval
    let compare (p0: t) (p1: t): int =
      let compare_a p1 p2 =
        match p1, p2 with
        | Deref, Deref -> 0
        | Deref, Field _ -> -1
        | Field _, Deref -> 1
        | Field s1, Field s2 -> String.compare s1 s2 in
      let rec compare_list l1 l2 =
        match l1, l2 with
        | [], [] -> 0
        | [], _  -> -1
        | _ :: _, [] -> 1
        | x1 :: tl1, x2 :: tl2 ->
            let c = compare_a x1 x2 in
            if c = 0 then compare_list tl1 tl2 else c in 
      compare_list (fst p0) (fst p1)
    let t_2str (p: t) =
      let a_path_2str (p: a_path): string =
      match p with
        | Deref -> "Deref"
        | Field s -> s in
      match fst p with
      | [] -> ""
      | [ ele ] -> a_path_2str ele
      | hd :: tl ->
          List.fold_left
            (fun acc ele -> Printf.sprintf "%s:%s" acc (a_path_2str ele))
            (a_path_2str hd) tl
  end
module PathSet = SetMake( PathOrd )
