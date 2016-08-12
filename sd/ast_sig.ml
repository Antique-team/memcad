(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: ast_sig.ml
 **       signatures of abstract syntax trees used in transfer functions
 ** Xavier Rival, 2011/05/27 *)
open Data_structures

(** Components of expressions *)
(* By convention, sizes are in bytes *)
type tisize = int (* integer size, could be 1, 2, 4, 8 *)
type tfsize = int (* floating point size, could be 4, 8 *)
type tsign =
  | Tsigned | Tunsigned
type typ =
  | Tunk (* No type information; used as a temporary/placeholder *)
  | Tint of tisize * tsign
  | Tfloat of tfsize
  | Tptr of typ option (* size is given by Settings.pointer_size *)
  | Tbool
  | Tstruct of typ_struct
  | Tunion of typ_union
  | Tarray of (typ * int)
  | Tchar
  | Tstring of int
  | Tnamed of string (* for named C type (no recursive data-type needed) *)
  | Tvoid
and typ_struct =
    { ts_align:  int;
      ts_size:   int;
      ts_fields: typ_sfield list }
and typ_sfield =
    { tsf_name:  string ; (* field name *)
      tsf_off:   int ;    (* numeric offset *)
      tsf_size:  int ;    (* size *)
      tsf_typ:   typ      (* type of field *) }
and typ_union =
    { tu_align:  int;
      tu_size:   int;
      tu_fields: typ_ufield list }
and typ_ufield =
    { tuf_name:  string ; (* field name *)
      tuf_size:  int ;    (* size *)
      tuf_typ:   typ      (* type of the field *) }
type const =
  | Cint of int
  | Cchar of char
  | Cint64 of int64
  | Cstring of string
type uni_op =
  (* Arithmetic *)
  | Uneg
  (* Logic *)
  | Unot
  (* bitwise logic *)
  | Ubnot
type bin_op =
  (* Arithmetic *)
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Bmod
  (* Comparison *)
  | Beq
  | Bgt
  | Bge
  | Bne
  (* Logic *)
  | Band
  | Bor
type field =
    { f_name:  string ;     (* field name *)
      f_off:   int option ; (* offset, if avail *) }
type var =
    { v_name: string ; (* name *)
      v_id:   int ;    (* unique id *)
      v_typ:  typ ;    (* type *) }


(** Expressions and lvalues *)
type 'a expr =
  | Erand (* expression evaluates to random value (for volatiles) *)
  | Ecst of const
  | Euni of uni_op * 'a texpr
  | Ebin of bin_op * 'a texpr * 'a texpr
  | Elval of 'a tlval
  | EAddrOf of 'a tlval
and 'a texpr = 'a expr * typ
and 'a lval =
  | Lvar of 'a
  | Lderef of 'a texpr
  | Lfield of 'a tlval * field
  | Lindex of 'a tlval * 'a texpr
and 'a tlval = 'a lval * typ


(** Set variables and properties *)
type setvar =
    { s_name: string;    (* name *)
      s_uid:  int;       (* unique ID *)
      s_root: bool       (* root or not *) }
type 'a setprop =
  | Sp_sub of setvar * setvar
  | Sp_mem of 'a  * setvar
  | Sp_emp of setvar
  | Sp_euplus of setvar * 'a * setvar

(** Condition trees, used for the evaluation of guards *)
type 'a condtree =
  | Ctrand (* random condition *)
  | Ctleaf of 'a texpr (* atomic expression *)
  | Ctland of 'a condtree * 'a condtree
  | Ctlor  of 'a condtree * 'a condtree


(** Sets and maps of variables *)
(* for program variables *)
module VarOrd =
  struct
    type t = var
    let compare (v0: var) (v1: var): int =
      let ci = v0.v_id - v1.v_id in
      if ci = 0 then
        begin
          assert (String.compare v0.v_name v1.v_name = 0);
          ci
        end
      else ci
    let t_2str (v: var) = v.v_name
  end
module VarSet = SetMake( VarOrd )
module VarMap = MapMake( VarOrd )
(* for set variables *)
module SvarOrd =
  struct
    type t = setvar
    let compare (v0: setvar) (v1: setvar): int =
      let ci = v0.s_uid - v1.s_uid in
      if ci = 0 then
        begin
          assert (String.compare v0.s_name v1.s_name = 0);
          assert (v0.s_root = v1.s_root);
          ci
        end
      else ci
    let t_2str (v: setvar) = v.s_name
  end
module SvarSet = SetMake( SvarOrd )
module SvarMap = MapMake( SvarOrd )
