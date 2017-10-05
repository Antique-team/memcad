(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: inst_utils.mli
 **       utilities for the instantiation of set parameters
 ** Xavier Rival, Huisong Li, 2015/04/05 *)
open Data_structures

open Ind_sig
open Inst_sig
open Set_sig
open Nd_sig
open Graph_sig

type setv_inst = Inst_sig.setv_inst

(** Set parameters instantiations *)
val setv_inst_empty: setv_inst
val setv_inst_2stri: string -> setv_inst -> string
val sv_inst_empty: sv_inst
val sv_inst_2stri: string -> sv_inst -> string
(* Add a new setv *)
val add_setv: int -> setv_inst -> setv_inst
(* Remove a previously added setv *)
val rem_setv: int -> setv_inst -> setv_inst

val setv_inst_free: int -> setv_inst -> bool
val setv_inst_bind: int -> set_expr -> setv_inst -> setv_inst
val setv_inst_nobind: int -> setv_inst -> setv_inst
val setv_inst_guess: int -> int -> setv_inst -> setv_inst
val setv_inst_over_bind: int -> set_expr -> setv_inst -> setv_inst
val setv_inst_make_guess: int -> set_expr -> setv_inst -> setv_inst

val setv_inst_complete: IntSet.t -> (set_cons -> bool)
  -> setv_inst -> setv_inst
val setv_inst_strengthen: setv_inst -> setv_inst  -> setv_inst



val fold_add: (int -> 'a -> 'a) -> setv_inst -> 'a -> 'a
val fold_rem: (int -> 'a -> 'a) -> setv_inst -> 'a -> 'a

(* graph_join: instantiate fresh set variables according to
 * guessed equal relationship *)
val instantiate_eq:
    setv_inst                   (* input instantiation *)
  -> int IntMap.t(* gussesed equal relation on out set parameters *)
    -> set_expr IntMap.t (* gussed weaken from out set parameters to *)
        (* input set expressions*)
      -> setv_inst

(* generate equality map from set parameters of output
 * summarized edge to set parameters of summarized edge
 * generated in inclusion checking *)
val gen_map: int list ->  int list -> int IntMap.t -> int IntMap.t

(* rename instantiation on set parameters from is_le into
 * set parameters of out put *)
val rename_is_le_inst:
    set_expr IntMap.t
  -> set_expr IntMap.t
    -> int IntMap.t -> set_expr IntMap.t

(* Generate equality from set parameters of output inductive edge to
 * set parameters of input inductive edge *)
val l_call_inst:
    ind_args (* set pars from the join input *)
  -> graph    (* join input graph *)
  -> ind_args (* set pars from the join output being constructed *)
  -> setv_inst (* set instantiation being constructed *)
  -> sv_inst (* sv instantiation being constructed *)
  ->  int_wk_typ IntMap.t (* weaken type *)
      -> graph * setv_inst * sv_inst * int list

(* Generate equality from set parameters of output segment edge to
 * set parameters of input segment edge *)
val l_seg_inst:
  seg_edge (* set pars from the join input *)
  -> graph (* join input graph *)
  -> seg_edge (* set pars from the join output being constructed *)
  -> setv_inst (* instantiation being constructed *)
  -> sv_inst (* sv instantiation being constructed *)
  -> int_wk_typ IntMap.t (* weaken type *)
  -> graph * setv_inst * sv_inst * int list * int list

(* Deal with instantaition from is_le_ind *)
val is_le_call_inst:
    ind_args (* set pars from the is_le output *)
  -> ind_args (* set pars from the join output being constructed *)
    -> setv_inst (* instantiation being constructed *)
      -> sv_inst  (* sv instantiation being constructed *)
        -> set_expr IntMap.t  (* instantiation from is_le *)
          -> sv_inst   (* sv instantiation from is_le *)
            -> IntSet.t (* new set variables generated from is_le *)
              -> set_cons list       (* non proved set constraints *)
                ->  int IntMap.t   (* sv mapping inferred by the inclusion *)
                  -> setv_inst * sv_inst * int list

(* Deal with instantaition from is_le_seg *)
val is_le_seg_inst:
    seg_edge (* set pars from the is_le output *)
  -> seg_edge (* set pars from the join output being constructed *)
    -> setv_inst (* instantiation being constructed *)
      -> sv_inst (* sv instantiation being constructed *)
        -> set_expr IntMap.t  (* instantiation from is_le *)
          -> sv_inst (* sv instantiation from is_le *)
            -> IntSet.t (* new set variables generated from is_le *)
              -> set_cons list (* non proved set constraints *)
                -> int IntMap.t  (* sv mapping inferred by the inclusion *)
                  -> setv_inst * sv_inst * int list * int list

(* Instantiation of symbolic variables according to equality constraints,
 * that is, when a fresh sv (instantiable sv) is constrainted to be equal
 * to a numerical expression with only non fresh sv, then, we instantiate
 * this fresh sv to the expression *)
val nd_instantiation_eq: n_cons list -> IntSet.t -> n_expr IntMap.t
  -> n_expr IntMap.t * n_cons list * n_cons list

(* Merging sv_inst in join and sv_inst return from is_le:
 * as is_le only returns instantiation on fresh sv, therefore,
 * this, merging will just join these two sv_inst *)
val sv_inst_merge: sv_inst -> sv_inst -> sv_inst


(* SV instantiation: first instantiate some fresh sv according to equality
 * constraints, and then, if a non-instantiated sv \alpha is constrainted
 * to be, l_e <= \alpha <= r_e, and l_e and r_e only contain already
 * instantiated sv, then, if we can prove that l_e <= r_e, we can
 * instantiate \alpha to be a value from l_e to r_e *)
val sv_instantiation: sv_inst -> (n_cons -> bool) -> sv_inst

(* Deal with some constraints left from sv_instantiation function:
 * as an example, for constraint \alpha <= \beta, where both \alpha and
 * \beta are fresh sv, and in sv_inst, we have e1 <= \alpha, \beta <= e2,
 * in this case, if we can prove that e1 <= e2, then, we can instantiate
 * \alpha be a value from e1 to \beta, and instantiate \beta be a value
 * from \alpha to e2 *)
val do_sv_inst_left_ctrs: sv_inst -> (n_cons -> bool) -> sv_inst

(* Instantiation according to the weakening type of integer parameters *)
val typed_sv_instantiation: sv_inst -> int_wk_typ IntMap.t
  -> (n_cons -> bool) -> sv_inst

(* Rename left constraints in sv_inst and prove them *)
val prove_sv_cons: sv_inst -> (n_cons -> bool) -> sv_inst
