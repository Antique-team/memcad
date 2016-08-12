(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: inst_sig.ml
 **       data-type for the instantiation of set parameters
 ** Xavier Rival, Huisong Li, 2015/04/05 *)
open Data_structures

open Set_sig

(** Set parameters instantiation (after join) *)
(* Synthesized setvs need to be resolved to something of the original graphs;
 *  - setvi_eqs:   exact resolution using an equality
 *  - setvi_guess: no exact resolution, we just know some members of the set
 *                 and will try to look among the roots if one satisfies this
 *                 (this is a bit arbitrary and could be improved)
 *  - setvi_none:  no constraint, and can be considered a free variable
 *                 so it could be instantiated to anything *)
type setv_inst =
    { (* Management of setvs to be instantiated *)
      setvi_add:   IntSet.t;
      setvi_rem:   IntSet.t;
      (* Definition of setvs to be instantiated *)
      setvi_eqs:   set_expr IntMap.t; (* new setv => renamed expr *)
      setvi_guess: int IntMap.t;      (* new setv => guessed element *)
      setvi_none:  IntSet.t;          (* new setv => could be anything *)
      (* Other definitions *)
      setvi_props: set_cons list;     (* def. constraints that can be assumed *)
      (* Validation of the instantiation *)
      setvi_prove: set_cons list;     (* constraints to prove *) }
