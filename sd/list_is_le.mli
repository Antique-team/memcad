(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: list_is_le.mli
 **       Inclusion checking for the list domain
 ** Xavier Rival, 2014/03/07 *)
open Data_structures
open Set_sig
open List_sig
open Nd_sig

(** Full inclusion checking, used in the domain functor *)
val is_le:
    lmem                         (* left input *)
  -> (n_cons -> bool)            (* satisfiability, in the left argument *)
  -> (set_cons -> bool)          (* satisfiability, left arg, set constraints *)
  -> lmem                        (* right input *)
  -> Graph_sig.node_emb          (* injection from right SV into left SV *)
  -> Graph_sig.node_emb          (* injection from right SETV to left SETV *)
  -> List_sig.is_le_ym           (* left remainder, possibly right segment *)
            
(** Partial inclusion checking function, used for join *)
val is_le_weaken_check:
    lmem                         (* left input *)
  -> IntSet.t                    (* segment end(s), if any *)
  -> (n_cons -> bool)            (* satisfiability, in the left argument *)
  -> (set_cons -> bool)          (* satisfiability, left arg, set constraints *)
  -> lmem                        (* right input *)
  -> Graph_sig.node_emb          (* injection from right SV into left SV *)   
  -> Graph_sig.node_emb          (* injection from right SETV to left SETV *)
  -> List_sig.is_le_weaken_check

(** Partial inclusion checking function, used for join *)
val is_le_weaken_guess:
    stop: int Aa_sets.t option   (* optional stop nodes *)
  -> lmem                        (* left input *)
  -> IntSet.t                    (* segment end(s), if any *)
  -> (n_cons -> bool)            (* satisfiability, in the left argument *)
  -> (set_cons -> bool)          (* satisfiability, left arg, set constraints *)
  -> lmem                        (* right input *)
  -> Graph_sig.node_emb          (* injection from right SV into left SV *)   
  -> Graph_sig.node_emb          (* injection from right SETV to left SETV *)
  -> List_sig.is_le_weaken_guess
