(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: svenv_sig.ml
 **       signatures of the symbolic variables environments
 ** Xavier Rival, 2014/01/12 *)
open Data_structures
open Sv_sig


(** Symbolic variables environment modifications *)

(* Abbrevs:
 *  - SV:  symbolic variable
 *  - SVE: symbolic variables environment
 *)

(* Principles:
 *  - structure svenv_mod:
 *    . stores local symbolic variables environment changes, before they get
 *      propagated to the domain above
 *    . is used to describe and propagate a list of changes to the SVE,
 *      either upwards or downards
 *  - synchronization functions need to be called to propagate these changes
 *  - sve_sync_bot_up: bottom-up synchronization:
 *    . empties the local list of changes
 *    . returns the list of changes that were only local, so that these can
 *      be taken into account higher in the abstract domain
 *    typically, a call to sve_sync_bot_up:
 *      1. will call the same synchro in the domains below;
 *      2. perform the local update
 *  - sve_sync_top_down: top-down synchronization:
 *    . takes a set of global modification to propagate localy
 *    . performs its action on a local abstraction level
 *  - sve_fix: internal synchronization:
 *    . performs the update inside a domain
 *)

(* The record below contains the following information:
 *  - removal / addition of variables: simply propagate globall;
 *  - locally modified variables: means that the concrete value this
 *    symbolic variable corresponds to may have changed, thus all
 *    constraints involving them should be dropped *)
type svenv_mod =
    { svm_add: (int,ntyp) PMap.t; (* locally added; to propagate globally *)
      svm_rem: int PSet.t;      (* locally removed; to propagate globally *)
      svm_mod: int PSet.t;     (* locally modified; to invalidate globally *) }

(* Qualification of the modification to the environment:
 *  - internal modification come from underlying domain and are added
 *    to the envmod structure (i.e., to be propagated to the rest of
 *    the domain)
 *  - external modifications come from the rest of the domain, and do
 *    not need to be repropagated *)
type svenv_mod_kind =
  | Mk_int
  | Mk_ext

(* To finish: complete refactoring of the gestion of environments
 *  - add invariants into sanity check functions, and fix any issue
 *  - distinguish external and internal addition of nodes, with svenv_mod_kind
 *    (it might not be needed)
 *
 * Modules that still need be thoroughly checked:
 *  - dom_mem_low_flat
 *  - dom_val_subm
 *    => this one may add symbolic variables as part of a numeric
 *       abstraction
 *)
