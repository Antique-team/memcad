(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: offs.mli
 **       selection of an offsets implementation
 ** Xavier Rival, 2012/04/23 *)
open Data_structures

(** Definition and functions over offsets *)
include Off_sig.OFF_SIG

(** Sets of offsets *)
module OffSet: (SET with type elt = t)
module OffMap: (MAP with type key = t)
