(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: offs.ml
 **       selection of an offsets implementation
 ** Xavier Rival, 2012/04/23 *)
open Data_structures

(** Definition and functions over offsets *)
module Off = Off_linexpr.Off_Linexpr
include Off

(** Sets of offsets *)
module OffSet = SetMake( Off )
module OffMap = MapMake( Off )
