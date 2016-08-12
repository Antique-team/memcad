(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: timer.mli
 **       Primitives for the extraction of timing information
 ** Xavier Rival, started 2012/08/11 *)

(* A timer is specified by the processor time when it was started *)
type timer

(** Operation on timers *)
val start: unit -> timer
val current_time: timer -> float

val cpu_timestamp: unit -> float

(** Time logging infrastructure *)
(* To monitor the total time spent in some functions
 *  nb: that includes time spent in sub-calls *)
(* Initialization *)
val init: unit -> unit
(* Printer: time spent in all functions *)
val print_timing_infos: unit -> unit

(** Logging module *)
module type TIMER_DEF =
  sig
    val name: string
  end
module Timer_Mod: functor (Mod : TIMER_DEF) ->
  sig
    val app1: string -> ('a -> 'b) -> 'a -> 'b
    val app2: string -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'c
    val app3: string -> ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
    val app4: string ->
      ('a -> 'b -> 'c -> 'd -> 'e) -> 'a -> 'b -> 'c -> 'd -> 'e
    val app5: string ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f) -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f
    val app6: string ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g) ->
        'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g
    val app7: string ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h) ->
        'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h
    val app8: string ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i) ->
        'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i
    val app9: string ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j) ->
      'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j
    val app10: string ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j -> 'k) ->
      'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j -> 'k
  end
