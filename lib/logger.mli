(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: logger.ml
 **       logging infrastructure
 ** Francois Berenger, 19/07/2016 *)

(** {2 Logger} *)

(** {4 Setup} *)

val set_output : out_channel -> unit
val set_prefix : string -> unit
val clear_prefix : unit -> unit

(** {4 Printf-like logging primitives} *)

module type S = sig

  val log: Log_level.t -> ('a, Buffer.t, unit, unit) format4 -> 'a

  (* All possible log statements, by decreasing order of importance.
   * At runtime, only statements of importance >= to a given level
   * will be shown for a given module. For example, when benchmarking the 
   * analyzer, only logs with level >= ERROR should be printed out
   * (for performance reasons). *)

  (* you want to force a message to be displayed (use sparingly) *)
  val force : ('a, Buffer.t, unit) format -> 'a
  (* an unrecoverable error was encountered; the analyzer will crash soon *)
  val fatal : ('a, Buffer.t, unit) format -> 'a
  (* an unrecoverable error was encountered and Failure is raised *)
  val fatal_exn : ('a, Buffer.t, unit, 'b) format4 -> 'a
  (* a todo was encountered *)
  val todo : ('a, Buffer.t, unit) format -> 'a
  (* a todo was encountered and Failure is raised *)
  val todo_exn : ('a, Buffer.t, unit, 'b) format4 -> 'a
  (* an error was encountered *)
  val error : ('a, Buffer.t, unit) format -> 'a
  (* a warning (something less severe than an error) was encountered *)
  val warn  : ('a, Buffer.t, unit) format -> 'a
  (* you want to give feedback to the user *)
  val info  : ('a, Buffer.t, unit) format -> 'a
  (* you want to give feedback to the programmer *)
  val debug : ('a, Buffer.t, unit) format -> 'a

end

include S

val color_on  : unit -> unit
val color_off : unit -> unit
val set_color_mapping : (Log_level.t -> Color.t) -> unit

(** {4 Functor interface (optional)} *)

module type SECTION = sig

  (** Signature for the functor parameters. *)

  val section: string
  (** Section name. *)

  val level: Log_level.t
  (** Initial log level. *)

end

module Make (Section: SECTION): S
(**
   This module aims to be used on the first line of each module:
   module Log = Log.Make(struct let section = "module-name" end)
*)
