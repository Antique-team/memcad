(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: batch.ml
 **       entry point of the automatic regression tester
 ** Xavier Rival, 2011/09/29 *)
open Config_sig
open Data_structures
open Flags
open Lib
open Rt_sig


module Log =
  Logger.Make(struct let section = "batch___" and level = Log_level.DEBUG end)


(** Flags *)
(* over-riding analysis fields *)
let flag_silent:        bool option ref = ref None
let flag_very_silent:   bool option ref = ref None
(* de-activating timing (for easier text log comparisons) *)
let no_timing: bool ref = ref false
(* dump log file to stdout in addition to the test's log file *)
let stdout_dump: bool ref = ref false

(** Parsing *)
let config_parser =
  Lib.read_from_file "c" Config_parser.file Config_lexer.token

(** Auxilliary functions *)
let default_test =
  { (** Options to be passed to analysis *)
    sp_src_file   = "";
    sp_header     = "memcad.h";
    sp_idirs      = "";
    sp_old_parser = false;
    sp_malloc_non0 = false;
    sp_ind_file   = "";
    sp_auto_ind   = false;
    sp_no_prev_fields = false;
    sp_main_fun   = !mainfun;
    sp_rec_calls  = false;
    sp_silent     = false;
    sp_very_silent= false;
    sp_verbose    = !test_verbose;
    sp_pp_add     = [];
    sp_pp_rem     = [];
    sp_dump_ops   = !flag_dump_ops;
    sp_timing     = [];
    (** Abstract domain: symbolic variables constraints *)
    sp_numdom     = !nd_selector;
    sp_submem     = !enable_submem;
    sp_subis      = StringSet.empty;
    sp_dynenv     = true;
    sp_red_mode   = !reduction_mode_selector;
    sp_setdom     = !sd_selector;
    sp_array      = !enable_array_domain;
    sp_eq_pack    = !enable_eq_pack;
    (** Abstract domain and inductive definitions *)
    sp_indpars    = !flag_indpars_analysis;
    sp_domstruct  = !shapedom_struct;
    (** Iteration strategy, widening *)
    sp_disj       = !disj_selector;
    sp_thrwide    = true;
    sp_thrs       = IntSet.empty;
    sp_unary_abs  = !do_unary_abstraction;
    sp_unrolls      = 0;
    sp_type_unfolds = 1;
    sp_dirweak    = !dweak_iters;
    sp_join_iters = !join_iters;
    sp_fast_iir   = true;
    sp_part_lfps  = !part_through_lfps;
    sp_sel_widen  = !sel_widen;
    sp_basic_widen = !old_widen;
    (** Regression testing elements *)
    sp_excluded   = false;
    sp_category   = [ ];
    sp_issue      = "";
    sp_assert_tot = 0;
    sp_assert_ok  = 0;
    sp_time_out   = 5 }

(** Revision letters conversion to/from integers *)
let rev_to_int: char option -> int = function
  | None -> -1
  | Some c -> int_of_char c - int_of_char 'a'
let rev_from_int (i: int): char option =
  if i < 0 then None
  else if i < 26 then Some (char_of_int (int_of_char 'a' + i))
  else Log.fatal_exn "invalid revision number"
let rev_2str: char option -> string = function
  | None -> ""
  | Some c -> Printf.sprintf "%c" c

(** Traduction of a parsed config file *)
let translate_tests (pconf: pconfig_file): tests =
  let extract_list (ctx: string): string list -> string = function
    | [ ] -> Log.fatal_exn "error %s: [ ]" ctx
    | [ s ] -> s
    | s :: _ -> Log.fatal_exn "error %s: %s..." ctx s in
  let aux_yesno (l: string list): bool =
    match extract_list "yes-no" l with
    | "yes" -> true
    | "no"  -> false
    | s     -> Log.fatal_exn "unbound yes-no: %s" s in
  let aux_onoff (l: string list): bool =
    match extract_list "on-off" l with
    | "on"  -> true
    | "off" -> false
    | s     -> Log.fatal_exn "unbound on-off: %s" s in
  let aux_numdom (l: string list): num_dom =
    match extract_list "domain" l with
    | "box" -> ND_box
    | "oct" -> ND_oct
    | "pol" -> ND_pol
    | s     -> Log.fatal_exn "unbound num domain %s" s in
  let aux_setdom (l: string list): set_dom =
    match extract_list "domain" l with
    | "none" -> SD_none
    | "on"
    | "lin"  -> SD_lin
    | "quicr"-> SD_quicr
    | "setr_lin" | "SETr_lin" -> SD_setr "lin"
    | "setr_bdd" | "SETr_bdd" -> SD_setr "bdd"
    | s     -> Log.fatal_exn "unbound set domain (%s)" s in
  let aux_redmod (l: string list): reduction_mode =
    match extract_list "redmod" l with
    | "manual"             -> Rm_manual
    | "disabled"           -> Rm_disabled
    | "minimal"            -> Rm_minimal
    | "on_read"            -> Rm_on_read
    | "on_read_and_unfold" -> Rm_on_read_and_unfold
    | "maximal"            -> Rm_maximal
    | s -> Log.fatal_exn "undefined reduction mod: %s" s in
  let aux_subind (l: string list): StringSet.t =
    StringSet.singleton (extract_list "subind" l) in
  let aux_category: string -> test_category = function
    | "valid"
    | "validated" -> TC_valid
    | "wait"      -> TC_wait
    | "exp"       -> TC_exp
    | s           -> TC_other s in
  let aux_categories: string list -> test_category list =
    List.map aux_category in
  let aux_field (t: test_spec) (f: field): test_spec =
    match f.fname, f.fval with
    | "array", F_strings s       -> { t with sp_array = aux_onoff s }
    | "eq_pack", F_strings s     -> { t with sp_eq_pack = aux_onoff s }
    | "auto_ind", F_strings s    -> { t with sp_auto_ind = aux_onoff s }
    | "no_prev_fields", F_strings s-> { t with sp_no_prev_fields = aux_onoff s }
    | "asserts_proved", F_int n  -> { t with sp_assert_ok = n }
    | "asserts_total", F_int n   -> { t with sp_assert_tot = n }
    | "category", F_strings s    -> { t with sp_category = aux_categories s }
    | "excluded", F_strings s    -> { t with sp_excluded = aux_yesno s }
    | "dirweak", F_int n         -> { t with sp_dirweak = n }
    | "disj", F_strings s        -> { t with sp_disj = aux_onoff s }
    | "domain", F_strings s      -> { t with sp_numdom = aux_numdom s }
    | "domstruct", F_qstring s   -> { t with sp_domstruct = s }
    | "dump_ops", F_strings s    -> { t with sp_dump_ops = aux_onoff s }
    | "dynenv", F_strings s      -> { t with sp_dynenv = aux_onoff s }
    | "set_on", F_qstring s      -> { t with sp_pp_add = s :: t.sp_pp_add }
    | "set_off", F_qstring s     -> { t with sp_pp_rem = s :: t.sp_pp_rem }
    | "fast_iir", F_strings s    -> { t with sp_fast_iir = aux_onoff s }
    | "file", F_qstring s        -> { t with sp_src_file = s }
    | "header", F_qstring s      -> { t with sp_header = s }
    | "idirs", F_qstring s       -> { t with sp_idirs = s }
    | "indfile", F_qstring s     -> { t with sp_ind_file = s }
    | "indpars", F_strings s     -> { t with sp_indpars = aux_onoff s }
    | "issue", F_qstring s       -> { t with sp_issue = s }
    | "join_iters", F_int n      -> { t with sp_join_iters = n }
    | "main_fun", F_qstring s    -> { t with sp_main_fun = s }
    | "malloc_non0", F_strings s -> { t with sp_malloc_non0 = aux_onoff s }
    | "old_parser", F_strings s  -> { t with sp_old_parser = aux_onoff s }
    | "basic_widen", F_strings s -> { t with sp_basic_widen = aux_onoff s }
    | "part_lfps", F_strings s   -> { t with sp_part_lfps = aux_onoff s }
    | "rec_calls", F_strings s   -> { t with sp_rec_calls = aux_onoff s }
    | "sel_widen", F_strings s   -> { t with sp_sel_widen = aux_onoff s }
    | "setdom", F_strings s      -> { t with sp_setdom = aux_setdom s }
    | "silent", F_strings s      -> { t with sp_silent = aux_onoff s }
    | "submem", F_strings s      -> { t with sp_submem = aux_onoff s }
    | "submem_ind", F_strings s  -> { t with sp_subis = aux_subind s }
    | "thr_widen", F_strings s   -> { t with sp_thrwide = aux_onoff s }
    | "thr_w_add", F_int n       -> { t with sp_thrs = IntSet.add n t.sp_thrs }
    | "timeout", F_int n         -> { t with sp_time_out = n }
    | "timing", F_qstring s      -> { t with sp_timing = s :: t.sp_timing }
    | "unary_abs", F_strings s   -> { t with sp_unary_abs = aux_onoff s }
    | "unrolls", F_int n         -> { t with sp_unrolls = n }
    | "type_unfolds", F_int n    -> { t with sp_type_unfolds = n }
    | "very_silent", F_strings s -> { t with sp_very_silent = aux_onoff s }
    | "red_mode", F_strings s    -> { t with sp_red_mode = aux_redmod s }
    | _ -> Log.fatal_exn "unsupported_field: %s" f.fname in
  let aux_fields: test_spec -> fields -> test_spec =
    List.fold_left aux_field in
  let rec aux (acc: test_spec RevMap.t) (t: entry list): test_spec RevMap.t =
    let rem, acc =
      List.fold_left
        (fun (accrem, accm) (ent: entry) ->
          try
            let prev_test =
              match ent.ent_extend with
              | None -> default_test
              | Some basis -> RevMap.find basis accm in
            let trans = aux_fields prev_test ent.ent_fields in
            accrem, RevMap.add ent.ent_code trans accm
          with Not_found -> ent :: accrem, accm
        ) ([ ], acc) t in
    let lrem = List.length rem in
    if lrem = 0 then acc
    else
      if List.length t = lrem then
        begin
          List.iter
            (fun e ->
              Log.info "unresolved: (%d,...)" (fst e.ent_code)
            ) t;
          Log.fatal_exn "cycle in the definition of entries"
        end
      else aux acc rem in
  let acc = aux RevMap.empty pconf in
  RevMap.fold
    (fun ec ent acc ->
      if String.length ent.sp_src_file = 0 then RevMap.remove ec acc
      else acc
    ) acc acc

let spec_to_options (t: test_spec): string list =
  let lopts = ref [ "-pipe" ] in
  (* input file *)
  if String.length t.sp_src_file != 0 then
    lopts := t.sp_src_file :: !lopts;
  (* header file *)
  if t.sp_header <> "" then
    lopts := "-header" :: t.sp_header :: !lopts;
  (* include dirs *)
  if t.sp_idirs <> "" then
    lopts := "-idirs" :: t.sp_idirs :: !lopts;
  if t.sp_old_parser <> !use_old_parser then
    if t.sp_old_parser then
      lopts := "-old-parser" :: !lopts
    else lopts := "-clang-parser" :: !lopts;
  (* inductive definitions *)
  if t.sp_ind_file <> "" then
    lopts := "-a" :: "-use-ind" :: t.sp_ind_file :: !lopts
  else if t.sp_auto_ind then
    lopts := "-a" :: "-auto-ind" :: !lopts
  else
    lopts := "-a" :: !lopts;
  if t.sp_no_prev_fields then
    lopts := "-no-prev-fields" :: !lopts;
  (* main function *)
  if String.compare t.sp_main_fun !mainfun != 0 then
    lopts := "-main" :: t.sp_main_fun :: !lopts;
  (* handling of recursive calls *)
  if t.sp_rec_calls != !rec_calls then
    lopts := "-rec-calls" :: !lopts;
  (* malloc semantics restriction *)
  if t.sp_malloc_non0 then
    lopts := "-malloc-non0" :: !lopts;
  (* inductive definitions analysis *)
  if t.sp_indpars != !flag_indpars_analysis then
    lopts := "-ind-analysis" :: !lopts;
  (* whether to dump domain individual operations (e.g., set domain) *)
  if t.sp_dump_ops != !flag_dump_ops then
    lopts := if t.sp_dump_ops then "-dump-ops" :: !lopts else !lopts;
  (* timing modules *)
  List.iter (fun s -> lopts := "-timing" :: s :: !lopts) t.sp_timing;
  (* shape domain *)
  if String.compare t.sp_domstruct !shapedom_struct != 0 then
    lopts := "-shape-dom" :: ("\""^t.sp_domstruct^"\"") :: !lopts;
  (* numerical domain *)
  if t.sp_numdom != !nd_selector then
    lopts := (Printf.sprintf "-nd-%s" (num_dom_2str t.sp_numdom)) :: !lopts;
  (* sub-memory abstraction *)
  if t.sp_submem != !enable_submem then
    lopts := if t.sp_submem then "-add-submem" :: !lopts else !lopts;
  (* sub-memory indutive definitions *)
  if t.sp_subis != StringSet.empty then
    lopts :=
      StringSet.fold (fun s a -> "-submem-ind" :: s :: a) t.sp_subis !lopts;
  (* dynamic environment *)
  if t.sp_dynenv != !enable_dynenv then
    begin
      let o = if t.sp_dynenv then "-dynenv-yes" else "-dynenv-no" in
      lopts := o :: !lopts
    end;
  (* Array domain *)
  if t.sp_array != !enable_array_domain then
    lopts :=
      (if t.sp_array then "-array-on" else "-array-off") :: !lopts;
  (* Equation pack *)
  if t.sp_eq_pack != !enable_eq_pack then
    lopts :=
      (if t.sp_array then "-eq-pack-on" else "-eq-pack-off") :: !lopts;
  (* disjunctions *)
  if t.sp_disj != !disj_selector then
    lopts := (if t.sp_disj then "-disj-on" else "-disj-off") :: !lopts;
  (* set domain *)
  if t.sp_setdom != !sd_selector then
    begin
      lopts :=
        match t.sp_setdom with
        | SD_none   -> "-setd-off" :: !lopts
        | SD_lin    -> "-setd-lin" :: !lopts
        | SD_quicr  -> "-setd-quicr" :: !lopts
        | SD_setr n -> (Printf.sprintf "-setd-r-%s" n) :: !lopts
    end;
  (* threshold widening activation *)
  if t.sp_thrwide != !widen_do_thr then
    lopts := (if t.sp_thrwide then "-w-thr" else "-w-no-thr") :: !lopts;
  (* threshold widening addition *)
  IntSet.iter
    (fun i ->
      lopts := "-w-add-thr" :: (string_of_int i) :: !lopts;
    ) t.sp_thrs;
  (* unary abstraction *)
  if t.sp_unary_abs != !do_unary_abstraction then
    lopts := (if t.sp_unary_abs then "-unary-abs" else "-no-unary-abs")
      :: !lopts;
  (* unrolls *)
  if t.sp_unrolls != !unrolls then
    lopts := "-unrolls" :: string_of_int t.sp_unrolls :: !lopts;
  (* type unfolding *)
  if t.sp_type_unfolds != !type_unfolds then
    lopts := "-type-unfolds" :: string_of_int t.sp_type_unfolds :: !lopts;
  (* directed weakening *)
  if t.sp_dirweak != !dweak_iters then
    lopts := "-dw-iters" :: string_of_int t.sp_dirweak :: !lopts;
  (* join iters *)
  if t.sp_join_iters != !join_iters then
    lopts := "-j-iters" :: string_of_int t.sp_join_iters :: !lopts;
  (* partitioning through loops *)
  if t.sp_part_lfps != !part_through_lfps then
    lopts :=
      (if t.sp_part_lfps then "-part-lfps" else "-no-part-lfps") :: !lopts;
  (* sel widen through loops *)
  if t.sp_sel_widen != !sel_widen then
    lopts :=
      (if t.sp_sel_widen then "-sel-widen" else "-no-sel-widen") :: !lopts;
  (* old widen function*)
  if t.sp_basic_widen != !old_widen then
    lopts :=
      (if t.sp_basic_widen then "-basic-widen" else "-no-old-widen") :: !lopts;
  (* fast ind-ind rule *)
  if t.sp_fast_iir != !do_quick_ind_ind_mt then
    lopts :=
      (if t.sp_fast_iir then Log.fatal_exn "fast-iir setting"
       else "-no-fast-iir")
        :: !lopts;
  (* reduction mode *)
  if t.sp_red_mode != !reduction_mode_selector then
    lopts :=
      (Printf.sprintf "-red-%s" (red_mode_2str t.sp_red_mode)) :: !lopts;
  (* silent mode (batch flag overrides rt.txt) *)
  let b =
    match !flag_silent with
    | None -> t.sp_silent
    | Some b -> b in
  if b then lopts := "-silent" :: !lopts;
  (* very silent mode (batch flag overrides rt.txt) *)
  let b =
    match !flag_very_silent with
    | None -> t.sp_very_silent
    | Some b -> b in
  if b then lopts := "-very-silent" :: !lopts;
  (* pretty-printing *)
  List.iter (fun s -> lopts := "-set-on" :: s :: !lopts) t.sp_pp_add;
  List.iter (fun s -> lopts := "-set-off" :: s :: !lopts) t.sp_pp_rem;
  (* result *)
  !lopts

let magenta_color = Color.(to_string Bold ^ to_string Magenta)
let reset_color = Color.(to_string Reset)

(** Management and pretty-printing of the results *)
let pp_results
    (stress_test: int)          (* repeat number *)
    (validated: bool option)    (* whether it is about validated tests *)
    (tot_duration: float)       (* duration of tests *)
    (tests: test_spec RevMap.t) (* specs *)
    (m: test_result RevMap.t)   (* results *): unit =
  let cnt_to = ref 0
  and cnt_ko = ref 0
  and cnt_ok = ref 0 in
  let sep = String.make 80 '=' in
  begin
    match validated with
    | None -> Log.info "\n\n%s\nSpecific tests:\n" sep
    | Some v ->
        Log.info "\n\n%s\n%s:\n" sep
          (if v then "Already validated tests" else "Experimental tests")
  end;
  RevMap.iter
    (fun (i,c) (tr: test_result) ->
      let ts = RevMap.find (i,c) tests in
      let r, msg =
        match tr with
        | Tr_timeout -> cnt_to, "timeout"
        | Tr_fail    -> cnt_ko, "failed"
        | Tr_ok s    ->
            let msg =
              Printf.sprintf "passed (%d ok) %s %.3fs" s.ts_assert_ok
                (Lib.mk_space (5 - Lib.posint_len s.ts_assert_ok)) s.ts_time in
            cnt_ok, msg in
      incr r;
      let ii = RevOrd.t_2str (i,c) in
      let spc0 = String.make (7 - String.length ii) ' ' in
      let spc1 = String.make (30 - String.length msg) ' ' in
      let s_issue =
        let li = String.length ts.sp_issue in
        if li > 0 then
          Printf.sprintf "%s%s"
            (String.make (24 - String.length ts.sp_src_file) ' ')
            (String.sub ts.sp_issue 0 (min li 25))
        else "" in
      Log.info "%s:%s  %s%s%s%s" ii spc0 msg spc1 ts.sp_src_file s_issue
    ) m;
  Log.info "\n\n\n%s" sep;
  let timeout_str =
    let count = string_of_int !cnt_to in
    if !cnt_to <> 0 then magenta_color ^ count ^ reset_color
    else count in
  let failed_str =
    let count = string_of_int !cnt_ko in
    if !cnt_ko <> 0 then magenta_color ^ count ^ reset_color
    else count in
  Log.info "Passed:  %d" !cnt_ok;
  (if !cnt_to <> 0 then Log.error else Log.info) "Timeout: %s" timeout_str;
  (if !cnt_ko <> 0 then Log.error else Log.info) "Failed:  %s" failed_str;
  Log.info "Time:    %.3f sec" (tot_duration /. float_of_int stress_test);
  if validated = Some true && (!cnt_to != 0 || !cnt_ko != 0) then
    Log.error "REGRESSION: Some validated tests failed"

(** Management of the pipes *)
let close_pipe ( ): unit =
  Unix.unlink pipe_name
let open_pipe ( ): unit =
  try
    Unix.mkfifo pipe_name 0o600;
  with
  | Unix.Unix_error (Unix.EEXIST, _, _) ->
      begin
        try (* the pipe already exists; remove it and retry *)
          close_pipe ( );
          Unix.mkfifo pipe_name 0o600
        with
        | exc ->
            Log.info "Pipe opening failed: %s" (Printexc.to_string exc)
      end
  | exc ->
      Log.info "Pipe opening failed: %s" (Printexc.to_string exc)

(* some preprocessing needed in order to run one test *)
let prepare_test
    (stress_test: int) (* repeat number *)
    (rev: char option) (* test revision *)
    (t: test_spec)     (* test spec *)
    : (int -> int) * string array * string =
  let div_stress_test =
    if stress_test = 1 then fun n -> n
    else
      fun n ->
        if n mod stress_test = 0 then n / stress_test
        else Log.fatal_exn "division by repeat num" in
  (* Computing command line options for the analyzer *)
  let lopts =
    let l = spec_to_options t in
    let l = if !no_timing then "-no-timing" :: l else l in
    let l =
      if stress_test = 1 then l
      else "-stress-test" :: string_of_int stress_test :: l in
    "analyze" :: l in
  let aopts = Array.of_list lopts in
  let out_filename =
    let str = (Filename.chop_extension t.sp_src_file) in
    match rev with
    | None -> str^".log"
    | Some r -> Printf.sprintf "%s-%c.log" str r in
  (div_stress_test, aopts, out_filename)

let run_test
    (analyzer: string)                (* analyzer program *)
    (stress_test: int)                (* repeat number *)
    ((ntest, rev): int * char option) (* test number and revision *)
    (t: test_spec)                    (* test spec *)
    : float * test_result =
  Log.info "RT: Forking, task [%s]" (RevOrd.t_2str (ntest,rev));
  let div_stress_test, aopts, out_filename = prepare_test stress_test rev t in
  let out_file =
    if flag_debug_open_file then
      Log.force "About to open: %s" out_filename;
    Unix.openfile out_filename
      [ Unix.O_WRONLY ; Unix.O_CREAT ; Unix.O_TRUNC ] 0o600 in
  Log.info "Command line:";
  (* allow users to copy-paste the command and run it directly *)
  let command = String.concat " " (Array.to_list aopts) in
  Log.info "./%s" command;
  flush stdout;
  let t0 = Timer.cpu_timestamp () in
  let child =
    Unix.create_process analyzer aopts
      (Unix.descr_of_in_channel stdin) out_file out_file in
  (* wait for some time, try to read the results, kills child if *)
  (* still alive *)
  let alarm_handle (i: int): unit =
    assert (i = Sys.sigalrm);
    Log.info "RT: time elapsed, killing child!";
    try
      Unix.kill child Sys.sigkill
    with Unix.Unix_error (err, s0, s1) ->
      Log.info "unix Log.fatal_exn %s (%s,%s)" (Unix.error_message err) s0 s1;
      Log.fatal_exn "regression tester failed to time-out a child" in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle alarm_handle) ;
  let _ = Unix.alarm (stress_test * t.sp_time_out) in
  let duration, result =
    try
      let pid, status = Unix.waitpid [ ] child in
      let t1 = Timer.cpu_timestamp () in
      let duration = t1 -. t0 in
      assert (pid = child);
      let passed =
        match status with
        | Unix.WEXITED i ->
            begin
              if i = 0 then
                Log.info "Status exit: %d" i
              else
                Log.error "%sStatus exit: %d%s" magenta_color i reset_color
            end;
            i = 0
        | Unix.WSIGNALED i ->
            Log.error "%sStatus signal: %d%s" magenta_color i reset_color;
            false
        | Unix.WSTOPPED i  ->
            Log.error "%sStatus stopped: %d%s" magenta_color i reset_color;
            false in
      Log.info "RT: child terminated its task (%.3f)" duration;
      let res =
        if passed then
          begin
            (* read information sent by the child on the channel *)
            if flag_debug_open_file then
              Log.force "About to open: %s" pipe_name;
            let file = Unix.openfile pipe_name [ Unix.O_RDONLY ] 0o600 in
            let chan = Unix.in_channel_of_descr file in
            let s0 = input_line chan in
            let s1 = input_line chan in
            let i0 = int_of_string s0 in
            let i1 = int_of_string s1 in
            Log.info "Read: %d %d" i0 i1;
            Unix.close file;
            Unix.unlink pipe_name;
            let i0 = div_stress_test i0 in
            let i1 = div_stress_test i1 in
            if i0 + i1 = t.sp_assert_tot && i0 = t.sp_assert_ok then
              Tr_ok { ts_assert_ok = i0;
                      ts_assert_ko = i1;
                      ts_time      = duration /. float_of_int stress_test }
            else Tr_fail
          end
        else Tr_fail in
      duration, res
    with
    | Unix.Unix_error (Unix.EINTR, _, _) ->
        (* waitpid interrupted as the child was killed, due to a timeout *)
        Log.error "%schild was terminated%s" magenta_color reset_color;
        (* return the time-out information *)
        0., Tr_timeout in
  Unix.close out_file;
  if !stdout_dump then
    ignore(Unix.system ("cat " ^ out_filename));
  (duration, result)

(* to create a valid command line from an array of options *)
let unwind_options opts =
  let protect_string s =
    let n = String.length s in
    assert(n > 0);
    if s.[0] = '\"' && s.[n - 1] = '\"' then
      "'" ^ s ^ "'"
    else s in
  List.fold_left
    (fun acc opt -> acc ^ " " ^ (protect_string opt))
    "" (Array.to_list opts)

(** Main function *)
let batch () =
  Logger_glob.set_log_level "batch" Log_level.INFO; (* FBR: test on the fly log level change *)
  (* Setting which experiments to run *)
  let flag_pure_regtest: bool ref = ref false in
  let flag_pure_expe:    bool ref = ref false in
  let flag_all_test:     bool ref = ref false in
  (* name of the analyzer binary *)
  let analyzer: string ref = ref "./analyze" in
  (* name of the file describing all tests to perform *)
  let filename: string ref = ref "rt.txt" in
  (* unique test to run (if none, will run all tests) *)
  let test_ids: (int * char option) list ref = ref [ ] in
  (* category of tests to run *)
  let category: string ref = ref "" in
  (* number of repeats for stress-test *)
  let stress_test: int ref = ref 1 in
  (* sequential or parallel run of tests *)
  let ncores = ref 1 in (* sequential by default *)
  (* setting option fields *)
  let optset (r: bool option ref) (b: bool) =
    Arg.Unit (fun () -> r := Some b) in
  Arg.parse
    [ "-in-file", Arg.Set_string filename, "FILE use tests from FILE";
      ("-analyzer", Arg.Set_string analyzer,
       "FILE path to the analyzer executable");
      "-no-silent", optset flag_silent false, "disable silent mode";
      "-silent",    optset flag_silent true,  "enable silent mode";
      "-no-timing", Arg.Set no_timing, "disable timing info display";
      "-no-very-silent", optset flag_very_silent false, "very silent checking";
      "-very-silent", optset flag_very_silent true, "very silent checking";
      "-all-test", Arg.Set flag_all_test, "run all tests";
      "-pure-regtest", Arg.Set flag_pure_regtest, "only run validated tests";
      "-pure-expe", Arg.Set flag_pure_expe, "only run experimental tests";
      ("-pure-cat", Arg.Set_string category,
       "CAT only run tests in category CAT");
      "-stdout", Arg.Set stdout_dump, "cat logfile to stdout too";
      ("-stress-test", Arg.Set_int stress_test,
       "N repeat each test N times");
      ("-ncores", Arg.Set_int ncores,
       "N run tests in parallel on N cores max") ]
    (fun s ->
      try test_ids :=
        let ic =
          let n = String.length s in assert (0 < n);
          let last = String.get s (n-1) in
          let ilast = int_of_char last in
          if int_of_char '0' <= ilast && ilast <= int_of_char '9' then
            (* this is just a number *)
            int_of_string s, None
          else
            (* this is a number + a revision index *)
            int_of_string (String.sub s 0 (n-1)), Some last in
        ic :: !test_ids
      with _ ->
        Log.info "failed to read int argument";
        exit 1
    ) "Batch regression testing" ;
  assert (!ncores > 0);
  if !flag_all_test then
    begin
      flag_pure_regtest := true;
      flag_pure_expe    := true;
    end;
  let pp_results = pp_results !stress_test in
  (* parsing and translation *)
  let p_config = config_parser !filename in
  let tests =
    let tt = translate_tests p_config in
    match !test_ids with
    | [ ] -> tt
    | ics ->
        try
          List.fold_left
            (fun acc ic ->
              RevMap.add ic (RevMap.find ic tt) acc
            ) RevMap.empty ics
        with Not_found -> RevMap.empty in
  (* runing of analyses *)
  let run_tests (category: test_category) (tests: test_spec RevMap.t)
      : float * test_result RevMap.t =
    let eq_category c0 c1 =
      match c0, c1 with
      | TC_valid, TC_valid | TC_exp, TC_exp -> true
      | TC_other s0, TC_other s1 -> String.compare s0 s1 = 0
      | _, _ -> false in
    (* sequential prtp run *)
    RevMap.fold
      (fun i t (accd, accr) ->
         let cats = List.filter (eq_category category) t.sp_category in
         if cats != [ ] then
           let d, r = run_test !analyzer !stress_test i t in
           accd +. d, RevMap.add i r accr
         else accd, accr
      ) tests (0., RevMap.empty) in
  if !test_ids = [ ] then
    (* general run: all tests in a category *)
    begin
      (* removal of excluded tests *)
      let tests =
        RevMap.fold
          (fun ic t acc ->
            if t.sp_excluded then acc
            else RevMap.add ic t acc
          ) tests RevMap.empty in
      (* tests which were already validated *)
      let out_valid =
        if not !flag_pure_regtest then 0., RevMap.empty
        else run_tests TC_valid tests in
      (* experimental tests *)
      let out_expe =
        if not !flag_pure_expe then 0., RevMap.empty
        else run_tests TC_exp tests in
      (* category specific tests *)
      let out_other =
        if String.length !category = 0 then 0., RevMap.empty
        else run_tests (TC_other !category) tests in
      (* display results *)
      if !ncores = 1 then
        begin
          if not !flag_pure_expe && snd out_valid != RevMap.empty then
            pp_results (Some true)  (fst out_valid) tests (snd out_valid);
          if not !flag_pure_regtest && snd out_expe != RevMap.empty then
            pp_results (Some false) (fst out_expe)  tests (snd out_expe);
          if snd out_other != RevMap.empty then
            pp_results (Some false) (fst out_other) tests (snd out_other)
        end
    end
  else
    let out_t, out_r =
      RevMap.fold
        (fun i t (accd, accr) ->
          let d, r = run_test !analyzer !stress_test i t in
          accd +. d, RevMap.add i r accr
        ) tests (0., RevMap.empty) in
    pp_results None out_t tests out_r

let () = batch ()
