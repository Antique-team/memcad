(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: main.ml
 **       entry point, and testing
 ** Xavier Rival, 2011/05/22 *)
open Flags
open Lib
open Ast_sig
open Data_structures

(** Error report *)
module Log =
  Logger.Make(struct let section = "main____" and level = Log_level.DEBUG end)
module T = Timer.Timer_Mod( struct let name = "Main" end )

(** Exception reporting *)
let exn_report (e: exn): unit =
  begin
    match e with
    | Apron.Manager.Error exc ->
      let open Apron.Manager in
      Log.fatal ("Apron failure:\n" ^^
                 "exn = %s\n" ^^
                 "funid = %s\n" ^^
                 "msg = %s")
        (string_of_exc exc.exn) (string_of_funid exc.funid) exc.msg
    | _ -> Log.fatal "%s" (Printexc.to_string e)
  end;
  exit 1

(** Parsers *)

(* Basic parsers for parameters *)
let ilines_parser =
  Lib.read_from_file "ind" Ind_parser.main_ilines Ind_lexer.token

let array_ind_parser =
  Lib.read_from_file "ind" Ind_parser.array_indlist Ind_lexer.token

(* Testing parsers *)
let meta_test_parser
    (msg: string)
    (f_parse: (Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'a)
    (f_lexe: Lexing.lexbuf -> 'b)
    (f_post: 'a -> unit)
    (files: string list): unit =
  Log.info "\nTest of the lexer of %s" msg;
  let parse_ind_file =
    Lib.read_from_file msg f_parse f_lexe in
  List.iter
    (fun file ->
      try
        Log.info "parsing %s..." file;
        let x = parse_ind_file file in
        Log.info "  [Ok]";
        f_post x
      with
      | e -> exn_report e
    ) files;
  Log.info "Finished!"
(* Old C parser *)
let run_old_parser (f: C_sig.c_prog -> unit): string list -> unit =
  meta_test_parser "c mini programs" C_parser.entry C_lexer.token f

(* FBR: this is dirty; those options must be passed to the transforms *)
(* (\* setup logger used by the AST transformations *\) *)
(* let setup_logger (s: string): unit = *)
(*   let level_str = *)
(*     if BatString.starts_with s "color:" then *)
(*       let _ = Log.color_on () in *)
(*       BatString.lchop ~n:(String.length "color:") s *)
(*     else *)
(*       s in *)
(*   let level = Log.level_of_string level_str in *)
(*   Log.set_log_level level; *)
(*   Log.set_output stdout *)

(* handle the user-provided and coma-separated list of include *)
(* dirs for additional C headers *)
let expand_include_dirs () =
  if !include_dirs = "" then
    []
  else if String.contains !include_dirs ',' then
    let dirs = BatString.nsplit !include_dirs ~by:"," in
    List.map (fun dir -> "-I" ^ dir) dirs
  else
    ["-I" ^ !include_dirs]

(* parse C files with clangml, with optional storing/loading to/from
 * dump files *)
let run_clangml_parser
    (c_parser: C_sig.c_prog -> unit) (files: string list): unit =
  (* setup_logger !Flags.transforms_log_level; *)
  List.iter
    (fun file ->
      let dump_fn = file ^ ".dump" in
      let c_prog =
         if !Flags.load_dump then
           with_in_file dump_fn
             (fun input ->
                let decls = (Marshal.from_channel input : Transform.env) in
                Transform.c_prog_from_decls decls)
         else
           begin
             if not (Sys.file_exists !clang_header_fn) then
               Log.fatal_exn "main.ml: run_clangml_parser: file not found: %s"
                 !clang_header_fn;
             let clang_opts =
               (* memcad assumes a 32bit environment, hence the -m32 option *)
               ["-m32"; "-include"; !clang_header_fn; "-w"; file;
                "-DMEMCAD_INRIA"] @ expand_include_dirs () in
             Clang.Api.parse clang_opts
               (fun clang ->
                 let translation_unit =
                   Clang.Api.request clang Clang.Api.TranslationUnit in
                 let after_transformations =
                   For_memcad.Transformation.All.transform_decl
                     (* to disable all transformations, use that one
                      * For_memcad.Transformation.Identity.transform_decl *)
                     clang translation_unit in
                 let decls =
                   Transform.decls_from_decl
                     !test_verbose clang after_transformations in
                 if !Flags.dump_parse then
                   with_out_file dump_fn
                     (fun out -> Marshal.to_channel out decls []);
                 Transform.c_prog_from_decls decls
               )
           end in
       c_parser c_prog
    ) files

let run_c_parser () =
  if !use_old_parser then
    run_old_parser
  else
    run_clangml_parser


(** Initialize the domain *)
(* Initialization of the inductive definitions domain *)
let init_inductives (ifile: string): unit =
  let _ =
    if !enable_array_domain then
      let al = array_ind_parser ifile in
      Array_ind_utils.array_ind_init al
    else
      let l = ilines_parser ifile in
      Ind_utils.ind_init l in
  (* antoine: do the inductive defs pre-analysis *)
  if !reduction_mode_selector != Rm_disabled then
    begin
      T.app1 "ind_preds_init" Ind_analysis.ind_preds_init ();
      T.app1 "seg_preds_init" Ind_analysis.seg_preds_init ()
    end
(* The function below is experimental code, that tries to see which
 * inductive definitions describe some form of list, and that tries
 * to extract all relevant information about these inductive
 * definitions *)
let exp_search_lists (indfile: string option) (domstruct: shape_dom): unit =
  let has_list =
    let rec aux = function
      | Shd_flat | Shd_all | Shd_inds _ | Shd_tvl -> false
      | Shd_list -> true
      | Shd_prod (s0, s1) | Shd_sep (s0, s1) -> aux s0 || aux s1 in
    aux domstruct in
  if has_list && indfile != None && not !enable_array_domain then
    List_utils.exp_search_lists ( )
  else if !enable_array_domain && indfile != None then
    Array_ind_utils.exp_search_array_lists ( )

let search_ppred (indfile: string option): unit =
  if indfile != None then
    Array_ppred_utils.search_ppred ( )

(** Starting the analysis *)
let do_analyze
    (indfile: string option) (* input file for inductive definitions *)
    (filename: string)       (* input C file *)
    (shapedom_struct: shape_dom) (* shape domain structure *)
    (mainfun: string)        (* main function *)
    (repeat_num: int)        (* stress-testing *)
    : unit =
  (* Inductive definitions initializations *)
  let inductives_initialization = function
    | None -> ( ) (* analysis with no inductive definition *)
    | Some ifile ->
        (* some inductive definitions to parse beforehand *)
        init_inductives ifile in
  inductives_initialization indfile;
  exp_search_lists indfile shapedom_struct;
  search_ppred indfile;
  (* Numerical domain construction *)
  let mod_apron =
    let mod_pre_apron =
      match !nd_selector with
      | ND_box -> (module Nd_apron.PA_box:   Nd_apron.PRE_APRON)
      | ND_oct -> (module Nd_apron.PA_oct:   Nd_apron.PRE_APRON)
      | ND_pol -> (module Nd_apron.PA_polka: Nd_apron.PRE_APRON) in
    let module MPA = (val mod_pre_apron: Nd_apron.PRE_APRON) in
    let msa =
      if !stat_apron then
        (module Nd_apron.Abstract1_stat: Nd_apron.ABSTRACT1_TYPE)
      else (module Apron.Abstract1: Nd_apron.ABSTRACT1_TYPE) in
    let module MSA = (val msa: Nd_apron.ABSTRACT1_TYPE) in
    let apr = (module Nd_apron.Build_apron( MSA )( MPA ): Nd_sig.DOM_NUM_NB) in
    let module APR = (val apr: Nd_sig.DOM_NUM_NB) in
    if !Flags.timing_apron then
      (module Nd_timing.Dom_num_nb_timing( APR ): Nd_sig.DOM_NUM_NB)
    else (module APR: Nd_sig.DOM_NUM_NB) in
  let module MApron  = (val mod_apron: Nd_sig.DOM_NUM_NB) in
  let module MAeq = Nd_add_eqs.Add_eqs( MApron ) in
  let mod_eq =
    if !enable_eq_pack then
      (module Nd_add_eqp.Add_eq_partition( MAeq ): Nd_sig.DOM_NUM_NB)
    else (module MAeq: Nd_sig.DOM_NUM_NB) in
  let module MAeq = (val mod_eq: Nd_sig.DOM_NUM_NB) in
  let module MAdiseq = Nd_add_diseqs.Add_diseqs( MAeq ) in
  let mod_dynenv =
    if !enable_dynenv then
      (module Nd_add_dyn_svenv.Add_dyn_svenv( MAdiseq ): Nd_sig.DOM_NUM_NB)
    else (module MAdiseq: Nd_sig.DOM_NUM_NB) in
  let module MAde    = (val mod_dynenv: Nd_sig.DOM_NUM_NB) in
  let module MNum    = Nd_add_bottom.Add_bottom( MAde ) in
  let module MVal0   = Dom_val_num.Make_val_num( MNum ) in
  assert (not (!enable_submem && !enable_array_domain));
  let mod_val1 =
    if !enable_submem then
      let module MSub = Dom_subm_graph.Submem in
      (module Dom_val_subm.Make_Val_Subm( MVal0 )( MSub ): Dom_sig.DOM_VALUE)
    else (module MVal0: Dom_sig.DOM_VALUE) in
  let mod_val2 =
    if !timing_value then
      let module MVal1 = (val mod_val1: Dom_sig.DOM_VALUE) in
      (module Dom_val_num.Dom_val_timing( MVal1 ): Dom_sig.DOM_VALUE)
    else mod_val1 in
  let module MVal2 = (val mod_val2: Dom_sig.DOM_VALUE) in
  (* Addition of the set domain if needed *)
  let mod_vset1 =
    match !sd_selector with
    | SD_lin ->
        let mod_set =
          if !flag_dump_ops then
            (module Set_dump.Make( Set_lin.Set_lin ): Set_sig.DOMSET)
          else (module Set_lin.Set_lin: Set_sig.DOMSET) in
        let module MSet = (val mod_set: Set_sig.DOMSET) in
        let mod_set =
          if !timing_valset then
            (module Nd_timing.Dom_set_timing( MSet ): Set_sig.DOMSET)
          else (module MSet: Set_sig.DOMSET) in
        let module MSet = (val mod_set: Set_sig.DOMSET) in
        (module Dom_set.DBuild( MVal2 )( MSet ): Dom_sig.DOM_VALSET)
    | SD_setr s ->
        let module L = SETr.SymSing.Logic in
        let d =
          match s with
          | "bdd" ->
              let module D0 = SETr.Symbolic.BDD.MLBDD in
              let module D1 = SETr.SymSing.Sing.Make( D0 ) in
              (module D1 : SETr.Domain with
               type sym = int
               and type cnstr  = int L.t
               and type output = int L.t )
          | "lin" ->
              begin
                match SETr.get s with
                | SETr.SymSing d ->
                    let module D = (val d) in
                    (module D: SETr.Domain with
                     type sym = int
                     and type cnstr  = int L.t
                     and type output = int L.t )
                | _ ->  Log.fatal_exn "unbound SETr module: %s" s
              end
          | _ ->  Log.fatal_exn "unbound SETr module name: %s" s in
        let module D = (val d) in
        let module MPre =
          struct
            let name = s
            module D = (val d)
            let ctx = D.init ( )
          end in
        let mod_set =
          (module Set_setr.Make( MPre ): Set_sig.DOMSET) in
        let module MSet = (val mod_set: Set_sig.DOMSET) in
        let mod_set =
          if !timing_valset then
            (module Nd_timing.Dom_set_timing( MSet ) : Set_sig.DOMSET)
          else (module MSet: Set_sig.DOMSET) in
        let module MSet = (val mod_set: Set_sig.DOMSET) in
        (module Dom_set.DBuild( MVal2 )( MSet ): Dom_sig.DOM_VALSET)
    | SD_quicr ->
        let mod_quickr = (* temporary: add timing and logging *)
          if true || !flag_dump_ops then
            (module Quicr_dump.Make( Quicr_lin ): Set_quicr.SDomain)
          else (module Quicr_lin: Set_quicr.SDomain) in
        let module MQuickr = (val mod_quickr: Set_quicr.SDomain) in
        let mod_set = (module Set_quicr.Make( MQuickr ): Set_sig.DOMSET) in
        let module MSet = (val mod_set: Set_sig.DOMSET) in
        (module Dom_set.DBuild( MVal2 )( MSet ): Dom_sig.DOM_VALSET)
    | SD_none ->
        (module Dom_no_set.DBuild( MVal2 ): Dom_sig.DOM_VALSET) in
  let module MVSet1 = (val mod_vset1: Dom_sig.DOM_VALSET) in
  (* Add array *)
  let mod_vset1 = 
    if !enable_array_domain then
      (module Dom_val_array.Make_VS_Array( MVSet1 ): Dom_sig.DOM_VALSET)
    else mod_vset1 in
  let module MVSet1 = (val mod_vset1: Dom_sig.DOM_VALSET) in
  let mod_vset2 =
    if !timing_valset then
      let module MVSet1 = (val mod_vset1: Dom_sig.DOM_VALSET) in
      (module Dom_timing.Dom_valset_timing( MVSet1 ): Dom_sig.DOM_VALSET)
    else mod_vset1 in
  let module MVSet2 = (val mod_vset2: Dom_sig.DOM_VALSET) in
  (* shape domain construction *)
  let add_timing m r os =
    let module D = (val m: Dom_sig.DOM_MEM_LOW) in
    let s_inds =
      match os with
      | None -> StringSet.empty
      | Some s -> s in
    ignore (D.init_inductives Keygen.empty s_inds);
    if !r then
      (module Dom_timing.Dom_mem_low_timing( D ): Dom_sig.DOM_MEM_LOW)
    else (module D: Dom_sig.DOM_MEM_LOW) in
  let build_shape_ind (s: StringSet.t) =
    Log.info "Creating summarizing shape domain <%d inductives>"
      (StringSet.cardinal s);
    let m = (module Dom_mem_low_shape.DBuild( MVSet2 ): Dom_sig.DOM_MEM_LOW) in
    add_timing m timing_bshape (Some s) in
  let build_shape_flat () =
    Log.info "Creating flat shape domain (with no summarization)";
    let m = (module Dom_mem_low_flat.DBuild( MVSet2 ): Dom_sig.DOM_MEM_LOW) in
    add_timing m timing_fshape None in
  let build_shape_list () =
    Log.info "Creating ad-hoc list domain";
    let m = (module Dom_mem_low_list.DBuild( MVSet2 ): Dom_sig.DOM_MEM_LOW) in
    add_timing m timing_lshape None in
  let build_shape_tvl () =
    Log.info "Creating ad-hoc TVL domain";
    let m = (module Dom_mem_low_tvl.DBuild( MVSet2 ): Dom_sig.DOM_MEM_LOW) in
    add_timing m timing_lshape None in
  let rec sd_2str = function
    | Shd_flat -> "[___]"
    | Shd_all -> "[@ll]"
    | Shd_list -> "[#list]"
    | Shd_tvl -> "[tvl]"
    | Shd_inds l -> Printf.sprintf "[%s]" (gen_list_2str "" (fun x -> x) "," l)
    | Shd_prod (d0, d1) -> Printf.sprintf "(%s X %s)" (sd_2str d0) (sd_2str d1)
    | Shd_sep (d0, d1) ->
        Printf.sprintf "(%s * %s)" (sd_2str d0) (sd_2str d1) in
  let rec build_domain ind (sd: shape_dom) =
    Log.info "%sBuild_domain called %s" ind (sd_2str sd);
    match sd with
    | Shd_flat ->
        build_shape_flat ()
    | Shd_all ->
        let inds =
          StringMap.fold
            (fun s _ -> StringSet.add s) !Ind_utils.ind_defs StringSet.empty in
        build_shape_ind inds
    | Shd_list ->
        build_shape_list ()
    | Shd_tvl ->
        build_shape_tvl ()
    | Shd_inds lst ->
        let inds =
          List.fold_left
            (fun acc i ->
              Log.info "%sBuild domain adds inductive %s to domain" ind i;
              assert (StringMap.mem i !Ind_utils.ind_defs);
              StringSet.add i acc
            ) StringSet.empty lst in
        build_shape_ind inds
    | Shd_sep (d0, d1) ->
        let nind = "   " ^ ind in
        let m0 = build_domain nind d0 in
        let module D0 = (val m0: Dom_sig.DOM_MEM_LOW) in
        let m1 = build_domain nind d1 in
        let module D1 = (val m1: Dom_sig.DOM_MEM_LOW) in
        let module D = Dom_mem_low_sep.Dom_sep( D0 )( D1 ) in
        if !timing_sshape then
          (module Dom_timing.Dom_mem_low_timing( D ): Dom_sig.DOM_MEM_LOW)
        else
          (module D: Dom_sig.DOM_MEM_LOW)
    | Shd_prod (d0, d1) ->
        let nind = "   " ^ ind in
        let m0 = build_domain nind d0 in
        let module D0 = (val m0: Dom_sig.DOM_MEM_LOW) in
        let m1 = build_domain nind d1 in
        let module D1 = (val m1: Dom_sig.DOM_MEM_LOW) in
        let module D = Dom_mem_low_prod.Dom_prod( D0 )( D1 ) in
        if !timing_pshape then
          (module Dom_timing.Dom_mem_low_timing( D ): Dom_sig.DOM_MEM_LOW)
        else
          (module D: Dom_sig.DOM_MEM_LOW) in
  let mshape = build_domain "" shapedom_struct in
  let module MShape = (val mshape: Dom_sig.DOM_MEM_LOW) in
  (* Memory domain, expressions layer *)
  let module MMExprs = Dom_mem_exprs.DBuild( MShape ) in
  let m =
    if !timing_mem_exprs then
      (module
          Dom_mem_exprs.Dom_mem_exprs_timing( MMExprs ): Dom_sig.DOM_MEM_EXPRS)
    else (module MMExprs: Dom_sig.DOM_MEM_EXPRS) in
  let module MMExprs = (val m: Dom_sig.DOM_MEM_EXPRS) in
  (* Environment domain *)
  let module MEnv    = Dom_env.Dom_env( MMExprs ) in
  let m =
    if !timing_env then (module Dom_env.Dom_env_timing( MEnv ): Dom_sig.DOM_ENV)
    else (module MEnv: Dom_sig.DOM_ENV) in
  let module MEnv = (val m: Dom_sig.DOM_ENV) in
  (* Disjunction domain *)
  let m =
    if !timing_graph_encode then
      (module Graph_encode.Graph_encode_timing( Graph_encode.Graph_encode )
          : Dom_sig.GRAPH_ENCODE)
    else
      (module Graph_encode.Graph_encode: Dom_sig.GRAPH_ENCODE) in
  let module GEncode = (val m: Dom_sig.GRAPH_ENCODE) in
  let mod_disj =
    if !disj_selector then
      if !timing_disj then
        (module
            Dom_disj.Dom_disj_timing ( Dom_disj.Dom_disj( MEnv )( GEncode ) )
           : Dom_sig.DOM_DISJ)
      else
        (module Dom_disj.Dom_disj( MEnv )( GEncode ): Dom_sig.DOM_DISJ)
    else
      (module Dom_no_disj.Dom_no_disj( MEnv )( GEncode ): Dom_sig.DOM_DISJ) in
  let module MDisj = (val mod_disj: Dom_sig.DOM_DISJ) in
  (* C domain and analyzer *)
  let module Path_liveness = C_pre_analyze.Path_liveness in
  let module Var_liveness = C_pre_analyze.Var_liveness in
  let module Mpre_path_analysis =
    C_pre_analyze.Gen_pre_analysis( Path_liveness ) in
  let module Mpre_var_analysis =
    C_pre_analyze.Gen_pre_analysis( Var_liveness ) in
  let module MC      = Dom_c.Dom_C( MDisj ) in
  Log.info "abstract domain config:\n%s" (MC.config_2str ());
  let module MAnalyzer = C_analyze.Make( MC )( Mpre_path_analysis ) in
  (* Launching the analysis *)
  let time_start = Timer.cpu_timestamp () in
  run_c_parser ()
    (fun cp ->
      let cp = C_process.process_c_prog cp in
      if !test_verbose then Log.info "%s" (C_utils.c_prog_2stri "    " cp);
      if do_live_analysis then
        begin
          ignore (C_pre_analyze.live_prog mainfun cp);
          ignore (Mpre_var_analysis.live_prog mainfun cp)
        end;
      pp_config_report ();
      (* Materialization for array analysis *)
      if !enable_array_domain then
        begin
          let module Mater =  C_pre_analyze.Materialization in
          let module Mpre_Mater_analysis =
            C_pre_analyze.Gen_path_sensitive_pre_analysis( Mater ) in
          let acc = Mpre_Mater_analysis.pre_prog mainfun cp in
          Array_node.mat_var:= Mpre_Mater_analysis.mat_resolve acc;
          Log.info "%s"
            (Mpre_Mater_analysis.t_2str
               (Mpre_Mater_analysis.pre_prog mainfun cp))
        end;
      for i = 1 to repeat_num do
        MAnalyzer.analyze_prog mainfun cp
      done
    ) [ filename ];
  pipe_end_status_report ( );
  Statistics.show_gc_statistics ( );
  Timer.print_timing_infos ();
  let time_finish = Timer.cpu_timestamp () in
  Nd_apron.pp_histo ( );
  show_end_status_report (time_finish -. time_start)

(* Inference of inductive definitions *)
let do_infer_ind (filename: string) (out_file: string): unit =
  run_c_parser ()
    (fun cp ->
      let cp = C_process.process_c_prog cp in
      if !test_verbose then Log.info "%s" (C_utils.c_prog_2stri "    " cp);
      let l = C_ind_infer.compute_inductives cp in
      Log.info "Computed inductive definitions:\n";
      List.iter (fun ind -> Log.info "%s" (Ind_utils.ind_2str ind)) l;
      Ind_utils.rules_to_file out_file l
    ) [ filename ]


(** Pre-analysis configuration *)
let configure_pp (add_pps: string list) (rem_pps: string list): unit =
  let get_ref: string -> bool ref list = function
    (* global switches *)
    | "pp_is_le" ->
        [ flag_debug_is_le_gen; flag_debug_is_le_shape;
          flag_debug_is_le_num; flag_debug_is_le_strategy ]
    | "pp_join" ->
        [ flag_debug_join_gen; flag_debug_join_shape;
          flag_debug_join_num; flag_debug_join_strategy ]
    (* pretty-printing stuffs *)
    | "pp_nodeinfos"            -> [ flag_pp_nodeinfos ]
    | "debug_back_index"        -> [ flag_debug_back_index ]
    (* debugging *)
    | "pp_debug_materialize"    -> [ flag_debug_materialize ]
    | "pp_debug_unfold"         -> [ flag_debug_unfold ]
    | "pp_debug_bwd_unfold"     -> [ flag_debug_bwd_unfold ]
    | "pp_debug_trigger_unfold" -> [ flag_debug_trigger_unfold ]
    | "pp_debug_disj"           -> [ flag_debug_disj ]
    | "pp_debug_dommem_eval"    -> [ flag_debug_dommem_eval ]
    | "pp_debug_guard"          -> [ flag_debug_guard ]
    | "pp_debug_assign"         -> [ flag_debug_assign ]
    | "pp_debug_num_env"        -> [ flag_debug_num_env ]
    | "pp_debug_list_dom"       -> [ flag_debug_list_dom ]
    | "pp_debug_reduction"      -> [ flag_debug_reduction ]
    | "pp_display_num_env"      -> [ flag_display_num_env ]
    (* status at various statements *)
    | "pp_status_decl"          -> [ flag_status_decl ]
    | "pp_status_block"         -> [ flag_status_block ]
    (* statistics *)
    | "stats"                   -> [ enable_stats ]
    | "stat_apron"              -> [ stat_apron ]
    (* other cases are left as an Log.fatal_exn for now *)
    | s -> Log.fatal_exn "configure_pp: unknown string %s" s in
  List.iter (fun s -> List.iter (fun r -> r := true ) (get_ref s)) add_pps;
  List.iter (fun s -> List.iter (fun r -> r := false) (get_ref s)) rem_pps

(* config is a list of modules and log levels like: 'l_abs:fatal,l_mat:debug'
 * or even shorter: 'l_abs:f,l_mat:d' *)
let set_log_level_per_module (config: string): unit =
  (* For the logger, a module name has 8 characters;
   * trailing chars are underscores. *)
  let extend_module_name (short: string): string =
    let len = String.length short in
    let ext_len = 8 - len in
    assert(ext_len >= 0);
    let ext = String.make ext_len '_' in
    short ^ ext in
  let modules_and_levels = Str.split (Str.regexp ",") config in
  List.iter
    (fun str ->
      let mod_name, ll = BatString.split ~by:":" str in
      let log_level = Log_level.of_string ll in
      match Logger_glob.expand_modules_group mod_name with
      | [] -> (* not a group of modules *)
          let mod_name = extend_module_name mod_name in
          Logger_glob.set_log_level mod_name log_level
      | modules ->
          List.iter (fun m -> Logger_glob.set_log_level m log_level) modules
    ) modules_and_levels

(** Start *)
let main ( ): unit =
  (* References *)
  let mode_analyze:   bool ref          = ref false in
  let mode_infer_ind: bool ref          = ref false in
  let indfile:        string option ref = ref None in
  let filename:       string ref        = ref "" in
  let add_pps:        string list ref   = ref [] in
  let rem_pps:        string list ref   = ref [] in
  let stress_test:    int ref           = ref 1 in
  (* Setter functions *)
  let set_numdom (nd: num_dom) (): unit = nd_selector := nd in
  let set_setdom (sd: set_dom) (): unit = sd_selector := sd in
  let set_setrdom (sd: string) = set_setdom (SD_setr sd) in
  let set_red_mode (rm: reduction_mode) (): unit =
    reduction_mode_selector:= rm in
  let set_stringopt (r: string option ref) (f: string): unit = r := Some f in
  let set_domstruct str = shapedom_struct := str in
  let add_submem_ind s = submem_inds := StringSet.add s !submem_inds in
  let add_pp s = add_pps := s :: !add_pps in
  let rem_pp s = rem_pps := s :: !rem_pps in
  let add_time s =
    let r =
      match s with
      | "apron"  -> timing_apron
      | "base"   -> timing_bshape
      | "flat"   -> timing_fshape
      | "list"   -> timing_lshape
      | "prod"   -> timing_pshape
      | "sep"    -> timing_sshape
      | "mexprs" -> timing_mem_exprs
      | "env"    -> timing_env
      | "value"  -> timing_value
      | "valset" -> timing_valset
      | "encode" -> timing_graph_encode
      | "disj"   -> timing_disj
      | _ -> Log.fatal_exn "unbound module to time: %s" s in
    r := true in
  let add_widen_thr i =
    widen_thresholds := IntSet.add i !widen_thresholds in
  (* Parsing of arguments *)
  Arg.parse
    [ (* test mode *)
      "-a",           Arg.Set mode_analyze, "launch analysis";
      "-analyze",     Arg.Set mode_analyze, "launch analysis";
      "-stats",       Arg.Set enable_stats, "statistics";
      "-silent",      Arg.Unit debug_disable, "silent testing";
      "-very-silent", Arg.Unit very_silent, "very silent testing, for timing";
      "-verbose",     Arg.Set test_verbose, "verbose testing";
      "-v",           Arg.Set test_verbose, "verbose testing";
      "-main",        Arg.String (fun s -> mainfun := s), "main function";
      "-rec-calls",   Arg.Set rec_calls, "analysis of recursive calls";
      "-set-on",      Arg.String add_pp, "enable boolean settings";
      "-set-off",     Arg.String rem_pp, "disable boolean settings";
      "-no-timing",   Arg.Clear flag_pp_timing, "disable timing pp";
      "-reachable",   Arg.Set Flags.show_reachable_functions,
      "show functions reachable from entry point";
      (* source language semantics *)
      ("-malloc-non0",Arg.Set Flags.flag_malloc_never_null,
       "only consider cases where malloc does not return null");
      (* timing and stress test *)
      "-timing",      Arg.String add_time, "perform timing of a module";
      "-stress-test", Arg.Int (fun i -> stress_test := i), "repeat number";
      (* inductive definitions settings *)
      "-use-ind",     Arg.String (set_stringopt indfile), "inductive file";
      "-ind-analysis",Arg.Set flag_indpars_analysis, "turns on ind analysis";
      "-auto-ind",    Arg.Set mode_infer_ind, "infer inductive definitions";
      "-no-prev-fields", Arg.Set Flags.no_ind_prev_fields,
      "ignore prev fields upon graph encoding";
      (* structure of the shape domain *)
      "-shape-dom",   Arg.String set_domstruct, "shape domain structure";
      (* numeric domain selection *)
      "-nd-box",      Arg.Unit (set_numdom ND_box), "selects box domain";
      "-nd-oct",      Arg.Unit (set_numdom ND_oct), "selects oct domain";
      "-nd-pol",      Arg.Unit (set_numdom ND_pol), "selects pol domain";
      (* value domain configuration *)
      "-add-submem",  Arg.Set enable_submem, "enables sub-memory abstraction";
      "-submem-ind",  Arg.String add_submem_ind, "sub-memory inductive";
      "-dynenv-yes",  Arg.Set enable_dynenv, "dynenv in num";
      "-dynenv-no",   Arg.Clear enable_dynenv, "no dynenv in num";
      (* equation pack *)
      "-eq-pack-on",    Arg.Set enable_eq_pack, "enable equation pack";
      "-eq-pack-off",    Arg.Clear enable_eq_pack, "disable equation pack";
      (* array domain activation / deactivation *)
      "-array-on",    Arg.Set enable_array_domain, "enable array domain";
      "-array-off",   Arg.Clear enable_array_domain, "disable array domain";
      (* disjunction domain activation *)
      "-disj-on",     Arg.Set disj_selector, "disjunctive domain ON (default)";
      "-disj-off",    Arg.Clear disj_selector, "disjunctive domain OFF";
      (* set domain activation *)
      "-setd-lin",    Arg.Unit (set_setdom SD_lin)  , "set dom lin";
      "-setd-off",    Arg.Unit (set_setdom SD_none) , "set dom None";
      "-setd-quicr",  Arg.Unit (set_setdom SD_quicr), "set dom QUICr";
      "-setd-r-lin",  Arg.Unit (set_setrdom "lin"), "set dom SETr-lin";
      "-setd-r-bdd",  Arg.Unit (set_setrdom "bdd"), "set dom SETr-bdd";
      (* dumping domain operations *)
      "-dump-ops",    Arg.Set flag_dump_ops, "activate operations dump";
      (* iteration strategy and widening parameters *)
      "-w-thr",       Arg.Set widen_do_thr, "activate threshold widening";
      "-w-no-thr",    Arg.Clear widen_do_thr, "deactivate threshold widening";
      "-w-add-thr",   Arg.Int add_widen_thr, "add widening threshold";
      "-j-iters",     Arg.Int (fun i -> join_iters:=i), "# of join iters";
      "-dw-iters",    Arg.Int (fun i -> dweak_iters := i), "# dir. weak iters";
      "-unrolls",     Arg.Int (fun i -> unrolls := i), "# of unroll iters";
      "-type-unfolds",Arg.Int (fun i -> type_unfolds := i), "# of type unfolds";
      "-no-unroll-in",Arg.Clear unroll_inner, "deactivate inner loops unroll";
      "-part-lfps",   Arg.Set part_through_lfps, "partition through loops";
      "-no-part-lfps",Arg.Clear part_through_lfps, "no partition through loops";
      "-sel-widen",   Arg.Set sel_widen, "select widening through loops";
      "-no-sel-widen",Arg.Clear sel_widen, "no select widen through loops";
      "-no-guided-join", Arg.Clear Flags.guided_join, "unguided join";
      "-guided-widen",    Arg.Set   Flags.guided_widen, "guided widen";
      "-no-guided-widen", Arg.Clear Flags.guided_widen, "unguided widen";
      "-widen-can",   Arg.Set Flags.widen_can,
      "canonicalization-like abstraction of shape graphs during join/widen \
       (simpler but less powerful)";
      "-basic-widen", Arg.Set old_widen, "basic disj widening algorithm";
      ("-no-basic-widen",Arg.Clear old_widen, "no basic disj widening");
      "-unary-abs",   Arg.Set do_unary_abstraction, "turns on unary abs";
      "-no-unary-abs",Arg.Clear do_unary_abstraction, "turns off unary abs";
      "-no-fast-iir", Arg.Clear do_quick_ind_ind_mt, "disable fast ind-ind emp";
      (* reduction *)
      "-red-disabled",Arg.Unit (set_red_mode Rm_disabled), "reduction disabled";
      "-red-manual",  Arg.Unit (set_red_mode Rm_manual), "man reduction";
      "-red-min",     Arg.Unit (set_red_mode Rm_minimal), "min reduction";
      "-red-on-read", Arg.Unit (set_red_mode Rm_on_read), "on read reduction";
      "-red-on-r-u",  Arg.Unit (set_red_mode Rm_on_read_and_unfold),
      "on read and unfold reduction mode";
      "-red-max",     Arg.Unit (set_red_mode Rm_maximal), "max reduction";
      (* internal domain settings *)
      "-no-full-gc",  Arg.Clear flag_gc_full, "deactivate the full GC";
      (* latex output (turned off for regression tests) *)
      "-dot-all",     Arg.Set flag_enable_ext_export_all, "dot, at all points";
      "-latex",       Arg.Set flag_latex_output, "latex output";
      (* sending the results on a pipe *)
      "-pipe",        Arg.Set use_pipe, "communication of results on a pipe";
      (* C parsing *)
      "-clang-parser",Arg.Clear use_old_parser, "use Clang parser (default)";
      "-old-parser",  Arg.Set use_old_parser, "use historic, old C parser";
      ("-dump-parse",  Arg.Set dump_parse,
       "dump AST of the analyzed file (after clang and all transformations)");
      ("-load-dump",   Arg.Set load_dump,
       "load an AST dump; cf. -dump-parse option");
      "-header",      Arg.Set_string clang_header_fn, "header for Clang";
      "-idirs",       Arg.Set_string include_dirs,
      "directories for C headers; example -idirs include,/usr/include";
      "-tlog",        Arg.Set_string transforms_log_level,
      "log level during transformations: [color:]fatal|error|warn|info|debug";
      "-log",         Arg.String set_log_level_per_module,
      "non default log level per module; example: -log l_abs:fatal,l_mat:debug";
    ] (fun s -> filename := s) "";
  (* display the command line *)
  let args = Array.to_list Sys.argv in
  Log.info "Command line was: %s" (gen_list_2str "" (fun x -> x) " " args);
  (* sets up printers *)
  configure_pp !add_pps !rem_pps;
  filebase := Filename.basename !filename;
  if !mode_analyze then
    let sd =
      analyzed_file := !filename;
      let s = !shapedom_struct in
      let n = String.length s in
      assert (n > 2);
      let s = String.sub s 1 (n-2) in
      Log.info "Parsing string: %s" s;
      if !mode_infer_ind then
        begin
          Flags.auto_ind := true;
          let res = "auto.ind" in
          do_infer_ind !filename "auto.ind";
          indfile := Some res
        end;
      read_from_string "domain structure"
        Domsel_parser.edomshape Domsel_lexer.token s in
    do_analyze !indfile !filename sd !mainfun !stress_test
  else if !mode_infer_ind then
    begin
      do_infer_ind !filename "inferred.ind"
    end

(* Run *)
let () = main ()
