(** MemCAD analyzer
 **
 ** config_lexer.mly
 ** configuration file lexer
 ** Xavier Rival, 2011/09/29 *)
{
open Config_parser
(* Integer plots extraction *)
let extract_plot_int s =
  let n = String.length s in
  assert (n > 2);
  int_of_string (String.sub s 1 (n-2))
let extract_plot_int_char s =
  let n = String.length s in
  assert (n > 3);
  int_of_string (String.sub s 1 (n-3)), Some (String.get s (n-2))
(* Extraction from a quoted string *)
let extract_qstring s =
  let n = String.length s in
  assert (n > 2);
  String.sub s 1 (n-2)
}

rule token = parse
| ' ' | '\t'              { token lexbuf }
| '\n'                    { incr Lex_lib.num_line; token lexbuf }
| '%'[^'\n']*'\n'   (* line of comments *)
                          { incr Lex_lib.num_line; token lexbuf }
| '['(['0'-'9'])+']'      { let n = extract_plot_int (Lexing.lexeme lexbuf) in
                            V_plot (n, None) }
| '['(['0'-'9'])+['a'-'z']']'
                          { let nc =
                              extract_plot_int_char (Lexing.lexeme lexbuf) in
                            V_plot nc }
| ['0'-'9']+              { V_int (int_of_string (Lexing.lexeme lexbuf)) }
| (['a'-'z']|['A'-'Z']|'_')(['a'-'z']|['A'-'Z']|'_'|['0'-'9'])*
                          { let str = Lexing.lexeme lexbuf in
                            V_string str }
| '\"'[^'\"']*'\"'        { let s = extract_qstring (Lexing.lexeme lexbuf) in
                            V_qstring s }
| '='                     { T_equal }
| ','                     { T_comma }
| '<'                     { T_less  }
| '>'                     { T_more  }
| '#'                     { T_sharp }
| eof                     { T_eof }
