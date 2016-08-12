(** MemCAD analyzer
 **
 ** domsel_lexer.mll
 ** domain structure lexer
 ** Xavier Rival, 2012/04/05 *)
{
open Domsel_parser
}

rule token = parse
| ' ' | '\t'              { token lexbuf }
| '\n'                    { incr Lex_lib.num_line; token lexbuf }
| (['a'-'z']|['A'-'Z'])(['a'-'z']|['A'-'Z']|'_'|['0'-'9'])*
                          { let str = Lexing.lexeme lexbuf in
                            Log.info "parsed %s" str;
                            V_string str }
| "@ll"                   { T_all }
| "#list"                 { T_list }
| '^'                     { T_and }
| '*'                     { T_star }
| ','                     { T_comma }
| '('                     { T_lpar }
| ')'                     { T_rpar }
| '['                     { T_lbrack }
| ']'                     { T_rbrack }
| '_'                     { T_underscore }
| eof                     { T_eof }
