(** MemCAD analyzer
 **
 ** c_lexer.mll
 ** a rotten C frontend
 ** Xavier Rival, 2011/07/09 *)
{
open C_parser
(* String tokens hash *)
let hash_string_tokens = Hashtbl.create 100
let _ =
  let lst_string_tokens =
    [ (* not C keywords *)
      "_memcad",       (fun l -> T__memcad  l);
      "assert",        (fun l -> T_assert   l);
      "free",          (fun l -> T_free     l);
      "malloc",        (fun l -> T_malloc   l);
      "NULL",          (fun l -> T_null     l);
      "null",          (fun l -> T_null     l);
      (* C keywords *)
      "auto",          (fun l -> T_auto     l);
      "break",         (fun l -> T_break    l);
      "char",          (fun l -> T_char     l);
      "else",          (fun l -> T_else     l);
      "float",         (fun l -> T_float    l);
      "if",            (fun l -> T_if       l);
      "int",           (fun l -> T_int      l);
      "return",        (fun l -> T_return   l);
      "short",         (fun l -> T_short    l);
      "sizeof",        (fun l -> T_sizeof   l);
      "struct",        (fun l -> T_struct   l);
      "typedef",       (fun l -> T_typedef  l);
      "union",         (fun l -> T_union    l);
      "unsigned",      (fun l -> T_unsigned l);
      "void",          (fun l -> T_void     l);
      "volatile",      (fun l -> T_volatile l);
      "while",         (fun l -> T_while    l);
    ] in
  List.iter (fun (str, tok) -> Hashtbl.add hash_string_tokens str tok)
    lst_string_tokens
let retrieve_string_tok (s: string) =
  try Hashtbl.find hash_string_tokens s !Lex_lib.num_line
  with Not_found -> V_string s
}

rule token = parse
| ' ' | '\t'              { token lexbuf }
| '\n'                    { incr Lex_lib.num_line; token lexbuf }
| '/''/'[^'\n']*'\n'   (* line of comments *)
                          { incr Lex_lib.num_line; token lexbuf }
| '\"'[^'\"']*'\"'        { let str = Lexing.lexeme lexbuf in
                            let n = String.length str in
                            V_qstring (String.sub str 1 (n-2)) }
| ['0'-'9']+              { V_int (int_of_string (Lexing.lexeme lexbuf)) }
| (['a'-'z']|['A'-'Z']|'_')(['a'-'z']|['A'-'Z']|'_'|['0'-'9'])*
                          { let str = Lexing.lexeme lexbuf in
                            retrieve_string_tok str }
| "&&"                    { T_ampamp }
| "->"                    { T_arrow }
| "!="                    { T_bangeq }
| "=="                    { T_eqeq }
| ">="                    { T_ge }
| "<="                    { T_le }
| '>'                     { T_gt }
| '<'                     { T_lt }
| "||"                    { T_pipepipe }
| ','                     { T_comma }
| ';'                     { T_semicolon !Lex_lib.num_line }
| '&'                     { T_amp }
| '.'                     { T_dot }
| '='                     { T_eq }
| '-'                     { T_minus }
| '|'                     { T_pipe }
| '+'                     { T_plus }
| '*'                     { T_star }
| '%'                     { T_percent }
| '{'                     { T_lbrace !Lex_lib.num_line }
| '}'                     { T_rbrace !Lex_lib.num_line }
| '('                     { T_lparen }
| ')'                     { T_rparen }
| '['                     { T_lbrack }
| ']'                     { T_rbrack }
| eof                     { T_eof }
