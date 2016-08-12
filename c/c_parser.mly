%{
(** MemCAD analyzer
 **
 ** c_parser.mly
 ** a rotten C frontend
 ** Xavier Rival, 2011/07/09 *)
open C_sig
open C_utils
type stroruni = SU_struct | SU_union
let add_fake_offsets l = List.map (fun (a, b) -> a, -1, b) l
%}

%token T_eof

%token T_comma
%token T_ge T_gt T_le T_lt
%token T_amp T_ampamp T_arrow T_bangeq T_dot
%token T_eq T_eqeq T_minus T_pipe T_pipepipe
%token T_plus T_star T_percent
%token T_lparen T_rparen
%token T_lbrack T_rbrack

%token <int>    T_lbrace
%token <int>    T_rbrace
%token <int>    T_semicolon

%token <int>    V_int
%token <string> V_qstring
%token <string> V_string

%token <int>    T__memcad
%token <int>    T_assert
%token <int>    T_free
%token <int>    T_malloc
%token <int>    T_null

%token <int>    T_auto
%token <int>    T_break
%token <int>    T_char
%token <int>    T_else
%token <int>    T_float
%token <int>    T_if
%token <int>    T_int
%token <int>    T_return
%token <int>    T_short
%token <int>    T_sizeof
%token <int>    T_struct
%token <int>    T_typedef
%token <int>    T_union
%token <int>    T_unsigned
%token <int>    T_void
%token <int>    T_volatile
%token <int>    T_while

%type <string>                 identifier
%type <string option>          identifier_opt
%type <c_const>                constant
/* A.2.1 Expressions */
%type <c_expr>                 primary_expression
%type <c_expr>                 postfix_expression
%type <c_expr list>            argument_expression_list_opt
%type <c_expr list>            argument_expression_list
%type <c_expr>                 unary_expression
%type <c_expr -> c_expr>       unary_operator
%type <c_expr>                 cast_expression
%type <c_expr>                 multiplicative_expression
%type <c_expr>                 additive_expression
%type <c_expr>                 shift_expression
%type <c_expr>                 shift_expression
%type <c_expr>                 equality_expression
%type <c_expr>                 equality_expression
%type <c_expr>                 and_expression
%type <c_expr>                 exclusive_or_expression
%type <c_expr>                 inclusive_or_expression
%type <c_expr>                 logical_and_expression
%type <c_expr>                 logical_or_expression
%type <c_expr>                 conditional_expression
%type <c_expr>                 assignment_expression
%type <c_expr>                 expression

/* A.2.2 Declarations */
%type <parsed_declaration>            declaration

%type <parsed_init_declarator>        init_declarator

%type <c_type>                        type_specifier

%type <c_type>                        struct_or_union_specifier
%type <stroruni>                      struct_or_union
%type <c_agg_field list>              struct_declaration_list
%type <c_agg_field>                   struct_declaration
%type <string>                        struct_declarator_list
%type <string>                        struct_declarator

%type <string * c_var list option>    declarator
%type <string * c_var list option>    direct_declarator
/* %type <bool>   pointer_opt */
%type <c_var list>                    parameter_type_list
%type <c_var list>                    parameter_list
%type <c_var>                         parameter_declaration

%type <string>             typedef_name

/* A.2.3 Statements */
%type <c_stat>             statement
%type <c_stat>             compound_statement
%type <c_stat>             assignment_statement
%type <c_stat>             call_statement
%type <c_stat list>        block_item_list
%type <c_stat>             block_item
%type <c_stat>             selection_statement
%type <c_stat>             iteration_statement
%type <c_stat>             jump_statement
%type <c_stat>             memory_statement
%type <c_stat>             assert_statement
%type <c_stat>             memcad_statement

/* A.2.4 External definitions */

%type <C_sig.c_prog> entry
%type <C_sig.c_prog> translation_unit
%type <c_prog -> c_prog> external_declaration
%type <parsed_fun> function_definition
%type <c_var list> declaration_list_opt
%type <c_var list> declaration_list
%start entry
%%

identifier:
| V_string
    { $1 }
identifier_opt:
|   { None }
| identifier { Some $1 }

/* A.1.5 Constants */
/* -> does not follow the norm */

constant:
| V_int
    { Ccint $1 }
| T_null
    { Ccnull }


/* A.2.1 Expressions */

primary_expression:
| identifier
    { mkve (Celval (mkvl (Clvar (C_utils.make_c_var $1 Ctvoid)))) }
| constant
    { mkve (Ceconst $1) }
| T_lparen expression T_rparen
    { $2 }
postfix_expression:
| primary_expression
    { $1 }
| postfix_expression T_lbrack expression T_rbrack
    { mkve (Celval (mkvl (Clindex (unbox_clval_in_cexpr $1, $3)))) }
| postfix_expression T_arrow identifier
    { mkve (Celval (mkvl (Clfield (mkvl (Clderef $1), $3)))) }
| postfix_expression T_dot identifier
    { mkve (Celval (mkvl (Clfield (unbox_clval_in_cexpr $1, $3)))) }
argument_expression_list_opt:
|   { [ ] }
| argument_expression_list
    { $1 }
argument_expression_list:
| assignment_expression
    { [ $1 ] }
| argument_expression_list T_comma assignment_expression
    { $1 @ [ $3 ] }
unary_expression:
| postfix_expression
    { $1 }
| unary_operator cast_expression
    { $1 $2 }
unary_operator:
| T_amp   { fun e -> mkve (Ceaddrof (unbox_clval_in_cexpr e)) }
| T_star  { fun e -> mkve (Celval (mkvl (Clderef e))) }
| T_minus { fun e -> mkve (Ceuni (Cuneg, e)) }
cast_expression:
| unary_expression
    { $1 }
multiplicative_expression:
| cast_expression
    { $1 }
| multiplicative_expression T_star cast_expression
    { mkve (Cebin (Cbmul, $1, $3)) }
| multiplicative_expression T_percent cast_expression
    { mkve (Cebin (Cbmod, $1, $3)) }
/*
  Problem, ambiguity in the grammar!!!
*/
additive_expression:
| multiplicative_expression
    { $1 }
| additive_expression T_plus multiplicative_expression
    { mkve (Cebin (Cbadd, $1, $3)) }
| additive_expression T_minus multiplicative_expression
    { mkve (Cebin (Cbsub, $1, $3)) }
shift_expression:
| additive_expression
    { $1 }
relational_expression:
| shift_expression
    { $1 }
| relational_expression T_ge shift_expression
    { mkve (Cebin (Cbge, $1, $3)) }
| relational_expression T_gt shift_expression
    { mkve (Cebin (Cbgt, $1, $3)) }
| relational_expression T_le shift_expression
    { mkve (Cebin (Cble, $1, $3)) }
| relational_expression T_lt shift_expression
    { mkve (Cebin (Cblt, $1, $3)) }
equality_expression:
| relational_expression
    { $1 }
| equality_expression T_eqeq relational_expression
    { mkve (Cebin (Cbeq, $1, $3)) }
| equality_expression T_bangeq relational_expression
    { mkve (Cebin (Cbne, $1, $3)) }
and_expression:
| equality_expression
    { $1 }
exclusive_or_expression:
| and_expression
    { $1 }
inclusive_or_expression:
| exclusive_or_expression
    { $1 }
logical_and_expression:
| inclusive_or_expression
    { $1 }
| logical_and_expression T_ampamp inclusive_or_expression
    { mkve (Cebin (Cbland, $1, $3)) }
logical_or_expression:
| logical_and_expression
    { $1 }
| logical_or_expression T_pipepipe logical_and_expression
    { mkve (Cebin (Cblor, $1, $3)) }
conditional_expression:
| logical_or_expression
    { $1 }
assignment_expression:
| conditional_expression
    { $1 }
/*
| unary_expression assignment_operator assignment_expression
    { mkve (Ceassign (unbox_clval_in_cexpr $1, $3)) }
*/
assignment_operator:
| T_eq
    { ( ) }
expression:
| assignment_expression
    { $1 }
/* | expression T_comma assignment_expression */
/*    { mkve (Cecomma ($1, $3)) } */


/* A.2.2 Declarations */
/* huge differences with the C grammar in this section */
/* (Declarations have a very nasty syntax as per the C */
/* grammar)                                            */

declaration:
| type_specifier /*pointer_opt*/ init_declarator T_semicolon
    { assert (snd $2 = None);
      let t = $1 in
      Pcd_var (make_c_var (fst $2) t, $3) }
| T_volatile type_specifier /*pointer_opt*/ init_declarator T_semicolon
    { assert (snd $3 = None);
      let t = $2 in
      Pcd_var ({ (make_c_var (fst $3) t) with
                 cv_volatile = true }, $4) }
| type_specifier T_star init_declarator T_semicolon
    { assert (snd $3 = None);
      let t = Ctptr (Some $1) in
      Pcd_var (make_c_var (fst $3) t, $4) }
| T_typedef struct_or_union_specifier identifier T_semicolon
    { Pcd_type ($3, $2) }
| type_specifier identifier T_lbrack V_int T_rbrack T_semicolon
    { Pcd_var ({ cv_name     = $2;
                 cv_uid      = -1;
                 cv_type     = Ctarray ($1, Some $4);
                 cv_volatile = false; }, $6) }
| type_specifier identifier T_lbrack T_rbrack T_semicolon
    { Pcd_var ({ cv_name     = $2;
                 cv_uid      = -1;
                 cv_type     = Ctarray ($1, None);
                 cv_volatile = false; }, $5) }
| T_typedef type_specifier T_star identifier T_semicolon
    { Pcd_type ($4, Ctptr (Some $2)) }

init_declarator:
| declarator
    { $1 }
type_specifier:
| T_char { Ctchar }
| T_int  { Ctint }
| T_void { Ctvoid }
| struct_or_union_specifier
    { $1 }
| typedef_name
    { Ctnamed { cnt_name = $1 ;
                cnt_type = Ctvoid } }
struct_or_union_specifier:
| struct_or_union identifier_opt T_lbrace struct_declaration_list T_rbrace
    { match $1 with
    | SU_struct -> Ctstruct (Cad_def { cag_name   = $2 ;
                                       cag_align  = -1 ;
                                       cag_size   = -1 ;
                                       cag_fields = $4 })
    | SU_union  -> Ctunion  (Cad_def { cag_name   = $2 ;
                                       cag_align  = -1 ;
                                       cag_size   = -1 ;
                                       cag_fields = $4 }) }
| struct_or_union identifier
    { match $1 with
    | SU_struct -> Ctstruct (Cad_named $2)
    | SU_union  -> Ctunion  (Cad_named $2) }
struct_or_union:
| T_struct { SU_struct }
| T_union  { SU_union  }
struct_declaration_list:
| struct_declaration
    { [ $1 ] }
| struct_declaration_list struct_declaration
    { $1 @ [ $2 ] }
struct_declaration:
| type_specifier struct_declarator_list T_semicolon
    { { caf_typ  = $1;
        caf_off  = -1;
        caf_size = -1;
        caf_name = $2 } }
| type_specifier T_star struct_declarator_list T_semicolon
    { { caf_typ  = Ctptr (Some $1);
        caf_off  = -1;
        caf_size = -1;
        caf_name = $3 } }
| type_specifier struct_declarator_list T_lbrack V_int T_rbrack T_semicolon
    { { caf_typ  = Ctarray ($1, Some $4);
        caf_off  = -1;
        caf_size = -1;
        caf_name = $2 } }
| type_specifier struct_declarator_list T_lbrack T_rbrack T_semicolon
    { { caf_typ  = Ctarray ($1, None);
        caf_off  = -1;
        caf_size = -1;
        caf_name = $2 } }
struct_declarator_list:
| struct_declarator
    { $1 }
/*
| struct_declarator_list T_comma struct_declarator
    { ( ) }
*/
struct_declarator:
| identifier
    { $1 }
/*
| declarator
    { ( ) }
*/

declarator:
| direct_declarator
    { $1 }

direct_declarator:
| identifier
    { $1, None }
| direct_declarator T_lparen parameter_type_list T_rparen
    {
     match $1 with
     | x, None -> x, Some $3
     | _ -> failwith "direct_declarator(parameter_type_list)" }
/*
pointer_opt:
|            { false }
| T_star     { true }
*/

parameter_type_list:
|   { [ ] }
| parameter_list
    { $1 }
parameter_list:
| parameter_declaration
    { [ $1 ] }
| parameter_list T_comma parameter_declaration
    { $1 @ [ $3 ] }
parameter_declaration:
| type_specifier identifier { make_c_var $2 $1 }
| type_specifier T_star identifier { make_c_var $3 (Ctptr (Some $1)) }
/*
| declaration_specifiers declarator
    { failwith "declaration_specifiers declarator" }
*/

typedef_name:
| identifier
    { $1 }


/* A.2.3 Statements */

statement:
| compound_statement
    { $1 }
| assignment_statement
    { $1 }
| call_statement
    { $1 }
| selection_statement
    { $1 }
| iteration_statement
    { $1 }
| jump_statement
    { $1 }
| memory_statement
    { $1 }
| assert_statement
    { $1 }
| memcad_statement
    { $1 }
compound_statement:
| T_lbrace block_item_list T_rbrace
    { { csk = Csblock $2 ;
        csl = $1 } }
assignment_statement:
| unary_expression assignment_operator assignment_expression T_semicolon
    { { csk = Csassign (unbox_clval_in_cexpr $1, $3) ;
        csl = $4 } }
call_statement:
| postfix_expression T_lparen argument_expression_list_opt T_rparen T_semicolon
    { let s = Cspcall { cc_fun  = $1 ;
                        cc_args = $3 } in { csk = s ; csl = $5 } }
| unary_expression assignment_operator postfix_expression
    T_lparen argument_expression_list_opt T_rparen T_semicolon
    { let s = Csfcall (unbox_clval_in_cexpr $1,
                       { cc_fun  = $3 ;
                         cc_args = $5 }) in { csk = s ; csl = $7 } }
block_item_list:
|   { [ ] }
| block_item_list block_item
    { (* match $2 with None -> $1 | Some s -> *) $1 @ [ $2 ] }
block_item:
| declaration
    { unbox_cstat_in_declaration $1 }
| statement
    { $1 }
selection_statement:
| T_if T_lparen expression T_rparen statement
    { { csk = Csif ($3, [ $5 ], [ ]) ;
        csl = $1 } }
| T_if T_lparen expression T_rparen statement T_else statement
    { { csk = Csif ($3, [ $5 ], [ $7 ]) ;
        csl = $1 } }
iteration_statement:
| T_while T_lparen expression T_rparen statement
    { { csk = Cswhile ($3, [ $5 ], None) ;
        csl = $1 } }
jump_statement:
| T_return T_semicolon
    { { csk = Csreturn None ;
        csl = $1 } }
| T_return expression T_semicolon
    { { csk = Csreturn (Some $2) ;
        csl = $1 } }
| T_break T_semicolon
    { { csk = Csbreak ;
        csl = $1 } }
memory_statement:
| unary_expression assignment_operator T_malloc
    T_lparen assignment_expression T_rparen T_semicolon
    { let s = Csalloc (unbox_clval_in_cexpr $1, $5) in { csk = s ; csl = $7 } }
| T_free T_lparen assignment_expression T_rparen T_semicolon
    { { csk = Csfree (unbox_clval_in_cexpr $3) ;
        csl = $5 } }
assert_statement:
| T_assert T_lparen assignment_expression T_rparen T_semicolon
    { { csk = Csassert $3 ;
        csl = $5 } }
memcad_statement:
| T__memcad T_lparen V_qstring T_rparen T_semicolon
    { { csk = Cs_memcad (Mc_comstring $3) ;
        csl = $1 } }


/* A.2.4 External definitions */

entry:
| translation_unit T_eof
    { $1 }
translation_unit:
|
    { empty_unit }
| translation_unit external_declaration
    { $2 $1 }
external_declaration:
| function_definition
    { add_fundef $1 }
| declaration
    { add_typedef $1 }
function_definition:
/*
| declaration_specifiers declarator declaration_list_opt compound_statement
    { ( ) }
*/
| type_specifier declarator declaration_list_opt compound_statement
    { assert ($3 = [ ]);
      let n, opars = $2 in
      let pars = match opars with None -> assert false | Some x -> x in
      ($1, n, pars, unbox_cstat_block $4) }

declaration_list_opt:
|
    { [ ] }
| declaration_list
    { $1 }
declaration_list:
| declaration
    { [ unbox_c_var_in_declaration $1 ] }
| declaration_list declaration
    { $1 @ [ unbox_c_var_in_declaration $2 ] }

