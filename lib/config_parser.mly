%{
(** MemCAD analyzer
 **
 ** config_parser.mly
 ** configuration file parser
 ** Xavier Rival, 2011/09/29 *)
open Config_sig
%}

%token <int * char option> V_plot
%token <int>               V_int
%token <string>            V_qstring
%token <string>            V_string

%token T_equal T_comma T_sharp T_less T_more

%token T_eof

%type <Config_sig.pconfig_file> file
%type <Config_sig.entry>  entry
%type <Config_sig.fields> fields
%type <Config_sig.field>  field
%type <Config_sig.fvalue> fvalue
%type <string list>       stringlist

%start file
%%

file:
| T_eof
    { [ ] }
| entry file
    { $1 :: $2 }

extopt:
|                              { None }
| T_sharp T_less V_plot T_more { Some $3 }

entry:
| V_plot extopt fields
    { { ent_code   = $1;
        ent_extend = $2;
        ent_fields = $3 } }

fields:
|
    { [ ] }
| field fields
    { $1 :: $2 }

field:
| V_string T_equal fvalue
    { { fname = $1 ;
        fval  = $3 } }

fvalue:
| V_int
    { F_int $1 }
| stringlist
    { F_strings $1 }
| V_qstring
    { F_qstring $1 }

stringlist:
| V_string
    { [ $1 ] }
| V_string T_comma stringlist
    { $1 :: $3 }
