%{
(** MemCAD analyzer
 **
 ** ind_parser.mly
 ** inductive definitions parser
 ** Xavier Rival, 2011/05/22 *)
open Data_structures
open Graph_sig
open Ind_sig
open Sv_sig
open C_sig
open Apron
open Array_ind_sig

let make_map: 'a list -> 'a IntMap.t =
  let rec aux i acc l =
    match l with
    | [ ] -> acc
    | x :: y -> aux (i+1) (IntMap.add i x acc) y in
  aux 0 IntMap.empty
%}

%token <int>    V_int
%token <int>    V_size_contains
%token <string> V_string

%token <int>    V_par_int
%token <int>    V_par_ptr
%token <int>    V_par_set
%token <int>    V_par_maya
%token <int>    V_par_nmaya

%token <int>    V_new_var

%token T_at T_arrow T_contains T_defeq T_notequal
%token T_setmem T_setequal

%token T_lsub T_rsub T_semicolon T_setincluded
%token T_lt T_gt T_colon T_comma T_dot T_pipe T_le T_ge
%token T_lbrace T_rbrace T_lbrack T_rbrack T_lpar T_rpar
%token T_equal
%token T_and T_plus T_minus T_star T_epsilon T_union

%token T_eof

%token T_alloc
%token T_addr
%token T_emp
%token T_int
%token T_prec
%token T_raw
%token T_set
%token T_this
%token T_idx
%token T_subi
%token T_subp
%token T_true

%type <Ind_sig.p_iline list>        main_ilines
%type <Ind_sig.ind list>            main_indlist
%type <Ind_sig.ind>                 main_ind
%type <ind>                         inductive
%type <irule list>                  irules
%type <irule>                       irule
%type <int * ntyp list>             nvars
%type <ntyp list>                   opt_ntypes
%type <ntyp>                        ntype
%type <hform>                       fheap
%type <hform>                       theap
%type <cell>                        cell
%type <indcall>                     indcall
%type <formal_main_arg>             indpoint
%type <formal_int_args>             intargs
%type <pform>                       fpure
%type <pformatom>                   tpure
%type <Ind_sig.pformatom>           tpurealloc
%type <sform>                       tpureset
%type <aform>                       tpurearith
%type <aexpr>                       tarith
%type <aexpr>                       tarith0
%type <aexpr>                       tarith1
%type <sexpr>                       sterm
%type <formal_int_arg>              iatom
%type <Offs.t>                      field
%type <string list>                 string_list
%type <Array_ind_sig.array_ind list> array_indlist
%type <Array_ind_sig.array_ind>     array_ind

%start main_ilines main_indlist main_ind array_indlist array_ind
%%

main_ilines:
| T_eof
    { [ ] }
| inductive main_ilines
    { Piind $1 :: $2 }
| T_prec T_colon string_list T_dot main_ilines
    { Piprec $3 :: $5 }
| V_string T_colon V_string T_dot main_ilines
    { Pibind ($1, $3) :: $5 }

main_indlist:
| T_eof
    { [ ] }
| inductive main_indlist
    { $1 :: $2 }

array_indlist:
| T_eof
    { [ ] }
| array_inductive array_indlist
    { $1 :: $2 }

array_ind:
| array_inductive T_eof
    { $1 }

main_ind:
| inductive T_eof
    { $1 }

inductive:
| V_string T_lt V_int T_comma V_int T_gt T_defeq irules T_dot
    { { i_name    = $1 ;
        i_ppars   = $3 ;
        i_ipars   = $5 ;
        i_spars   = 0 ;
        i_rules   = $8;
        i_rules_cons = [];
        i_srules  = $8;
        i_mt_rule = false;
        i_emp_ipar = -1;
        i_reds0   = false;
        i_dirs    = Offs.OffSet.empty;
        i_may_self_dirs = Offs.OffSet.empty;
        i_pr_pars = IntSet.empty;
        i_fl_pars = IntMap.empty;
        i_pr_offs = Offs.OffSet.empty;
        i_list    = None;
        i_pkind   = Ind_utils.pars_rec_top;
	i_ppath   = [];
        i_pars_wktyp = { ptr_typ = IntMap.empty;
                         int_typ = IntMap.empty;
                         set_typ = IntMap.empty; };
        i_emp_pars_wktyp = { ptr_typ = IntMap.empty;
                             int_typ = IntMap.empty;
                             set_typ = IntMap.empty; } } }
| V_string T_lt V_int T_comma V_int T_comma V_int T_gt T_defeq irules T_dot
    { { i_name    = $1 ;
        i_ppars   = $3 ;
        i_ipars   = $5 ;
        i_spars   = $7 ;
        i_rules   = $10;
        i_rules_cons = [];
        i_srules  = $10;
        i_mt_rule = false;
        i_emp_ipar = -1;
        i_reds0   = false;
        i_dirs    = Offs.OffSet.empty;
        i_may_self_dirs = Offs.OffSet.empty;
        i_pr_pars = IntSet.empty;
        i_fl_pars = IntMap.empty;
        i_pr_offs = Offs.OffSet.empty;
        i_list    = None;
        i_pkind   = Ind_utils.pars_rec_top;
	i_ppath   = [];
	i_pars_wktyp = { ptr_typ = IntMap.empty;
                         int_typ = IntMap.empty;
                         set_typ = IntMap.empty; };
       i_emp_pars_wktyp = { ptr_typ = IntMap.empty;
                            int_typ = IntMap.empty;
                            set_typ = IntMap.empty; } } }

array_inductive:
| V_string T_lt V_int T_comma V_int T_gt submem woffset T_defeq airules T_dot
    { { ai_submem  = $7;
        ai_name    = $1;
        ai_ppars   = $3;
        ai_ipars   = $5;
        ai_mpars   = $8;
        ai_rules   = $10;
        ai_mt_rule = false;
        ai_emp_ipar = -1; } }
| V_string T_lt V_int T_comma V_int T_comma V_int T_gt submem woffset T_defeq airules T_dot
    { { ai_submem  = $9;
        ai_name    = $1 ;
        ai_ppars   = $3 ;
        ai_ipars   = $5 ;
        ai_mpars   = $10;
        ai_rules   = $12;
        ai_mt_rule = false;
        ai_emp_ipar = -1;} }

irules:
|
    { [ ] }
| irule irules
    { $1 :: $2 }

airules:
|
    { [ ] }
| airule airules
    { $1 :: $2 }

irule:
| T_pipe nvars T_minus fheap T_minus fpure
    { let n, t = $2 in { ir_num   = n;
                         ir_nnum  = IntSet.empty;
                         ir_snum  = IntSet.empty;
                         ir_typ   = make_map t;
                         ir_heap  = $4;
                         ir_pure  = $6;
                         ir_kind  = Ik_unk;
                         ir_uptr  = IntSet.empty;
                         ir_uint  = IntSet.empty;
                         ir_uset  = IntSet.empty;
                         ir_unone = false;
                         ir_cons = None } }

airule:
| T_pipe nvars T_minus fheap T_minus aifpure
    { let n, t = $2 in { air_num   = n;
                         air_typ   = make_map t;
                         air_heap  = $4;
                         air_pure  = $6;
                         air_kind  = Aik_unk;
                         air_unone = false; } }

| T_pipe nvars T_minus T_true T_minus aifpure
    {  { air_num   = 0;
         air_typ   = IntMap.empty;
         air_heap  = [ ];
         air_pure  = $6;
         air_kind  = Aik_true;
         air_unone = false; } }

nvars:
| T_lbrack V_int opt_ntypes T_rbrack
    { $2, $3 }

opt_ntypes:
|   { [ ] }
| ntype opt_ntypes
    { $1 :: $2 }

ntype:
| T_addr   { Ntaddr }
| T_int    { Ntint }
| T_raw    { Ntraw }
| T_set    { Ntset }

fheap:
| theap
    { $1 }
| theap T_star fheap
    { $1 @ $3 }

theap:
| T_emp
    { [ ] }
| cell
    { [ Hacell $1 ] }
| indcall
    { [ Haind $1 ] }

cell:
| T_this T_arrow field T_contains aatom
    { { ic_off  = $3;
        ic_size =  4;
        ic_dest = $5 } }
| T_this T_arrow field V_size_contains aatom
    { { ic_off  = $3;
        ic_size = $4;
        ic_dest = $5 } }

indcall:
| indpoint T_dot V_string T_lpar indargs T_rpar
    { let p, i, s = $5 in { ii_maina = $1;
                            ii_ind   = $3;
                            ii_argp  = p ;
                            ii_argi  = i ;
                            ii_args  = s } }

indpoint:
| T_this
    { `Fa_this }
| V_new_var
    { `Fa_var_new $1 }

indargs:
|
    { [ ], [ ], [ ] }
| ptrargs T_pipe intargs T_pipe setargs
    { $1, $3, $5 }

ptrargs:
|
    { [ ] }
| patom
    { [ $1 ] }
| patom T_comma ptrargs
    { $1 :: $3 }

intargs:
|
    { [ ] }
| iatom
    { [ $1 ] }
| iatom T_comma intargs
    { $1 :: $3 }

setargs:
|
    { [ ] }
| satom
    { [ $1 ] }
| satom T_comma setargs
    { $1 :: $3 }

submem:
| T_lsub T_subi T_colon V_int T_rsub
    { Some { acc_type = Access_by_offset;
             groups = $4;} }
| T_lsub T_subp T_colon V_int T_rsub
    { Some { acc_type = Access_by_pointer;
             groups = $4;} }

woffset:
|
  { [ ] }
| T_lpar offset T_rpar
    { $2 }

offset:
| V_int
    { $1::[] }
| T_idx
    { (-1)::[] }
| T_idx T_semicolon offset
    { (-1)::$3}
| V_int T_semicolon offset
    { $1::$3}

aifpure:
|
    { [ ] }
| aitpure
    { [ $1 ] }
| aitpure T_and aifpure
    { $1 :: $3 }

fpure:
|
    { [ ] }
| tpure
    { [ $1 ] }
| tpure T_and fpure
    { $1 :: $3 }

aitpure:
| tpure
   { Ai_Pf $1 }
| tpuremaya
    { Ai_Pf_maya $1 }

tpure:
| tpurealloc
    { $1 }
| tpurearith
    { Pf_arith $1 }
| tpureset
    { Pf_set $1 }
| tpurepath
    { Pf_path $1 }

tpuremaya:
| aatom T_setmem matom
    {Ai_Mf_mem ($1,$3)}
| matom T_setequal T_lbrace T_rbrace
    {Ai_Mf_empty $1}
| matom T_setequal matom
    {Ai_Mf_equal_s ($1,$3)}
| matom T_setincluded matom
    {Ai_Mf_included ($1,$3)}
| matom T_equal tarith
    {Ai_Mf_cons (Cbeq,$1,$3)}
| matom T_lt tarith
    {Ai_Mf_cons (Cblt,$1,$3)}
| matom T_gt tarith
    {Ai_Mf_cons (Cbgt,$1,$3)}
| matom T_le tarith
    {Ai_Mf_cons (Cble,$1,$3)}
| matom T_ge tarith
    {Ai_Mf_cons (Cbge,$1,$3)}
| T_pipe matom T_pipe T_equal V_int
    {Ai_Mf_cardinality ($2,$5)}

tpurealloc:
| T_alloc T_lpar T_this T_comma V_int T_rpar
    { Pf_alloc $5 }

tpureset:
| aatom T_setmem satom
    { Sf_mem ($1, $3) }
| satom T_setequal sterm
    { Sf_equal ($1, $3) }
| satom T_setequal T_lbrace T_rbrace
    { Sf_empty $1 }

tpurepath:
| T_lpar patom T_comma a_path T_comma patom T_rpar
   { ($2, $4, $6) }

a_path:
| T_epsilon
    { Pe_epsilon }
| T_lpar flds T_rpar T_star
    { Pe_seg $2 }
| flds
    { Pe_single $1 }

flds:
| V_int
    { [Offs.of_int $1] }
| V_int T_plus flds
    { (Offs.of_int $1)::$3 }

tpurearith:
| tarith T_equal tarith
    { Af_equal ($1, $3) }
| tarith T_notequal tarith
    { Af_noteq ($1, $3) }
| tarith T_gt tarith
    { Af_sup ($1, $3) }
| tarith T_ge tarith
    { Af_supeq ($1, $3) }
| tarith T_lt tarith
    { Af_sup ($3, $1) }
| tarith T_le tarith
    { Af_supeq ($3, $1) }
tarith:
| tarith0
    { $1 }

tarith0:
| tarith1
    { $1 }
| tarith0 T_plus tarith1
    { Ae_plus ($1, $3) }

tarith1:
| V_int
    { Ae_cst $1 }
| aatom
    { Ae_var $1 }

sterm:
| satom
    { Se_var $1 }
| satoms T_plus T_lbrace aatom T_rbrace
    { Se_uplus ($1, $4) }
| satoms T_union T_lbrace aatom T_rbrace
    { Se_union ($1, $4) }

satoms:
| satom
    { [$1] }
| satom T_comma satoms
    { $1 :: $3 }


patom:
| T_this
    { `Fa_this }
| V_new_var
    { `Fa_var_new $1 }
| V_par_ptr
    { `Fa_par_ptr $1 }

iatom:
| V_new_var
    { `Fa_var_new $1 }
| V_par_int
    { `Fa_par_int $1 }

satom:
| V_new_var
    { `Fa_var_new $1 }
| V_par_set
    { `Fa_par_set $1 }

aatom:
| T_this
    { `Fa_this }
| V_new_var
    { `Fa_var_new $1 }
| V_par_ptr
    { `Fa_par_ptr $1 }
| V_par_int
    { `Fa_par_int $1 }

matom:
| V_par_maya
    { Fa_par_maya $1 }
| V_par_nmaya
    { Fa_par_nmaya $1 }

field:
| V_string
    { Offs.of_string $1 }
| V_int
    { Offs.of_int $1 }

string_list:
| { [ ] }
| V_string string_list { $1 :: $2 }
