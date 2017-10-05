#-------------------------------------------------------------------#
# makefile for a domain library version                             #
#-------------------------------------------------------------------#
# For wc
ML_ML=          bin/increase_arity.ml \
		c/c_parser.mly \
		c/c_lexer.mll \
		c/mc_parser.mly \
		c/mc_lexer.mll \
		main/domsel_parser.mly \
		main/domsel_lexer.mll \
		sd/ind_lexer.mll \
		sd/ind_parser.mly \
		c/c_analysis_sig.ml \
		c/c_analyze.ml \
		c/c_ind_infer.ml \
		c/c_ind_infer.mli \
		c/c_pre_analyze.ml \
		c/c_pre_analyze.mli \
		c/c_process.ml \
		c/c_process.mli \
		c/c_sig.ml \
		c/c_utils.ml \
		c/c_utils.mli \
		c/dom_c.ml \
		lib/aa_maps.ml \
		lib/aa_maps.mli \
		lib/aa_sets.ml \
		lib/aa_sets.mli \
		lib/bi_fun.ml \
		lib/bi_fun.mli \
		lib/config_lexer.mll \
		lib/config_parser.mly \
		lib/config_sig.ml \
		lib/data_structures.ml \
		lib/flags.ml \
		lib/flags.mli \
		lib/graph.ml \
		lib/keygen.ml \
		lib/keygen.mli \
		lib/latex_utils.ml \
		lib/latex_utils.mli \
		lib/lex_lib.ml \
		lib/lex_lib.mli \
		lib/lib.ml \
		lib/lib.mli \
		lib/printable_graph.ml \
		lib/refcount.ml \
		lib/refcount.mli \
		lib/regular_expr.ml \
		lib/regular_expr.mli \
		lib/timer.ml \
		lib/timer.mli \
		lib/union_find.ml \
		lib/union_find.mli \
		main/batch.ml \
		main/main.ml \
		main/rt_sig.ml \
		main/transform.ml \
		nd/dom_no_set.ml \
		nd/dom_set.ml \
		nd/nd_add_bottom.ml \
		nd/nd_add_diseqs.ml \
		nd/nd_add_dyn_svenv.ml \
		nd/nd_apron.ml \
		nd/nd_sig.ml \
		nd/nd_utils.ml \
		nd/nd_utils.mli \
		nd/quicr_dump.ml \
		nd/quicr_lin.ml \
		nd/set_bdd.ml \
		nd/set_bdd.mli \
		nd/set_dump.ml \
		nd/set_lin.ml \
		nd/set_quicr.ml \
		nd/set_sig.ml \
		nd/set_utils.ml \
		nd/set_utils.mli \
		nd/sv_sig.ml \
		sd/array_ind_sig.ml \
		sd/array_ind_utils.ml \
		sd/array_node.ml \
		sd/array_ppred_sig.ml \
		sd/array_ppred_utils.ml \
		sd/ast_sig.ml \
		sd/ast_utils.ml \
		sd/ast_utils.mli \
		sd/block_frag.ml \
		sd/block_frag.mli \
		sd/bound_set.ml \
		sd/bound_set.mli \
		sd/bound_sig.ml \
		sd/bounds.ml \
		sd/bounds.mli \
		sd/constrain_ops.ml \
		sd/constrain_ops.mli \
		sd/constrain_rules.ml \
		sd/constrain_rules.mli \
		sd/constrain_sig.ml \
		sd/constrain_utils.ml \
		sd/constrain_utils.mli \
		sd/disj_sig.ml \
		sd/disj_utils.ml \
		sd/disj_utils.mli \
		sd/dom_dictionary.ml \
		sd/dom_disj.ml \
		sd/dom_env.ml \
		sd/dom_eqs.ml \
		sd/dom_eqs.mli \
		sd/dom_mem_exprs.ml \
		sd/dom_mem_low_flat.ml \
		sd/dom_mem_low_list.ml \
		sd/dom_mem_low_prod.ml \
		sd/dom_mem_low_sep.ml \
		sd/dom_mem_low_shape.ml \
		sd/dom_no_disj.ml \
		sd/dom_sig.ml \
		sd/dom_subm_graph.ml \
		sd/dom_subm_sig.ml \
		sd/dom_timing.ml \
		sd/dom_utils.ml \
		sd/dom_utils.mli \
		sd/dom_val_array.ml \
		sd/dom_val_maya.ml \
		sd/dom_val_npack.ml \
		sd/dom_val_record.ml \
		sd/dom_val_num.ml \
		sd/dom_val_subm.ml \
		sd/gen_dom.ml \
		sd/gen_is_le.ml \
		sd/gen_is_le.mli \
		sd/gen_join.ml \
		sd/gen_join.mli \
		sd/graph_abs.ml \
		sd/graph_abs.mli \
		sd/graph_algos.ml \
		sd/graph_algos.mli \
		sd/graph_dir_weak.ml \
		sd/graph_dir_weak.mli \
		sd/graph_encode.ml \
		sd/graph_is_le.ml \
		sd/graph_is_le.mli \
		sd/graph_join.ml \
		sd/graph_join.mli \
		sd/graph_materialize.ml \
		sd/graph_materialize.mli \
		sd/graph_sig.ml \
		sd/graph_strategies.ml \
		sd/graph_strategies.mli \
		sd/graph_utils.ml \
		sd/graph_utils.mli \
		sd/graph_visu.ml \
		sd/graph_visu.mli \
		sd/graph_visu_atom.ml \
		sd/graph_visu_common.ml \
		sd/graph_visu_common.mli \
		sd/graph_visu_sig.ml \
		sd/ind_analysis.ml \
		sd/ind_analysis.mli \
		sd/ind_sig.ml \
		sd/ind_utils.ml \
		sd/ind_utils.mli \
		sd/inst_sig.ml \
		sd/inst_utils.ml \
		sd/inst_utils.mli \
		sd/list_abs.ml \
		sd/list_abs.mli \
		sd/list_inst.ml \
		sd/list_inst.mli \
		sd/list_is_le.ml \
		sd/list_is_le.mli \
		sd/list_join.ml \
		sd/list_join.mli \
		sd/list_mat.ml \
		sd/list_mat.mli \
		sd/list_sig.ml \
		sd/list_utils.ml \
		sd/list_utils.mli \
		sd/list_visu.ml \
		sd/list_visu.mli \
		sd/off_impl.ml \
		sd/off_impl.mli \
		sd/off_linexpr.ml \
		sd/off_linexpr.mli \
		sd/off_sig.ml \
		sd/offs.ml \
		sd/offs.mli \
		sd/statistics.ml \
		sd/statistics.mli \
		sd/svenv_sig.ml

#-------------------------------------------------------------------#
# Main targets					                    #
#-------------------------------------------------------------------#
all: analyze batch

config: memcad.obuild
	obuild configure
	touch config && rm -f dconfig

dconfig:
	obuild configure --enable-executable-bytecode --enable-executable-debugging
	touch dconfig && rm -f config
# Normal mode; native code
analyze: config
	obuild build exe-analyze
batch: config
	obuild build exe-batch
# In debug mode
danalyze: dconfig
	obuild build exe-analyze
	ln -sf analyze.byte danalyze
dbatch: dconfig
	obuild build exe-batch
	ln -sf batch.byte dbatch

#-------------------------------------------------------------------#
# Testing targets                                                   #
#-------------------------------------------------------------------#
.PHONY: rt analyze
# (p|)(rt|ex)(p|)
# - p: pure
# - rt: regression tests   (already   validated)
#   ex: experimental tests (still not validated)
# - p: perf mode (disable all pretty-printing)
broken: analyze batch
	./batch -in-file rt.txt -pure-cat broken
hack: analyze batch
	./batch -in-file rt.txt -pure-cat hack
todobdd: analyze batch
	./batch -in-file rt.txt -pure-cat todobdd
sas: analyze batch
	./batch -in-file rt.txt -pure-cat sas
sastest: analyze batch
	./batch -in-file rt.txt -pure-cat sastest
rt: analyze batch
	./batch -in-file rt.txt -all-test
rtp: analyze batch
	./batch -in-file rt.txt -all-test -very-silent
prt: analyze batch
	./batch -in-file rt.txt -pure-regtest
prtst: analyze batch
	./batch -in-file rt.txt -pure-regtest -very-silent -stress-test 100
prtp: analyze batch
	./batch -in-file rt.txt -pure-regtest -very-silent
# Other targets
bigrt: analyze batch # regression tests that take significant time
	./batch -in-file bigrt.txt -very-silent -pure-cat bigrt
selwiden: analyze batch # regression tests that take significant time
	./batch -in-file bigrt.txt -pure-cat selwiden
popl17: analyze batch # regression tests that take significant time
	./batch -in-file bigrt.txt -pure-cat popl17
poplm17: analyze batch # regression tests that take significant time
	./batch -in-file bigrt.txt -pure-cat poplm17
prtpnt: analyze batch
	./batch -in-file rt.txt -pure-regtest -very-silent -no-timing
pex: analyze batch
	./batch -in-file rt.txt -pure-expe
pexp: analyze batch
	./batch -in-file rt.txt -pure-expe -very-silent
tvl: analyze batch
	./batch -in-file rt.txt -pure-cat tvl
# test for array domain
pcva: analyze batch
	./batch -in-file rt.txt -pure-cat validarray
pcea: analyze batch
	./batch -in-file rt.txt -pure-cat arraypred
pcas: analyze batch
	./batch -in-file rt.txt -pure-cat arrayshape
# unit tests for join_paths
jptest: analyze
	qtest -o sd/jptest.ml extract sd/graph_encode.ml
	obuild build exe-jptest
	./jptest
	echo "(* DO NOT EDIT THIS FILE *)" > sd/jptest.ml

# Temporary:
rtl: analyze batch
	./batch -pure-cat explist
# debug (deprecated)
vmcai13: analyze batch bench/vmcai-ex-00.c
	./batch 5002a 5002c 5002d
# set tests already validated
sprtp: analyze batch
	./batch -in-file rt.txt -pure-cat validset -very-silent
spex: analyze batch
	./batch -in-file rt.txt -pure-cat expset
#-------------------------------------------------------------------#
# Auxilliary stuffs						    #
#-------------------------------------------------------------------#
.PHONY: edit wedit wc clean pull tags
edit:
	emacs --background-color=Black --foreground-color=White &
wedit:
	emacs --background-color=White --foreground-color=Black makefile &
wc:
	wc $(ML_ML)
gclean: # graphs cleaning
	rm -f *.dot *.pdf *.c-*N*-D*.txt
clean:
	obuild clean
	rm -rf */*.o */*.cmo */*.cmi */*.cmx */*.cma */*.cmxa */*.cmo \
	  */*.cmi */*.cmt */*.annot */*~ */*.output depend config dconfig \
	  *.pdf *.dot bench/log-*.tex bench/*/*.log bench/*/*/*.log \
	  bench/*/*/*/*.log bench/*/*/*/*/*.log dbatch danalyze log.log \
	  c/c_lexer.ml c/c_parser.ml c/c_parser.mli c/mc_parser.mli \
	  lib/config_lexer.ml lib/config_parser.ml lib/config_parser.mli \
	  main/domsel_lexer.ml main/domsel_parser.ml main/domsel_parser.mli \
	  sd/ind_lexer.ml sd/ind_lexer.mli sd/ind_parser.ml sd/ind_parser.mli
exclean:
	rm -rf bench/*.log bench/*/*log

#-------------------------------------------------------------------#
# GIT            						    #
#-------------------------------------------------------------------#
lpull:
	git pull ../../pull/memcad
mpull:
	git pull rival@mezcal.ens.fr:git/memcad.git master
mpush:
	git push rival@mezcal.ens.fr:git/memcad.git master
bpull:
	git pull /import/absint3/rival/git/memcad.git master
bpush:
	git push /import/absint3/rival/git/memcad.git master
