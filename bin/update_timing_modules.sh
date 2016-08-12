#!/bin/bash

# hackish way to try updating timing modules
# this should be launched and the resulting modifications
# be committed before any benchmarking experiments campaign
# date: May 17th 2016
# author: francois.berenger@inria.fr

FILES_TO_PROCESS=`egrep -rl ' T\.app[0-9]+ ' * | grep -v bin | grep -v dist | egrep '\.ml$'`

grep ' T\.app10 ' $FILES_TO_PROCESS && \
    echo "FATAL: some files use T.app10; we cannot increase that" && \
    exit 1

for f in $FILES_TO_PROCESS ; do
    # list candidate lines along with their line number
    awk '/ T\.app[0-9]+ /{print(NR" "$0)}' $f > lines_to_update
    # for each line; keep incrementing the arity as long as the
    # whole project compiles
    ./increase_arity $f lines_to_update
done
