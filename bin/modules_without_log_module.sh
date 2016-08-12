#!/bin/bash

# find modules using the logger without having defined a section

users=`mktemp`
allowed_users=`mktemp`
grep -l 'Log\.' */*.ml | grep -v bin/increase_arity.ml | sort -u > $users
grep -l 'Logger\.' */*.ml | sort -u > $allowed_users
echo 'CULPRITS:'
comm -2 -3 $users $allowed_users
\rm -f $users $allowed_users
