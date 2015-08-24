#!/bin/sh
grep BTOR_FORMAT_TAG_ btorfmt.h | \
sed -e 's,.*TAG_,,' -e 's/,.*$//g' | \
sort > /tmp/btorfmt-run-coverage-tags-in-header
grep 'PARSE (' btorfmt.c | \
sed -e 's,.*PARSE (,,' -e 's/,.*//g' | \
sort > /tmp/btorfmt-run-coverage-tags-in-parsed
diff \
  /tmp/btorfmt-run-coverage-tags-in-header \
  /tmp/btorfmt-run-coverage-tags-in-parsed | sed -e '/^[0-9]/d'
make clean && ./configure.sh -g -c && make && ./runtests.sh && gcov btorfmt.c
echo "vi btorfmt.c.gcov"
