#!/bin/bash

# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

die () 
{
  echo "*** $(basename $0): $*" 1>&2
  exit 1
}

trap "exit 2" SIGHUP SIGINT SIGTERM

INFILE=""
MODEL=""
TMPFILE=/tmp/btorcheckmodelsmt2-$$.smt2

while [ $# -gt 0 ]
do
  case $1 in
    -h|--help)
      echo -n "usage: $(basename $0) [<option>] <infile> <model> <boolector-binary>"
      echo
      echo "  options:"
      echo "    -h, --help    print this message and exit"
      echo
      exit
      ;;
    -*|[0-9]*) 
      die "invalid option: $1"
      ;;
    *) 
      if [ x"$INFILE" = x ]; then
        INFILE=$1
      else
        break
      fi
  esac
  shift
done

MODEL="$1"
BOOLECTOR="$2"

[ -z "$BOOLECTOR" ] && die "no Boolector binary specified"
[ ! -e "$BOOLECTOR" ] && die "given Boolector binary does not exist"

cat $INFILE | sed 's/\(check-sat\)|\(exit\)//' >> $TMPFILE
cat $MODEL | sed 's/sat//' >> $TMPFILE
echo "(check-sat)" >> $TMPFILE
echo "(exit)" >> $TMPFILE
"${BOOLECTOR}" ${TMPFILE}
ret=$?
if [[ $ret = 10 ]]; then
  exit 0
fi
exit 1
