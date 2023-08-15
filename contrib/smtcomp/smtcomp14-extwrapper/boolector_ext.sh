#!/bin/sh

# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

BOOLECTOR=./boolector
BOOLECTOREXT=./boolector-1.5.118

trap "exit 2" SIGHUP SIGINT SIGTERM

opts=""
benchmark=""

while [ $# -gt 0 ]
do
  case $1 in
    -*|[0-9]*) opts="$opts $1" ;;
	    *) benchmark="$1";;
  esac
  shift
done

out=`$BOOLECTOR $opts $benchmark`
ret=$?
if [ `echo $out | grep "extensionality" -c` -gt 0 ]; then 
  $BOOLECTOREXT $benchmark 
  ret=$?
else
  if [ $ret -eq 10 ]; then
    echo "sat"
  elif [ $ret -eq 20 ]; then
    echo "unsat"
  else
    echo "unknown"
  fi
fi
exit $ret

