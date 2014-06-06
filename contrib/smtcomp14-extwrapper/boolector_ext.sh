#!/bin/sh
BENCHMARK=$1
BOOLECTOR=./boolector
BOOLECTOREXT=./boolector-1.5.118

out=`$BOOLECTOR $BENCHMARK`
ret=$?
if [ `echo $out | grep "extensionality on arrays/lambdas not yet supported" -c` -gt 0 ]; then 
  $BOOLECTOREXT $BENCHMARK 
  echo "asdf"
else
  if [ $ret -eq 10 ]; then
    echo "sat"
  elif [ $ret -eq 20 ]; then
    echo "unsat"
  else
    echo "unknown"
  fi
  exit $ret
fi

