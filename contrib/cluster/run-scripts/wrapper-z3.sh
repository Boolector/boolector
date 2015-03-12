#! /bin/sh

z3=$HOME/src/z3/build/z3

out=`$z3 $*`
retval=$?

echo $out
if [ "$out" = "unsat" ]; then
  exit 20
elif [ "$out" = "sat" ]; then
  exit 10
else
  exit $retval 
fi
