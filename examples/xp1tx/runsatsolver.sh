#!/bin/sh
i=1
while [ $i -le $1 ]
do
  base=xp1tx`printf %03d $i`
  cnf=$base.cnf
  log=$base.log
  echo -n "$2 $cnf "
  /usr/bin/time -f %e --quiet $2 $cnf >$log
  i=`expr $i + 1`
done
