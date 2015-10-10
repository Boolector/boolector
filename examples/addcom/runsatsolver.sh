#!/bin/sh
i=1
while [ $i -le $1 ]
do
  base=addcom`printf %04d $i`
  cnf=$base.cnf
  log=$base.log
  echo -n "$2 $cnf "
  /usr/bin/time -f %e --quiet $2 $cnf >$log
  i=`expr $i \* 2`
done
