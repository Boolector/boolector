#!/bin/sh
i=1
while [ $i -le 128 ]
do
  n=`printf '%03d' $i`
  smt=mulcom$n.smt
  aig=mulcom$n.aig
  cnf=mulcom$n.cnf
  sed -e "s,@,$i," mulcom.tmp > $smt
  boolector -rwl 2 --no-sort-exp --no-sort-aigvec -dai -o $aig $smt
  aigtocnf $aig $cnf
  i=`expr $i + 1`
done
