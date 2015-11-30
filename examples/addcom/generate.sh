#!/bin/sh
i=1
while [ $i -le 8192 ]
do
  n=`printf '%04d' $i`
  smt=addcom$n.smt
  aig=addcom$n.aig
  cnf=addcom$n.cnf
  sed -e "s,@,$i," addcom.tmp > $smt
  boolector -rwl 2 --no-sort-exp --no-sort-aig --no-sort-aigvec -dai -o $aig $smt
  aigtocnf $aig $cnf
  i=`expr $i \* 2`
done
