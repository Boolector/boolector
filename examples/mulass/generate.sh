#!/bin/sh
i=1
while [ $i -le 16 ]
do
  n=`printf '%03d' $i`
  smt=mulass$n.smt
  aig=mulass$n.aig
  cnf=mulass$n.cnf
  sed -e "s,@,$i," mulass.tmp > $smt
  boolector -rwl 2 -dai -o $aig $smt
  aigtocnf $aig $cnf
  i=`expr $i + 1`
done
