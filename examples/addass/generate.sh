#!/bin/sh
i=1
while [ $i -le 8192 ]
do
  n=`printf '%04d' $i`
  smt=addass$n.smt
  aig=addass$n.aig
  cnf=addass$n.cnf
  sed -e "s,@,$i," addass.tmp > $smt
  boolector -rwl 2 -dai -o $aig $smt
  aigtocnf $aig $cnf
  i=`expr $i \* 2`
done
