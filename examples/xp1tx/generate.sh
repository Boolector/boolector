#!/bin/sh
i=2
while [ $i -le 32 ]
do
  n=`printf '%03d' $i`
  smt=xp1tx$n.smt
  aig=xp1tx$n.aig
  cnf=xp1tx$n.cnf
  sed -e "s,@,$i," xp1tx.tmp > $smt
  boolector -rwl 2 -dai -o $aig $smt
  aigtocnf $aig $cnf
  i=`expr $i \+ 2`
done
