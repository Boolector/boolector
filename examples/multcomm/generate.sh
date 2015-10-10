#!/bin/sh
i=1
while [ $i -le 128 ]
do
  n=`printf '%03d' $i`
  smt=multcomm$n.smt
  aig=multcomm$n.aig
  cnf=multcomm$n.cnf
  sed -e "s,@,$i," multcomm.template > $smt
  boolector -rwl 0 -dai -o $aig $smt
  aigtocnf $aig $cnf
  i=`expr $i + 1`
done
