#!/bin/sh
i=1
while [ $i -le 4 ]
do
  n=`printf '%03d' $i`
  smt=hwb$n.smt
  aig=hwb$n.aig
  cnf=hwb$n.cnf
  ./genhwb.sh $i > $smt
  boolector -rwl 2 --no-sort-exp --no-sort-aigvec -dai -o $aig $smt
  aigtocnf $aig $cnf
  i=`expr $i + 1`
done
