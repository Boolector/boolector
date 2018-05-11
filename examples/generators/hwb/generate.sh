#!/bin/sh
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../bin/boolector
aigtocnf=$dir/../../../../aiger/aigtocnf
if [ ! -e $boolector ]
then
  echo "[error] Boolector not built"
  exit 1
fi
if [ ! -e $aigtocnf ]
then
  echo "[error] AIGER tools not installed"
  exit 1
fi
genhwb=$dir/genhwb.sh
i=1
while [ $i -le 4 ]
do
  n=`printf '%03d' $i`
  smt=hwb$n.smt2
  aig=hwb$n.aig
  cnf=hwb$n.cnf
  $genhwb $i > $smt
  $boolector -rwl 2 --no-sort-exp --no-sort-aigvec -dai -o $aig $smt
  $aigtocnf $aig $cnf
  i=`expr $i + 1`
done
