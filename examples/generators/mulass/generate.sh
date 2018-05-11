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
i=1
while [ $i -le 16 ]
do
  n=`printf '%03d' $i`
  smt=mulass$n.smt2
  aig=mulass$n.aig
  cnf=mulass$n.cnf
  sed -e "s,@,$i," $dir/mulass.template > $smt
  $boolector -rwl 2 -dai -o $aig $smt
  $aigtocnf $aig $cnf
  i=`expr $i + 1`
done
