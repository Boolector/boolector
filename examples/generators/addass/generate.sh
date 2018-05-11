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
while [ $i -le 8192 ]
do
  n=`printf '%04d' $i`
  smt=addass$n.smt2
  aig=addass$n.aig
  cnf=addass$n.cnf
  sed -e "s,@,$i," $dir/addass.template > $smt
  $boolector -rwl 2 -dai -o $aig $smt
  $aigtocnf $aig $cnf
  i=`expr $i \* 2`
done
