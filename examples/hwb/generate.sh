#!/bin/sh
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../bin/boolector
aigtocnf=$dir/../../../aiger/aigtocnf
genhwb=$dir/genhwb.sh
type $aigtocnf > /dev/null 2>&1
if [ $? == 1 ]
then
  aigtocnf=`type aigtocnf | cut -d ' ' -f 2`
  type $aigtocnf > /dev/null 2>&1
  if [ $? == 1 ]
  then
    echo "[error] AIGER tools not installed"
    exit 1
  fi
fi
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
