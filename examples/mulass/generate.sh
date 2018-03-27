#!/bin/sh
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../bin/boolector
aigtocnf=$dir/../../../aiger/aigtocnf
type $aigtocnf > /dev/null 2>&1
if [ $? == 1 ]
then
  aigtocnf=`type aigtocnf | cut -d ' ' -f 2`
  type $aigtocnf > /dev/null 2>&1
  if [ $? == 1 ]
  then
    echo "ERROR: AIGER tools not installed"
    exit 1
  fi
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
