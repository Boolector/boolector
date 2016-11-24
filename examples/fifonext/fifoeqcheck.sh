#!/bin/bash
if [[ $# -ne 2 ]]; then
  echo "Usage: ./fifoeqcheck <num-bits> <power>"
  exit
fi

tempstack="/tmp/fifoeqcheckstack.tmp"

./fifostack $1 $2 1 > $tempstack
iddataoutstack="`egrep .*var.*data_out < $tempstack | awk '{ print $1 }';`"
idemptystack="`egrep .*var.*empty < $tempstack | awk '{ print $1 }';`"
idfullstack="`egrep .*var.*full < $tempstack | awk '{ print $1 }';`"
idlaststack="`tail -n 1 $tempstack | awk '{ print $1 }';`"
idreset="`egrep .*var.*reset < $tempstack | awk '{ print $1 }';`"
idone="`egrep .*one.*1 < $tempstack | awk '{ print $1 }';`"

((id = idlaststack + 1))


tempqueue="/tmp/fifoeqcheckqueue.tmp"

./fifoqueue $1 $2 $id > $tempqueue
iddataoutqueue="`egrep .*var.*data_out < $tempqueue | awk '{ print $1 }';`"
idemptyqueue="`egrep .*var.*empty < $tempqueue | awk '{ print $1 }';`"
idfullqueue="`egrep .*var.*full < $tempqueue | awk '{ print $1 }';`"
idlastqueue="`tail -n 1 $tempqueue | awk '{ print $1 }';`"

((id = idlastqueue + 1))

cat $tempstack
echo ""
cat $tempqueue
echo ""
echo ""
echo "$((id++)) next 1 $idreset $idone"
echo ""
echo ";BAD: full, empty or data_out differ in the two implementations "
echo "$((id++)) ne 1 $idfullstack $idfullqueue"
((idne1 = id - 1))
echo "$((id++)) ne 1 $idemptystack $idemptyqueue"
((idne2 = id - 1))
echo "$((id++)) ne 1 $iddataoutstack $iddataoutqueue"
((idne3 = id - 1))
echo "$((id++)) or 1 $idne1 $idne2"
((lastid = id - 1))
echo "$((id++)) or 1 $idne3 $lastid"
((lastid = id - 1))
echo "$((id++)) and 1 $lastid $idreset"
((lastid = id - 1))
echo "$((id++)) root 1 $lastid"
