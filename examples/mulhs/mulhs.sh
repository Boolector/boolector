#!/bin/bash
#mulhs algorithm from hacker's delight, p132

function log_2
{
  local result=0
  local x=$1
  while [[ "$x" -gt 1 ]]
  do  
      ((x >>= 1))
      ((result++))
  done 
  echo $result
}

if [[ $# -ne 1 ]]; then
  echo "Usage: ./mulhs <num-bits>"
  exit 1
fi

if [[ "$1" -ne 4 ]] && [[ "$1" -ne 8 ]] && [[ "$1" -ne 16 ]] && [[ "$1" -ne 32 ]] && [[ "$1" -ne 64 ]]; then
  echo "number of bits must be in {4, 8, 16, 32, 64}"
  exit 1
fi

id=1
numbits=$1
numbitslog=`log_2 $numbits`
((numbitshalf =  numbits >> 1))
((numbitstwice = numbits << 1))

echo "$((id++)) var $numbits u"
((idu = id - 1))
echo "$((id++)) var $numbits v"
((idv = id - 1))
echo "$((id++)) constd $numbitslog $numbitshalf"
((idconstlog = id - 1))
echo -n "$((id++)) const $numbits "
for ((i = 0; i < $numbits; i++))
do
  if [[ $i -lt $numbitshalf ]]; then
    echo -n "0"
  else
    echo -n "1"
  fi
done
echo ""
((idconst = id - 1))
echo "$((id++)) and $numbits $idu $idconst"
((idu0 = id - 1))
echo "$((id++)) sra $numbits $idu $idconstlog"
((idu1 = id - 1))
echo "$((id++)) and $numbits $idv $idconst"
((idv0 = id - 1))
echo "$((id++)) sra $numbits $idv $idconstlog"
((idv1 = id - 1))
echo "$((id++)) mul $numbits $idu0 $idv0"
((lastid = id - 1))
echo "$((id++)) srl $numbits $lastid $idconstlog"
((idw0 = id - 1))
echo "$((id++)) mul $numbits $idu1 $idv0"
((lastid = id - 1))
echo "$((id++)) add $numbits $lastid $idw0"
((idt = id - 1))
echo "$((id++)) and $numbits $idt $idconst"
((idw1 = id - 1))
echo "$((id++)) sra $numbits $idt $idconstlog"
((idw2 = id - 1))
echo "$((id++)) mul $numbits $idu0 $idv1"
((lastid = id - 1))
echo "$((id++)) add $numbits $lastid $idw1"
((idw1 = id - 1))
echo "$((id++)) sra $numbits $idw1 $idconstlog"
((idw1 = id - 1))
echo "$((id++)) mul $numbits $idu1 $idv1"
((idresult = id - 1))
echo "$((id++)) add $numbits $idw1 $idw2"
((lastid = id - 1))
echo "$((id++)) add $numbits $idresult $lastid"
((idresult = id - 1))

echo "$((id++)) sext $numbitstwice $idu $numbits"
((iduext = id - 1))
echo "$((id++)) sext $numbitstwice $idv $numbits"
((idvext = id - 1))
echo "$((id++)) mul $numbitstwice $iduext $idvext"
((lastid = id - 1))
echo "$((id++)) slice $numbits $lastid $((numbitstwice - 1)) $((numbitstwice - $numbits))"
((lastid = id - 1))
echo "$((id++)) eq 1 $idresult $lastid"
((lastid = id - 1))
echo "$((id++)) root 1 -$lastid"
