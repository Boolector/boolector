#!/bin/bash
# Number of leading zeroes nlz(x) algorithm
# hacker's delight, page 79, working both ends at the same time 
# we verifiy it by cross-checking with an obvios method of counting leading 0s 
#    s = 0;
#    for (i = n - 1; i >= 0; i--)
#      if (x & (1 << i))
#        break;
#      else
#        s++;

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

function is_power_of_2
{
  local x=$1
  ((x = x & (x - 1)))
  if [[ x -eq 0 ]]; then
    echo 1
  else
    echo 0
  fi
}

if [[ $# -ne 1 ]]; then
  echo "Usage ./nlzbe <num-bits>"
  exit 1
fi

numbits=$1
if [[ "$numbits" -le 2 ]] || [[ ! `is_power_of_2 $numbits` -eq 1 ]]; then
  echo "Number of bits must be a power of 2 > 2"
  exit 1
fi
numbitslog=`log_2 $numbits`
id=1

echo "$((id++)) var $numbits result1init"
((idresult1 = id - 1))
echo "$((id++)) var $numbits x"
((idx = id - 1))
((idxorig = idx))
((idy = idx))
echo "$((id++)) zero 1"
((idzero1 = id - 1))
((idterminate = idzero1))
echo "$((id++)) zero $numbits"
((idzero = id - 1))
((idn = idzero))
echo "$((id++)) one $numbits"
((idone = id - 1))
echo "$((id++)) one $numbitslog"
((idonelog = id - 1))
echo "$((id++)) constd $numbits $numbits"
((idnumbits = id - 1))
for ((i = 0; i < $numbits / 2 + 1; i++))
do
  echo "$((id++)) eq 1 $idy $idzero"
  ((idcond2 = id - 1))
  echo "$((id++)) sub $numbits $idnumbits $idn"
  ((lastid = id - 1))
  echo "$((id++)) cond $numbits $idcond2 $lastid $idresult1"
  ((tempid = id - 1))
  echo "$((id++)) slt 1 $idx $idzero"
  ((idcond1 = id - 1))
  echo "$((id++)) cond $numbits $idcond1 $idn $tempid"
  ((lastid = id - 1))
  echo "$((id++)) cond $numbits $idterminate $idresult1 $lastid"
  ((idresult1 = id - 1))
  echo "$((id++)) or 1 $idcond1 $idcond2"
  ((lastid = id - 1))
  echo "$((id++)) or 1 $idterminate $lastid"
  ((idterminate = id - 1))
  echo "$((id++)) inc $numbits $idn"
  ((idn = id - 1))
  echo "$((id++)) sll $numbits $idx $idonelog"
  ((idx = id - 1))
  echo "$((id++)) sra $numbits $idy $idonelog"
  ((idy = id - 1))
done

((idsum = idzero))
((idfoundone = idzero1))

for ((i = $numbits - 1; i >= 0; i--))
do
  echo "$((id++)) constd $numbitslog $i"
  ((lastid = id - 1))
  echo "$((id++)) sll $numbits $idone $lastid"
  ((lastid = id - 1))
  echo "$((id++)) and $numbits $idxorig $lastid"
  ((lastid = id - 1))
  echo "$((id++)) eq 1 $lastid $idzero"
  ((idcond = id - 1))
  echo "$((id++)) or 1 $idfoundone -$idcond"
  ((idfoundone = id - 1))
  echo "$((id++)) inc $numbits $idsum"
  ((lastid = id - 1))
  echo "$((id++)) cond $numbits $idfoundone $idsum $lastid"
  ((lastid = id - 1))
  echo "$((id++)) cond $numbits $idcond $lastid $idsum"
  ((idsum = id - 1))
done
((idresult2 = idsum))

echo "$((id++)) eq 1 $idresult1 $idresult2"
((lastid = id - 1))
echo "$((id++)) root 1 -$lastid"
