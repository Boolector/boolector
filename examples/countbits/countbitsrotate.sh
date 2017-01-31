#!/bin/bash
# Count bits pop(x) algorithm, rotate and sum method,
# hacker's delight, page 70
# we verify it by cross-checking with the obvious method of counting bits
#    for (s = i = 0; i < n; i++)
#      if (x & (1 << i))
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
  echo "Usage ./countbitsrotate <num-bits>"
  exit 1
fi

numbits=$1
if [[ "$numbits" -le 1 ]] || [[ ! `is_power_of_2 $numbits` -eq 1 ]]; then
  echo "Number of bits must be a power of 2 > 1"
  exit 1
fi
numbitslog=`log_2 $numbits`
id=1

echo "$((id++)) var $numbits x"
((idx = id - 1))
((idsum = idx))
((idxorig = idx))
for ((i = 1; i < $numbits; i++))
do
  echo "$((id++)) constd $numbitslog $i"
  ((lastid = id - 1))
  echo "$((id++)) rol $numbits $idx $lastid"
  ((idx = id - 1))
  echo "$((id++)) add $numbits $idsum $idx"
  ((idsum = id - 1))
done
echo "$((id++)) neg $numbits $idsum"
((idresult1 = id - 1))

echo "$((id++)) zero $numbits"
((idsum = id - 1))
((idzero = idsum))
echo "$((id++)) one $numbits"
((idone = id - 1))

for ((i = 0; i < $numbits; i++))
do
  echo "$((id++)) constd $numbitslog $i"
  ((lastid = id - 1))
  echo "$((id++)) sll $numbits $idone $lastid"
  ((lastid = id - 1))
  echo "$((id++)) and $numbits $idxorig $lastid"
  ((lastid = id - 1))
  echo "$((id++)) ne 1 $lastid $idzero"
  ((idcond = id - 1))
  echo "$((id++)) inc $numbits $idsum"
  ((lastid = id - 1))
  echo "$((id++)) cond $numbits $idcond $lastid $idsum"
  ((idsum = id - 1))
done
((idresult2 = idsum))

echo "$((id++)) eq 1 $idresult1 $idresult2"
((lastid = id - 1))
echo "$((id++)) root 1 -$lastid"
