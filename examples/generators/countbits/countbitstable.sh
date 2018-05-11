#!/bin/bash
# Count bits pop(x) algorithm, table lookup version,
# hacker's delight, page 71
# we verifiy it by cross-checking with the obvios method of counting bits
#    for (s = i = 0; i < n; i++)
#      if (x & (1 << i))
#        s++;

function dec2binbyte
{
  local x=$1
  local ret="`echo "ibase=10; obase=2; $x" | bc`"
  local result=`printf "%08d" $ret`
  echo $result
}

function pop
{
  local x=$1
  local result=0
  while [[ -n "$x" ]]
  do
    if [[ "${x:0:1}" = "1" ]]; then 
      ((result++))
    fi
    x=${x:1}
  done
  echo $result
}



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
  echo "Usage ./countbitstable <num-bits>"
  exit 1
fi

numbits=$1
if [[ "$numbits" -lt 8 ]] || [[ ! `is_power_of_2 $numbits` -eq 1 ]]; then
  echo "Number of bits must be a power of 2 >= 8"
  exit 1
fi
numbitslog=`log_2 $numbits`
id=1

echo "$((id++)) var $numbits x"
((idx = id - 1))
((idsum = idx))
((idxorig = idx))
echo "$((id++)) array 8 8"
((idarray = id - 1))
echo "$((id++)) zero $numbits"
((idzero = id - 1))
echo "$((id++)) one $numbits"
((idone = id - 1))
if [[ $numbits -gt 8 ]]; then
  echo "$((id++)) constd $numbitslog 8"
  ((ideight = id - 1))
fi
for ((i = 0; i < 256; i++))
do
  binrep="`dec2binbyte $i`"
  echo "$((id++)) const 8 $binrep"
  ((idindex = id - 1))
  pop="`pop $binrep`"
  echo "$((id++)) const 8 `dec2binbyte $pop`"
  ((lastid = id - 1))
  echo "$((id++)) write 8 8 $idarray $idindex $lastid"
  ((idarray = id - 1))
done

echo "$((id++)) slice 8 $idx 7 0"
((lastid = id - 1))
echo "$((id++)) read 8 $idarray $lastid"
((lastid = id - 1))
echo "$((id++)) uext $numbits $lastid $((numbits - 8))"
((idsum = id - 1))
for ((i = 8; i < $numbits; i += 8))
do
  echo "$((id++)) srl $numbits $idx $ideight"
  ((idx = id - 1))
  echo "$((id++)) slice 8 $idx 7 0"
  ((lastid = id - 1))
  echo "$((id++)) read 8 $idarray $lastid"
  ((lastid = id - 1))
  echo "$((id++)) uext $numbits $lastid $((numbits - 8))"
  ((lastid = id - 1))
  echo "$((id++)) add $numbits $lastid $idsum"
  ((idsum = id - 1))
done
((idresult1 = idsum))

((idsum = idzero))
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
