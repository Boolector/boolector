#!/bin/bash
# hacker's delight, chapter 7, page 101, rev(rev(x)) = x

readonly usage="./rev <num-bits>"

function ispowerof2
{
  local x=$1
  local temp=""
  if [[ $x -le 0 ]]; then
    echo 0
  else
    ((temp = x & (x - 1)))
    if [[ $temp -eq 0 ]]; then
      echo 1
    else
      echo 0
    fi
  fi
}

function log2
{
  local result=0
  local x=$1
  while [[ $x -gt 1 ]]
  do
    ((x >>= 1))
    ((result++))
  done
  echo $result
}

if [[ $# -ne 1 ]]; then
  echo "$usage"
  exit 1
fi

if [[ `ispowerof2 "$1"` -eq 0 ]]; then
  echo "number of bits must be positive and a power of 2"
  exit 1
fi

bits=$1
logbits=`log2 $bits`
id=1

echo "$((id++)) var $bits x"
((idx = id - 1))
((idorigx = id - 1))

for n in 0 1
do
  for ((i = 1; i < $bits; i *= 2))
  do
    echo "$((id++)) constd $logbits $i"
    ((shiftid = id - 1))
    counter=0
    val=0
    mask1=""
    mask2=""
    for ((j = 0; j < $bits; j++))
    do
      mask1=$mask1$val
      mask2=$mask2$((!val))
      ((counter++))
      if [[ $counter -eq $i ]]; then
        ((val = ! val))
        counter=0
      fi
    done
    echo "$((id++)) const $bits $mask1"
    ((lastid = id - 1))
    echo "$((id++)) and $bits $idx $lastid"
    ((lastid = id - 1))
    echo "$((id++)) sll $bits $lastid $shiftid"
    ((leftid = id - 1))

    echo "$((id++)) const $bits $mask2"
    ((lastid = id - 1))
    echo "$((id++)) and $bits $idx $lastid"
    ((lastid = id - 1))
    echo "$((id++)) srl $bits $lastid $shiftid"
    ((rightid = id - 1))
    echo "$((id++)) or $bits $leftid $rightid"
    ((idx = id - 1))
  done
done

echo "$((id++)) eq 1 $idx $idorigx"
((lastid = id - 1))
echo "$((id++)) root 1 -$lastid" 
