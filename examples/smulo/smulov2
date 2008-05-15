#!/bin/bash

if [[ $# -ne 1 ]]; then
  echo "Usage: ./smulov2 <num-bits>"
  exit 1
fi

if [[ $1 -lt 2 ]]; then
  echo "Number of bits must be greater than 1"
  exit 1
fi

numbits=$1
((numbits2 = numbits * 2))

echo "1 var $numbits"
echo "2 var $numbits"
echo "3 zero $numbits"
echo "4 concat $numbits2 3 1"
echo "5 concat $numbits2 3 2"
echo "6 mul $numbits2 4 5"
id=7
firstslice=7
for ((i = numbits2 - 1; i >= numbits - 1; i--))
do
  echo "$((id++)) slice 1 6 $i $i"
done
((lastslice = id - 1))
firstxor=$id
for ((i = firstslice; i < lastslice; i++))
do
  echo "$((id++)) xor 1 $i $lastslice"
done
((lastxor = id - 1))
echo "$((id++)) or 1 $firstxor $((firstxor + 1))"
((lastor = id - 1))
for ((i = firstxor + 2; i <= lastxor; i++))
do
  echo "$((id++)) or 1 $lastor $i"
  ((lastor = id - 1))
done
echo "$((id++)) smulo 1 1 2"
((smulo = id - 1))
echo "$((id++)) implies 1 $smulo $lastor"
((lastid = id - 1))
echo "$((id++)) root 1 -$lastid"
