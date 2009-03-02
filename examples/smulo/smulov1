#!/bin/bash

if [[ $# -ne 1 ]]; then
  echo "Usage: ./smulov1 <num-bits>"
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
echo "3 sext $numbits2 1 $numbits"
echo "4 sext $numbits2 2 $numbits"
echo "5 mul $numbits2 3 4"
echo "6 constd $numbits2 `echo "2 ^ ($numbits - 1)" | bc`"
echo "7 neg $numbits2 6" 
echo "8 slt 1 5 7"
echo "9 sgte 1 5 6"
echo "10 or 1 8 9"
echo "11 smulo 1 1 2"
echo "12 eq 1 10 11"
echo "13 root 1 -12" 
