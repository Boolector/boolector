#!/bin/bash

if [[ $# -ne 1 ]]; then
  echo "Usage: ./umulov1 <num-bits>"
  exit 1
fi

if [[ $1 -lt 1 ]]; then
  echo "Number of bits must be greater than 0"
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
echo "7 slice $numbits 6 $((numbits2 - 1)) $numbits"
echo "8 redor 1 7"
echo "9 umulo 1 1 2"
echo "10 eq 1 8 9"
echo "11 root 1 -10"

