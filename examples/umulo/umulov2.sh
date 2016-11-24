#!/bin/bash

if [[ $# -ne 1 ]]; then
  echo "Usage: ./umulov2 <num-bits>"
  exit 1
fi

if [[ $1 -lt 2 ]]; then
  echo "Number of bits must be greater than 1"
  exit 1
fi

numbits=$1
((numbits2 = numbits / 2))

echo "1 var $numbits"
echo "2 var $numbits"
echo "3 slice $numbits2 1 $((numbits - 1)) $numbits2"
echo "4 slice $numbits2 2 $((numbits - 1)) $numbits2"
echo "5 redor 1 3"
echo "6 redor 1 4"
echo "7 and 1 -5 -6"
echo "8 umulo 1 1 2"
echo "9 implies 1 7 -8"
echo "10 root 1 -9"
