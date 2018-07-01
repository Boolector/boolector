#!/bin/bash
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../../build/bin/boolector
memcpy=$dir/../../../../build/bin/examples/memcpy
numbits=32
for ((size=2;size<=12;size+=1))
do
  header=1
  if [[ $size -lt 10 ]]; then
    sizestring=0$size
  else
    sizestring=$size
  fi
  filename=memcpy$sizestring".smt2"
  $memcpy $size | $boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(set-info :source |" >> $filename
      echo "We verify the correctness of the memcpy algorithm." >> $filename
      echo "We represent main memory as byte array of size 2 ^ 32," >> $filename 
      echo "and model the memcpy algorithm with pointer arithmetic." >> $filename
      echo "We assume that the memory locations do not overlap." >> $filename
      echo "Length: $size" >> $filename
      echo "" >> $filename
      echo -n "Contributed by Armin Biere " >> $filename
      echo "(armin.biere@jku.at)." >> $filename
      echo "|)" >> $filename
      echo "(set-info :status unsat)" >> $filename
      echo "(set-info :category crafted)" >> $filename
      header=0
    else 
      echo $line >> $filename
    fi
  done
done
