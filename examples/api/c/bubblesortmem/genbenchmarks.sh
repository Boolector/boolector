#!/bin/bash
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../../build/bin/boolector
bubble=$dir/../../../../build/bin/examples/bubblesortmem
inc=1
for ((size=2;size<=50;size+=$inc))
do
  header=1
  if [[ $size -lt 10 ]]; then
    sizestring="00"$size
  else
    sizestring="0"$size
  fi
  filename=bubsort$sizestring"un.smt2"
  $bubble $size | $boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(set-info :source |" >> $filename
      echo "We verify that bubble sort sorts an array" >> $filename
      echo "of length $size in memory. Additionally, we read an element" >> $filename
      
      echo "at an arbitrary index of the initial array and show that this" >> $filename
      echo "element can not be unequal to an element in the sorted array.">> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "|)" >> $filename
      echo "(set-info :status unsat)" >> $filename
      echo "(set-info :category crafted)" >> $filename
      header=0
    else
      echo $line >> $filename
    fi
  done
  if [[ $size -eq 10 ]]; then
    inc=2
  elif [[ $size -eq 20 ]]; then
    inc=5
  fi
done
