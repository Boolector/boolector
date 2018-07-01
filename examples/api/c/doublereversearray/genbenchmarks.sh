#!/bin/bash
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../../build/bin/boolector
drarray=$dir/../../../../build/bin/examples/doublereversearray
inc=1
limit=10
for ((size=2;size<=$limit;size+=$inc))
do
  header=1
  if [[ $size -lt 10 ]]; then
    sizestring="00"$size
  elif [[ $size -lt 100 ]]; then
    sizestring="0"$size
  else
    sizestring=$size
  fi
  filename=dubreva$sizestring"ue.smt2"
  $drarray $size | $boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(set-info :source |" >> $filename
      echo "We reverse an array of length $size twice in memory at $size positions." >> $filename
      echo "We show via extensionality that memory has to be equal." >> $filename
      echo "" >> $filename
      echo "In one case swapping elements is done via XOR in the following way:" >> $filename
      echo "x ^= y;" >> $filename 
      echo "y ^= x;" >> $filename
      echo "x ^= y;" >> $filename
      echo "In the other case the elements are just swapped." >> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "|)" >> $filename
      if [[ $overlap -eq 1 ]]; then
        echo "(set-info :status sat)" >> $filename
      else
        echo "(set-info :status unsat)" >> $filename
      fi
      echo "(set-info:category crafted)" >> $filename
      header=0
    else
      echo $line >> $filename
    fi
  done
done
