#!/bin/bash
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../../build/bin/boolector
swapmem=$dir/../../../../build/bin/examples/swapmem
for ((overlap=0;overlap<=1;overlap+=1))
  do
  if [[ $overlap -eq 1 ]]; then
    overlaparg="-o"
    limit=60
    inc=2
  else
    overlaparg=""
    limit=30
    inc=1
  fi
  for ((size=2;size<=$limit;size+=$inc))
  do
    header=1
    if [[ $size -lt 10 ]]; then
      sizestring="00"$size
    else
      sizestring="0"$size
    fi
    if [[ $overlap -eq 1 ]]; then
      filename=swapmem$sizestring"se.smt2"
    else
      filename=swapmem$sizestring"ue.smt2"
    fi
    $swapmem $size $overlaparg | $boolector -rwl 0 -ds | while read line
    do
      if [[ $header -eq 1 ]]; then
        echo "(set-info :source |" >> $filename
        echo "We swap two byte sequences of length $size twice in memory." >> $filename
        if [[ $overlap -eq 1 ]]; then
          echo "The sequences can overlap, hence it is not always the case" >> $filename
        else
          echo "The sequences can not overlap, hence it is always the case" >> $filename
        fi
        echo "that swapping them twice yields the initial memory." >> $filename
        echo "" >> $filename
        echo "Swapping is done via XOR in the following way:" >> $filename
        echo "x ^= y;" >> $filename 
        echo "y ^= x;" >> $filename
        echo "x ^= y;" >> $filename
        echo "" >> $filename
        echo -n "Contributed by Robert Brummayer " >> $filename
        echo "(robert.brummayer@gmail.com)." >> $filename
        echo "|)" >> $filename
        if [[ $overlap -eq 1 ]]; then
          echo "(set-info :status sat)" >> $filename
        else
          echo "(set-info :status unsat)" >> $filename
        fi
        echo "(set-info :category crafted)" >> $filename
        header=0
      else
        echo $line >> $filename
      fi
    done
  done
done
