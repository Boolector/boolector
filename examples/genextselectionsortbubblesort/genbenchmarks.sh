#!/bin/bash
for ((numelements=2;numelements<=128;numelements*=2))
do
  header=1
  filename=selectionsortbubblesort$numelements".smt"
  ./genextselectionsortbubblesort 1 $numelements | boolector -rwl0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo "This benchmark sorts an arbitrary array" >> $filename
      echo -n "of size $numelements " >> $filename
      echo "via selection sort and bubble sort." >> $filename
      echo "Finally, it shows that the sorted arrays are equal." >> $filename
      echo "The elements of the array have bit width 1." >> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "}" >> $filename
      echo ":status unsat" >> $filename
      echo ":category { crafted }" >> $filename
      header=0
    else
      echo $line >> $filename
    fi
  done
done
