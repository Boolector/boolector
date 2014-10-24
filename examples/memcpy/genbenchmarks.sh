#!/bin/bash
numbits=32
for ((size=2;size<=12;size+=1))
do
  header=1
  if [[ $size -lt 10 ]]; then
    sizestring=0$size
  else
    sizestring=$size
  fi
  filename=memcpy$sizestring".smt"
  ./memcpy $size | boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo "We verify the correctness of the memcpy algorithm." >> $filename
      echo "We represent main memory as byte array of size 2 ^ 32," >> $filename 
      echo "and model the memcpy algorithm with pointer arithmetic." >> $filename
      echo "We assume that the memory locations do not overlap." >> $filename
      echo "Length: $size" >> $filename
      echo "" >> $filename
      echo -n "Contributed by Armin Biere " >> $filename
      echo "(armin.biere@jku.at)." >> $filename
      echo "}" >> $filename
      echo ":status unsat" >> $filename
      echo ":category { crafted }" >> $filename
      header=0
    else 
      echo $line >> $filename
    fi
  done
done
