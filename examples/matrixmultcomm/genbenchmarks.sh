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
  filename=matrixmultcomm$sizestring".smt"
  ./matrixmultcomm $numbits $size | boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo -n "This benchmark shows that matrix multiplication" >> $filename
      echo "is not commutative in general." >> $filename
      echo "We try to show that A x B = B x A, which is generally not the case". >> $filename
      echo -n "The matrices have $size * $size fields of " >> $filename
      echo "bit-width $numbits," >> $filename
      echo "and are respectively represented by a one-dimensional array." >> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "}" >> $filename
      echo ":status sat" >> $filename
      echo ":category { crafted }" >> $filename
      header=0
    else 
      echo $line >> $filename
    fi
  done
done
