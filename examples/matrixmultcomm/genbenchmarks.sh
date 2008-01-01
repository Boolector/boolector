#!/bin/bash
for ((numbits=2;numbits<=8;numbits*=2))
do
  for ((size=2;size<=12;size+=1))
  do
    header=1
    filename=matrixmultcomm$size"_"$numbits".smt"
    ./genextmatrixmultcomm $numbits $size | boolector -rwl0 -ds | while read line
    do
      if [[ $header -eq 1 ]]; then
        echo "(benchmark $filename" > $filename
	echo ":source {" >> $filename
	echo "This benchmark verifies that matrix multiplication" >> $filename
	echo "is not commutative in general." >> $filename
	echo -n "The matrix has $size * $size fields of " >> $filename
	echo "bit width $numbits." >> $filename
	echo "It is modelled as one-dimensional array." >> $filename
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
done
