#!/bin/bash
for ((numbits=2;numbits<=8;numbits*=2))
do
  for ((size=2;size<=256;size*=2))
  do
    header=1
    filename=doublereversexor$size"_"$numbits".smt"
    ./doublereversexor $numbits $size | boolector -rwl0 -ds | while read line
    do
      if [[ $header -eq 1 ]]; then
        echo "(benchmark $filename" > $filename
	echo ":source {" >> $filename
	echo "This benchmark verifies that reversing an arbitrary " >> $filename
	echo -n "array twice yields an array which is equivalent" >> $filename
	echo "to the original array." >> $filename
	echo -n "The array has size $size and the elements have " >> $filename
	echo "bit width $numbits." >> $filename
	echo -n "The array is reversed by swapping elements " >> $filename
	echo "via XOR in the following way:" >> $filename
	echo "x ^= y;" >> $filename 
	echo "y ^= x;" >> $filename
	echo "x ^= y;" >> $filename
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
done
