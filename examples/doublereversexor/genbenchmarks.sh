#!/bin/bash
  for ((size=2;size<=20;size+=1))
  do
    header=1
    filename=doublereversexor$size".smt"
    ./doublereversexor $size | boolector -rwl0 -ds | while read line
    do
      if [[ $header -eq 1 ]]; then
        echo "(benchmark $filename" > $filename
	echo ":source {" >> $filename
	echo "This benchmark verifies that reversing an arbitrary " >> $filename
	echo "sequence of $size bytes twice yields the original sequence." >> $filename
	echo "Note that the top and the bottom pointer can be arbitrary." >> $filename
	echo -n "The bytes are reversed " >> $filename
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
