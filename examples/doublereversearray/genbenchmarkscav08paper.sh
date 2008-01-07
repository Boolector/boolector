#!/bin/bash
inc=1
limit=100
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
  filename=dubrevl$sizestring"ue.smt"
  ./doublereversearray $size | boolector -rwl0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo "We reverse an array of length $size twice in memory." >> $filename
      echo "We show via extensionality that the final memory is equal to the initial." >> $filename
      echo "" >> $filename
      echo "Swapping elements is done via XOR in the following way:" >> $filename
      echo "x ^= y;" >> $filename 
      echo "y ^= x;" >> $filename
      echo "x ^= y;" >> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "}" >> $filename
      if [[ $overlap -eq 1 ]]; then
	echo ":status sat" >> $filename
      else
	echo ":status unsat" >> $filename
      fi
      echo ":category { crafted }" >> $filename
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
