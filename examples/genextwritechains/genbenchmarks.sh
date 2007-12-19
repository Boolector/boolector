#!/bin/bash
for ((numbits=2;numbits<=8;numbits+=1))
do
  header=1
  filename=writechains$numbits".smt"
  ./genextwritechains $numbits | boolector -rwl0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo "This benchmark generates write chains and shows" >> $filename
      echo "via extensionality that they are equal." >> $filename
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
