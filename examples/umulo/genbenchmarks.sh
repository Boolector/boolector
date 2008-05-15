#!/bin/bash
for bits in 32 48 64 96 128 192 256
do
  header=1
  if [[ $bits -lt 100 ]]; then
    bitsstring="0"$bits
  else 
    bitsstring=$bits
  fi
  filename=umulo$bitsstring".smt"
  ./umulo $bits | boolector -rwl0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo "We verify the correctness of an unsigned multiplication" >> $filename
      echo "overflow detection unit as proposed in" >> $filename
      echo "\"Combined unsigned and two's complement saturating multipliers\"" >> $filename
      echo "by M. Schulte et al." >> $filename
      echo "" >> $filename
      echo "Bit-width: $bits" >> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "}" >> $filename
      echo ":status unsat" >> $filename
      echo ":category { industrial }" >> $filename
      header=0
    else
      echo $line >> $filename
    fi
  done
done
