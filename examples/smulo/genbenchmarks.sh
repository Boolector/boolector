#!/bin/bash
inc=16
for ((bits = 16; bits <= 512; bits += inc))
do
  header=1
  if [[ $bits -lt 100 ]]; then
    bitsstring="0"$bits
  else 
    bitsstring=$bits
  fi
  filename=smulov1bw$bitsstring".smt"
  ./smulov1 $bits | boolector -rwl0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo "We verify a verification condition for a signed multiplication" >> $filename
      echo "overflow detection unit as proposed in" >> $filename
      echo "\"Combined Unsigned and Two's Complement Saturating Multipliers\"" >> $filename
      echo "by M. Schulte et al." >> $filename
      echo "" >> $filename
      echo "Let n be the bit-width of the operands and r the result of the multiplication.">> $filename
      echo "Let ^ denote boolean XOR, and + boolean OR." >> $filename
      echo "If the overflow detection unit finds an overflow, then it must be the case that" >> $filename
      echo "(r[2n-1] ^ r[n-1])  +  (r[2n-2] ^ r[n-1])  +  ...  +  ([r[n] ^ r[n-1]) holds." >> $filename
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
  if [[ $bits -eq 128 ]]; then
    inc=32
  elif [[ $bits -eq 256 ]]; then
    inc=64
  fi
done

inc=16
for ((bits = 32; bits <= 1024; bits+=inc))
do
  header=1
  if [[ $bits -lt 100 ]]; then
    bitsstring="00"$bits
  elif [[ $bits -lt 1000 ]]; then 
    bitsstring="0"$bits
  else
    bitsstring=$bits
  fi
  filename=smulov2bw$bitsstring".smt"
  ./smulov2 $bits | boolector -rwl0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(benchmark $filename" > $filename
      echo ":source {" >> $filename
      echo "We verify a verification condition for a signed multiplication" >> $filename
      echo "overflow detection unit as proposed in" >> $filename
      echo "\"Combined Unsigned and Two's Complement Saturating Multipliers\"" >> $filename
      echo "by M. Schulte et al." >> $filename
      echo "" >> $filename
      echo "Let n be the bit-width, which is even." >> $filename
      echo "If the n/2 + 1 most significant bits of the operands are zero, then." >> $filename
      echo "the overflow detection unit must not yield an overflow." >> $filename
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
  if [[ $bits -lt 256 ]]; then
    ((inc = 2 * inc))
  else
    inc=128
  fi
done
