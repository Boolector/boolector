#!/bin/bash
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../bin/boolector
if [ ! -e $boolector ]
then
  echo "[error] Boolector not built"
  exit 1
fi
umulov1=$dir/umulov1.sh
umulov2=$dir/umulov2.sh
inc=16
for ((bits=16; bits <= 256; bits+=inc))
do
  header=1
  if [[ $bits -lt 100 ]]; then
    bitsstring="0"$bits
  else 
    bitsstring=$bits
  fi
  filename=umulov1bw$bitsstring".smt2"
  $umulov1 $bits | $boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(set-info :source |" >> $filename
      echo "We verify the correctness of an unsigned multiplication" >> $filename
      echo "overflow detection unit, which is described in" >> $filename
      echo "\"Combined Unsigned and Two's Complement Saturating Multipliers\"" >> $filename
      echo "by M. Schulte et al." >> $filename
      echo "" >> $filename
      echo "Bit-width: $bits" >> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "|)" >> $filename
      echo "(set-info :status unsat)" >> $filename
      echo "(set-info :category industrial)" >> $filename
      header=0
    else
      echo $line >> $filename
    fi
  done
  if [[ $bits -eq 128 ]]; then
    inc=32
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
  filename=umulov2bw$bitsstring".smt"
  $umulov2 $bits | $boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(set-info :source |" >> $filename
      echo "We verify a verification condition for an unsigned multiplication" >> $filename
      echo "overflow detection unit, which is described in" >> $filename
      echo "\"Combined Unsigned and Two's Complement Saturating Multipliers\"" >> $filename
      echo "by M. Schulte et al." >> $filename
      echo "" >> $filename
      echo "Let n be the bit-width, which is even." >> $filename
      echo "If the n/2 most significant bits of the operands are zero, then" >> $filename
      echo "the overflow detection unit must not yield an overflow." >> $filename
      echo "" >> $filename
      echo "Bit-width: $bits" >> $filename
      echo "" >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "|)" >> $filename
      echo "(set-info :status unsat)" >> $filename
      echo "(set-info :category industrial)" >> $filename
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
