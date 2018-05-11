#!/bin/bash
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../bin/boolector
if [ ! -e $boolector ]
then
  echo "[error] Boolector not built"
  exit 1
fi
countbits=$dir/countbits
limit=512
for ((size=16;size<=$limit;size*=2))
do
  header=1
  if [[ $size -lt 10 ]]; then
    sizestring="00"$size
  elif [[ $size -lt 100 ]]; then
    sizestring="0"$size
  else
    sizestring=$size
  fi
  filename=countbits$sizestring".smt2"
  $countbits $size | $boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(set-info :source |" >> $filename
      echo "Verifies correcntess of Peter Wegner's algorithm:" >> $filename
      echo "P. Wegner." >> $filename
      echo "A technique for counting ones in a binary computer." >> $filename
      echo "CACM 3(5), 1960." >> $filename
      echo "Bit-width: $size" >> $filename
      echo "" >> $filename
      echo -n "Contributed by Armin Biere " >> $filename
      echo "(armin.biere@jku.at)." >> $filename
      echo "|)" >> $filename
      echo "(set-info :status unsat)" >> $filename
      echo "(set-info :category crafted)" >> $filename
      header=0
    else
      echo $line >> $filename
    fi
  done
done
