#!/bin/bash
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
boolector=$dir/../../../../build/bin/boolector
np2=$dir/../../../../build/bin/examples/nextpowerof2
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
  filename=nextpoweroftwo$sizestring".smt2"
  $np2 $size | $boolector -rwl 0 -ds | while read line
  do
    if [[ $header -eq 1 ]]; then
      echo "(set-info :source |" >> $filename
      echo "We verify the correctness of the \"next power of 2 algorithm\"" >> $filename
      echo "from the book \"hacker's delight\" (Warren Jr., Henry)". >> $filename
      echo -n "Contributed by Robert Brummayer " >> $filename
      echo "(robert.brummayer@gmail.com)." >> $filename
      echo "|)" >> $filename
      echo "" >> $filename
      echo "; Algorithm:" >> $filename
      echo "; int next_power_of_2 (int x)" >> $filename
      echo "; {" >> $filename
      echo ";   int i;" >> $filename
      echo ";   x--;" >> $filename
      echo ";   for (i = 1; i < sizeof(int) * 8; i = i * 2)" >> $filename
      echo ";   x = x | (x >> i)" >> $filename
      echo ";   return x + 1;" >> $filename
      echo "; }" >> $filename
      echo ";" >> $filename
      echo ";Bit-width: $size" >> $filename
      echo "" >> $filename
      echo "(set-info :status unsat)" >> $filename
      echo "(set-info :category crafted)" >> $filename
      header=0
    else
      echo $line >> $filename
    fi
  done
done
