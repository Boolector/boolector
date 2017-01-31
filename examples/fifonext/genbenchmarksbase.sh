#!/bin/bash
temp="/tmp/genbenchmarksbase.btor"
bw=32
maxk=10
for (( power = 2; power <= 10; power+=2))
do
  for ((k = 3; k <= $maxk; k++))
    do
      header=1
      if [[ $k -lt 10 ]]; then
        kstring=0$k
      else
        kstring=$k
      fi
      if [[ $power -lt 10 ]]; then
        powerstring=0$power
      else
        powerstring=$power
      fi
      file="fifo"$bw"bc"$powerstring"k"$kstring
      filebtor=$file".btor"
      filesmt=$file".smt"
      ./fifoeqcheck $bw $power > $temp 
      boolector $temp -rwl 1 -bmc-base-only -bmc-maxk=$k -bmc-replay $filebtor
      boolector -rwl 0 $filebtor -ds | while read line 
      do
        if [[ $header -eq 1 ]]; then
          echo "(benchmark $filesmt" > $filesmt
          echo ":source {" >> $filesmt
          echo "This benchmark comes from bounded model checking of two fifo implementations." >> $filesmt
          echo "The fifos are resetted once at the beginning. We show that the" >> $filesmt
          echo "implementations are behaviorally equivalent up to a bound of $k clock cycles." >> $filesmt
          echo "Fifo inputs: 'enqueue', 'dequeue', 'reset' (active low) and 'data_in'." >> $filesmt
          echo "Fifo output: 'empty', 'full' and 'data_out'." >> $filesmt
          echo "Bit-width: $bw" >> $filesmt
          echo "The fifos have an internal memory of size $((2 ** $power)), respectively modelled as array." >> $filesmt
          echo "" >> $filesmt
          echo -n "Contributed by Robert Brummayer " >> $filesmt
          echo "(robert.brummayer@gmail.com)." >> $filesmt
          echo "}" >> $filesmt
          echo ":status unsat" >> $filesmt
          echo ":category { crafted }" >> $filesmt
          header=0
        else
          echo $line >> $filesmt
        fi
    done
    rm $file".btor"
  done
done
