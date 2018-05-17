#!/bin/bash

contribdir=$(dirname "$(readlink -f $0)")
boolector=$contribdir/../bin/boolector
btormbt=$contribdir/../bin/btormbt

tmpfile=/tmp/testprintmodelsmt2-$$.smt2
infile=/tmp/testprintmodelsmt2-infile-$$.smt2
modelfile=/tmp/testprintmodelsmt2-model-$$.smt2
tracefile=/tmp/testprintmodelsmt2-$$.trace

cleanup-and-exit ()
{
  rm -f $tmpfile
  rm -f $infile
  rm -f $modelfile
  rm -f $tracefile
  exit
}

trap "cleanup-and-exit;" SIGHUP SIGINT SIGTERM
#trap exit 1 SIGHUP SIGINT SIGTERM

while true
do
  seed="$RANDOM$RANDOM$RANDOM"
  BTORAPITRACE="$tracefile" ${btormbt} --output-format smt2 $seed -t 2 --p-dump 1.0 | head -n -3 > $infile
  $boolector -m --smt2-model $infile > $modelfile
  ret=$?
  if [[ $ret = 10 ]]; then
    cat $infile | sed -r 's/\(check-sat\)|\(exit\)//' > $tmpfile
    cat $modelfile | sed 's/sat//' >> $tmpfile
    echo "(check-sat)" >> $tmpfile
    echo "(exit)" >> $tmpfile
    $boolector $tmpfile > /dev/null
    ret=$?
    if [[ $ret != 10 ]]; then
      echo "found bug: ${seed}"
      cp $tracefile testprintmodelsmt2-error-${seed}.trace
      cp $tmpfile testprintmodelsmt-error-${seed}.smt2
      break
    fi
  fi
done

cleanup-and-exit

