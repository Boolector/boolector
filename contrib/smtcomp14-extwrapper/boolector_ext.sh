#!/bin/sh
BOOLECTOR=~/dev/boolector/boolector
BOOLECTOREXT=~/dev/boolector/contrib/smtcomp14-extwrapper/boolector-1.5.118

trap "exit 2" SIGHUP SIGINT SIGTERM

opts=""
benchmark=""

while [ $# -gt 0 ]
do
  case $1 in
    -*|[0-9]*) opts="$opts $1" ;;
	    *) benchmark="$1";;
  esac
  shift
done

out=`$BOOLECTOR $opts $benchmark`
ret=$?
if [ `echo $out | grep "extensionality on arrays/lambdas not yet supported" -c` -gt 0 ]; then 
  $BOOLECTOREXT $benchmark 
else
  if [ $ret -eq 10 ]; then
    echo "sat"
  elif [ $ret -eq 20 ]; then
    echo "unsat"
  else
    echo "unknown"
  fi
fi
exit $ret

