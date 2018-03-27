#!/bin/sh

readonly usage="usage: $(basename $0) <SAT solver> <up to benchmark number>"

die ()
{
  echo "[error] $(basename $0): $*" 1>&2
  exit 1
}

n=8200
while [ $# -gt 0 ]
do
  case $1 in
    -h|--help)
      echo $usage
      exit
      ;;
    -*)
      die "invalid option: $1"
      ;;
    *)
      if [ -z $sat ]
      then
        sat=$1
      else
        n=$1
        break
      fi
  esac
  shift
done

if [ -z $sat ]
then
  die "arguments missing"
fi

i=1
while [ $i -le $n ]
do
  base=addass`printf %04d $i`
  cnf=$base.cnf
  log=$base.log
  echo "$sat $cnf "
  $sat $cnf > $log
  i=`expr $i \* 2`
done
