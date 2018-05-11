#!/bin/sh
die () {
  echo "*** countinc.sh: $*" 1>&2
  exit 1
}
[ $# -eq 1 ] || die "expected exactly one argument (try '-h')"
[ x"$1" = x-h ] && die "usage: countinc.sh [-h] <bits>"
case $1 in
  1*|2*|3*|4*|5*|6*|7*|8*|9*);;
  0) die "expected positive number as argument (try '-h')";;
  *) die "expected number as argument (try '-h')";;
esac
n=`expr $1 + 0 2>/dev/null`
i=0
p=1
while [ $i -lt $n ]
do
  i=`expr $i + 1`
  p=`expr $p \* 2`
done
m=`expr $p - 1`
echo "(benchmark count${n}inc"
echo ":logic QF_BV"
echo ":extrafuns ((s0 BitVec[$n]))"
echo ":extrafuns ((zero BitVec[$n]))"
echo ":extrafuns ((one BitVec[$n]))"
echo ":extrafuns ((goal BitVec[$n]))"
echo ":assumption (= goal bv$m[$n])"
echo ":assumption (= zero bv0[$n])"
echo ":assumption (= one bv1[$n])"
echo ":assumption (= s0 zero)"
echo ":formula (= s0 goal)"
prev=0
i=1
while [ $i -le $m ]
do
echo ":extrafuns ((r$i Bool))"
echo ":extrafuns ((e$i Bool))"
echo ":extrafuns ((s$i BitVec[$n]))"
echo ":assumption (= s$i (ite r$i zero (ite e$i (bvadd s$prev one) s$prev)))"
echo ":formula (= s$i goal)"
prev=$i
i=`expr $i + 1`
done
echo ")"
