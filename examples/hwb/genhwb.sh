#!/bin/sh
n=$1
l=1
while [ `echo "2 $l ^p" |dc` -le $n ]
do
  l=`expr $l + 1`
done
m=`expr $l - 1`
p1=`echo "2 $l ^ $n - p" | dc`
p2=`echo "2 $l ^ $l - p" | dc`
echo "(set-logic QF_BV)"

echo "(declare-fun x () (_ BitVec $n))"
i=0
prev="(_ bv$n $l)"
while [ $i -lt $n ]
do
  echo "(declare-fun x$i () (_ BitVec $l))"
  echo "(assert (= x$i (bvsub $prev ((_ zero_extend $m) ((_ extract $i $i) x)))))"
  prev=x$i
  i=`expr $i + 1`
done
echo "(declare-fun g () (_ BitVec 1))"
echo "(assert (= g ((_ extract 0 0) (bvlshr ((_ zero_extend $p1) x) ((_ zero_extend $p2) $prev)))))"

echo "(assert g)"

echo "(check-sat)"
