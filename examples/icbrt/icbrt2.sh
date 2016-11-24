#!/bin/bash
# integer cube root algorithm, hacker's delight page 210, without "if"
# we show that x >= 0   =>   y^3 == x \/ (y^3 < x /\ (y+1)^3 > x)

id=1
echo "$((id++)) var 32 x"
((idx = id - 1))
idxorig=$idx
echo "$((id++)) constd 5 30"
((ids = id - 1))
echo "$((id++)) zero 32"
((idy = id - 1))
echo "$((id++)) constd 32 1"
((id1 = id - 1))
echo "$((id++)) constd 32 2"
((id2 = id - 1))
echo "$((id++)) constd 32 3"
((id3 = id - 1))
echo "$((id++)) constd 5 3"
((id3s = id - 1))
echo "$((id++)) constd 5 31"
((id31s = id - 1))
for ((i = 0; i < 11; i++))
do
  echo "$((id++)) mul 32 $idy $id2"
  ((idy = id - 1))
  echo "$((id++)) add 32 $idy $id1"
  ((idyp1 = id - 1))
  echo "$((id++)) mul 32 $idy $id3"
  ((lastid = id - 1))
  echo "$((id++)) mul 32 $lastid $idyp1"
  ((lastid = id - 1))
  echo "$((id++)) add 32 $lastid $id1"
  ((lastid = id - 1))
  echo "$((id++)) sll 32 $lastid $ids"
  ((idb = id - 1))
  echo "$((id++)) sub 5 $ids $id3s"
  ((ids = id - 1))
  echo "$((id++)) sub 32 $idx $idb"
  ((lastid = id - 1))
  echo "$((id++)) or 32 $idx -$lastid"
  ((lastid = id - 1))
  echo "$((id++)) sra 32 $lastid $id31s"
  ((idt = id - 1))
  echo "$((id++)) and 32 $idb $idt"
  ((lastid = id - 1))
  echo "$((id++)) sub 32 $idx $lastid"
  ((idx = id - 1))
  echo "$((id++)) and 32 $id1 $idt"
  ((lastid = id - 1))
  echo "$((id++)) add 32 $idy $lastid"
  ((idy = id - 1))
done
echo "$((id++)) mul 32 $idy $idy"
((lastid = id - 1))
echo "$((id++)) mul 32 $lastid $idy"
((idyyy = id - 1))
echo "$((id++)) eq 1 $idxorig $idyyy"
((ideq = id - 1))
echo "$((id++)) inc 32 $idy"
((idyp1 = id - 1))
echo "$((id++)) mul 32 $idyp1 $idyp1"
((idyp1yp1 = id - 1))
echo "$((id++)) mul 32 $idyp1yp1 $idyp1"
((idyp1yp1yp1 = id - 1))
echo "$((id++)) ult 1 $idyyy $idxorig"
((idult = id - 1))
echo "$((id++)) ugt 1 $idyp1yp1yp1 $idxorig"
((idugt = id - 1))
echo "$((id++)) and 1 $idult $idugt"
((lastid = id - 1))
echo "$((id++)) or 1 $ideq $lastid"
((idor = id - 1))
echo "$((id++)) slice 1 $idxorig 31 31"
((lastid = id - 1))
echo "$((id++)) implies 1 -$lastid $idor"
((lastid = id - 1))
echo "$((id++)) root 1 -$lastid"
