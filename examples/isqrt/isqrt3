#!/bin/bash
# integer square root algorithm, hacker's delight page 210
# bit-vector ORs are replaced by + 
# we show that x >= 0   =>   y^2 == x \/ (y^2 < x /\ (y+1)^2 > x)

id=1
echo "$((id++)) var 32 x"
((idx = id - 1))
idxorig=$idx
echo "$((id++)) constd 32 1073741824"
((idm = id - 1))
echo "$((id++)) zero 32"
((idy = id - 1))
echo "$((id++)) constd 5 1"
((id1 = id - 1))
echo "$((id++)) constd 5 2"
((id2 = id - 1))
for ((i = 0; i < 16; i++))
do
  echo "$((id++)) add 32 $idy $idm"
  ((idb = id - 1))
  echo "$((id++)) srl 32 $idy $id1"
  ((idy = id - 1))
  echo "$((id++)) ugte 1 $idx $idb"
  ((idcond = id - 1))
  echo "$((id++)) sub 32 $idx $idb"
  ((lastid = id - 1))
  echo "$((id++)) cond 32 $idcond $lastid $idx"
  ((idx = id - 1))
  echo "$((id++)) add 32 $idy $idm"
  ((lastid = id - 1))
  echo "$((id++)) cond 32 $idcond $lastid $idy"
  ((idy = id - 1))
  echo "$((id++)) srl 32 $idm $id2"
  ((idm = id - 1))
done
echo "$((id++)) mul 32 $idy $idy"
((idyy = id - 1))
echo "$((id++)) eq 1 $idxorig $idyy"
((ideq = id - 1))
echo "$((id++)) inc 32 $idy"
((lastid = id - 1))
echo "$((id++)) mul 32 $lastid $lastid"
((idyp1yp1 = id - 1))
echo "$((id++)) ult 1 $idyy $idxorig"
((idult = id - 1))
echo "$((id++)) ugt 1 $idyp1yp1 $idxorig"
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
