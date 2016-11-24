#!/bin/bash
# integer cube root algorithm, hacker's delight page 212
# equivalence checking with variant that uses or instead of add

id=1
echo "$((id++)) var 32 x"
((idx = id - 1))
idxorig=$idx
echo "$((id++)) constd 5 30"
((ids = id - 1))
idsorig=$ids
echo "$((id++)) zero 32"
((idy1 = id - 1))
idy2=$idy1
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
  echo "$((id++)) mul 32 $idy1 $id2"
  ((idy1 = id - 1))
  echo "$((id++)) add 32 $idy1 $id1"
  ((idy1p1 = id - 1))
  echo "$((id++)) mul 32 $idy1 $id3"
  ((lastid = id - 1))
  echo "$((id++)) mul 32 $lastid $idy1p1"
  ((lastid = id - 1))
  echo "$((id++)) add 32 $lastid $id1"
  ((lastid = id - 1))
  echo "$((id++)) sll 32 $lastid $ids"
  ((idb = id - 1))
  echo "$((id++)) sub 5 $ids $id3s"
  ((ids = id - 1))
  echo "$((id++)) ugte 1 $idx $idb"
  ((idcond = id - 1))
  echo "$((id++)) sub 32 $idx $idb"
  ((lastid = id - 1))
  echo "$((id++)) cond 32 $idcond $lastid $idx"
  ((idx = id - 1))
  echo "$((id++)) add 32 $idy1 $id1"
  ((lastid = id - 1))
  echo "$((id++)) cond 32 $idcond $lastid $idy1"
  ((idy1 = id - 1))
done

idx=$idxorig
ids=$idsorig
for ((i = 0; i < 11; i++))
do
  echo "$((id++)) mul 32 $idy2 $id2"
  ((idy2 = id - 1))
  echo "$((id++)) add 32 $idy2 $id1"
  ((idy2p1 = id - 1))
  echo "$((id++)) mul 32 $idy2 $id3"
  ((lastid = id - 1))
  echo "$((id++)) mul 32 $lastid $idy2p1"
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
  echo "$((id++)) add 32 $idy2 $lastid"
  ((idy2 = id - 1))
done

echo "$((id++)) ne 1 $idy1 $idy2"
((lastid = id - 1))
echo "$((id++)) root 1 $lastid"
