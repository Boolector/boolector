#!/bin/bash
# integer square root algorithm, hacker's delight page 210
# equality check of the original algorithm and the variant without "if"

id=1
echo "$((id++)) var 32 x"
((idx = id - 1))
idxorig=$idx
echo "$((id++)) constd 32 1073741824"
((idm = id - 1))
idmorig=$idm
echo "$((id++)) zero 32"
((idy1 = id - 1))
idy2=$idy1
echo "$((id++)) constd 5 1"
((id1 = id - 1))
echo "$((id++)) constd 5 2"
((id2 = id - 1))
echo "$((id++)) constd 5 31"
((id31 = id - 1))
for ((i = 0; i < 16; i++))
do
  echo "$((id++)) or 32 $idy1 $idm"
  ((idb = id - 1))
  echo "$((id++)) srl 32 $idy1 $id1"
  ((idy1 = id - 1))
  echo "$((id++)) ugte 1 $idx $idb"
  ((idcond = id - 1))
  echo "$((id++)) sub 32 $idx $idb"
  ((lastid = id - 1))
  echo "$((id++)) cond 32 $idcond $lastid $idx"
  ((idx = id - 1))
  echo "$((id++)) or 32 $idy1 $idm"
  ((lastid = id - 1))
  echo "$((id++)) cond 32 $idcond $lastid $idy1"
  ((idy1 = id - 1))
  echo "$((id++)) srl 32 $idm $id2"
  ((idm = id - 1))
done

idm=$idmorig
idx=$idxorig
for ((i = 0; i < 16; i++))
do
  echo "$((id++)) or 32 $idy2 $idm"
  ((idb = id - 1))
  echo "$((id++)) srl 32 $idy2 $id1"
  ((idy2 = id - 1))
  echo "$((id++)) sub 32 $idx $idb"
  ((lastid = id - 1))
  echo "$((id++)) or 32 $idx -$lastid"
  ((lastid = id - 1))
  echo "$((id++)) sra 32 $lastid $id31"
  ((idt = id - 1))
  echo "$((id++)) and 32 $idb $idt"
  ((lastid = id - 1))
  echo "$((id++)) sub 32 $idx $lastid"
  ((idx = id - 1))
  echo "$((id++)) and 32 $idm $idt"
  ((lastid = id - 1))
  echo "$((id++)) or 32 $idy2 $lastid"
  ((idy2 = id - 1))
  echo "$((id++)) srl 32 $idm $id2"
  ((idm = id - 1))
done
echo "$((id++)) ne 1 $idy1 $idy2"
((lastid = id - 1))
echo "$((id++)) root 1 $lastid"
