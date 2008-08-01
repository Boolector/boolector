#!/bin/bash

# http://www.ietf.org/rfc/rfc1950.txt

declare -a bytes

if [[ $# -ne 1 ]] && [[ $# -ne 0 ]]; then
  echo "Usage: ./adler32 [-num-loops]"
  exit 1
fi

num_loops=5552

if [[ $# -eq 1 ]]; then
  num_loops=$1;
fi

id=1
bytescounter=0

echo "$((id++)) constd 32 65521"
((idbase = id - 1))
echo "$((id++)) one 32"
((idone = id - 1))
echo "$((id++)) zero 24"
((idzero = id - 1))
echo "$((id++)) constd 5 16"
((id16 = id - 1))
echo "$((id++)) var 32 adler"
((idadler = id - 1))
echo "$((id++)) consth 32 ffff"
((idhex = id - 1))
echo "$((id++)) and 32 $idadler $idhex"
((ids1 = id - 1))
((ids1initial = ids1))
echo "$((id++)) srl 32 $idadler $id16"
((lastid = id - 1))
echo "$((id++)) and 32 $lastid $idhex"
((ids2 = id - 1))
((ids2initial = ids2))

for ((i = 0; i < num_loops; i++))
do
echo "$((id++)) var 8 buffer_byte"$bytescounter
((lastid = id - 1))
echo "$((id++)) concat 32 $idzero $lastid"
((lastid = id - 1))
bytes[bytescounter]=$lastid
((bytescounter++))
echo "$((id++)) add 32 $ids1 $lastid"
((lastid = id - 1))
echo "$((id++)) urem 32 $lastid $idbase"
((ids1 = id - 1))
echo "$((id++)) add 32 $ids1 $ids2"
((lastid = id - 1))
echo "$((id++)) urem 32 $lastid $idbase"
((ids2 = id - 1))
done

echo "$((id++)) sll 32 $ids2 $id16"
((lastid = id - 1))
echo "$((id++)) add 32 $lastid $ids1"
((idresult1 = id - 1))

ids1=$ids1initial
ids2=$ids2initial
bytescounter=0

for ((i = 0; i < num_loops; i++))
do
echo "$((id++)) add 32 $ids1 ${bytes[$bytescounter]}"
((bytescounter++))
((ids1 = id - 1))
echo "$((id++)) add 32 $ids1 $ids2"
((ids2 = id - 1))
done


echo "$((id++)) urem 32 $ids1 $idbase"
((ids1 = id - 1))
echo "$((id++)) urem 32 $ids2 $idbase"
((ids2 = id - 1))

echo "$((id++)) sll 32 $ids2 $id16"
((lastid = id - 1))
echo "$((id++)) add 32 $lastid $ids1"
((idresult2 = id - 1))

echo "$((id++)) eq 1 $idadler $idone"
echo "$((id++)) eq 1 $idresult1 $idresult2"
((lastid = id - 1))
echo "$((id++)) and 1 -$lastid $((lastid - 1))"
((lastid = id - 1))
echo "$((id++)) root 1 $lastid"


