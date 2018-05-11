#!/bin/bash

if [[ $# -ne 1 ]] && [[ $# -ne 0 ]]; then
  echo "Usage: ./adler32 [-num-loops]"
  exit 1
fi

num_loops=5552
counter=0

if [[ $# -eq 1 ]]; then
  if [[ ! $num_loops -gt 0 ]]; then
    echo "num-loops must be greater than zero"
    exit 1;
  fi
  num_loops=$1;
fi

id=1

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
echo "$((id++)) srl 32 $idadler $id16"
((lastid = id - 1))
echo "$((id++)) and 32 $lastid $idhex"
((ids2 = id - 1))

for ((i = 0; i < num_loops - 1; i++))
do
echo "$((id++)) var 8 buffer_byte"$counter
((lastid = id - 1))
((counter++))
echo "$((id++)) concat 32 $idzero $lastid"
((lastid = id - 1))
echo "$((id++)) add 32 $ids1 $lastid"
((ids1 = id - 1))
echo "$((id++)) add 32 $ids1 $ids2"
((ids2 = id - 1))
done

echo "$((id++)) var 8 buffer_byte"$counter
((lastid = id - 1))
echo "$((id++)) concat 32 $idzero $lastid"
((lastid = id - 1))
echo "$((id++)) uaddo 1 $ids1 $lastid"
((iduaddo1 = id - 1))
echo "$((id++)) add 32 $ids1 $lastid"
((ids1 = id - 1))
echo "$((id++)) uaddo 1 $ids1 $ids2"
((iduaddo2 = id - 1))

echo "$((id++)) or 1 $iduaddo1 $iduaddo2"
((lastid = id - 1))
echo "$((id++)) root 1 $lastid"
