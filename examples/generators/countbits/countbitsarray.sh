#!/bin/bash
# Count bits pop_array(A, n) algorithm
# hacker's delight, page 71
# we verifiy it by cross-checking with the obvios method of counting bits
#    for (s = i = 0; i < n; i++)
#      if (x & (1 << i))
#        s++;
# for each element of A. The result is summed up.

function dec2bin
{
  local x=$1
  local len=$2
  local ret="`echo "ibase=10; obase=2; $x" | bc`"
  local result=`printf "%0${len}d" $ret`
  echo $result
}

function log_2
{
  local result=0
  local x=$1
  while [[ "$x" -gt 1 ]]
  do  
      ((x >>= 1))
      ((result++))
  done 
  echo $result
}

function is_power_of_2
{
  local x=$1
  ((x = x & (x - 1)))
  if [[ x -eq 0 ]]; then
    echo 1
  else
    echo 0
  fi
}

if [[ $# -ne 1 ]]; then
  echo "Usage ./countbitsarray <size>"
  exit 1
fi

size=$1
if [[ "$size" -lt 2 ]] || [[ ! `is_power_of_2 $size` -eq 1 ]]; then
  echo "Size must be a power of 2 >= 2"
  exit 1
fi
sizelog=`log_2 $size`
id=1

echo "$((id++)) zero 32"
((idzero = id - 1))
((idsum = idzero))
echo "$((id++)) one 32"
((idone = id - 1))
echo "$((id++)) one 5"
((idone5 = id - 1))
echo "$((id++)) constd 5 2"
((idtwo5 = id - 1))
echo "$((id++)) constd 5 4"
((idfour5 = id - 1))
echo "$((id++)) constd 5 8"
((ideight5 = id - 1))
echo "$((id++)) constd 5 16"
((idsixteen5 = id - 1))
echo "$((id++)) consth 32 55555555"
((idhex55555555 = id - 1))
echo "$((id++)) consth 32 33333333"
((idhex33333333 = id - 1))
echo "$((id++)) consth 32 0f0f0f0f"
((idhex0f0f0f0f = id - 1))
echo "$((id++)) consth 32 00ff00ff"
((idhex00ff00ff = id - 1))
echo "$((id++)) consth 32 0000ffff"
((idhex0000ffff = id - 1))
echo "$((id++)) array 32 $sizelog"
((idarray = id - 1))
for ((i = 0; i < $size; i += 31))
do
  ((ip31 = i + 31))
  if [[ $size -lt ip31 ]]; then
    lim=$size
  else
    lim=$ip31;
  fi
  ((ids8 = idzero))
  for ((j = i; j < $lim; j++))
  do
    binj="`dec2bin $j $sizelog`"
    echo "$((id++)) const $sizelog $binj"
    ((lastid = id - 1))
    echo "$((id++)) read 32 $idarray $lastid"
    ((idx = id - 1))
    echo "$((id++)) srl 32 $idx $idone5"
    ((lastid = id - 1))
    echo "$((id++)) and 32 $lastid $idhex55555555"
    ((lastid = id - 1))
    echo "$((id++)) sub 32 $idx $lastid"
    ((idx = id - 1))
    echo "$((id++)) srl 32 $idx $idtwo5" 
    ((lastid = id - 1))
    echo "$((id++)) and 32 $lastid $idhex33333333"
    ((idtemp = id - 1))
    echo "$((id++)) and 32 $idx $idhex33333333"
    ((lastid = id - 1))
    echo "$((id++)) add 32 $idtemp $lastid"
    ((idx = id - 1))
    echo "$((id++)) srl 32 $idx $idfour5"
    ((lastid = id - 1))
    echo "$((id++)) add 32 $idx $lastid"
    ((lastid = id - 1))
    echo "$((id++)) and 32 $lastid $idhex0f0f0f0f"
    ((idx = id - 1))
    echo "$((id++)) add 32 $ids8 $idx"
    ((ids8 = id - 1))
  done
  echo "$((id++)) srl 32 $ids8 $ideight5"
  ((lastid = id - 1))
  echo "$((id++)) and 32 $lastid $idhex00ff00ff"
  ((idtemp = id - 1))
  echo "$((id++)) and 32 $ids8 $idhex00ff00ff"
  ((lastid = id - 1))
  echo "$((id++)) add 32 $idtemp $lastid"
  ((idx = id - 1))
  echo "$((id++)) srl 32 $idx $idsixteen5"
  ((idtemp = id - 1))
  echo "$((id++)) and 32 $idx $idhex0000ffff"
  ((lastid = id - 1))
  echo "$((id++)) add 32 $idtemp $lastid"
  ((idx = id - 1))
  echo "$((id++)) add 32 $idsum $idx"
  ((idsum = id - 1))
done
((idresult1 = idsum))

((idresult2 = idzero))
for ((i = 0; i < $size; i++))
do
  binrep="`dec2bin $i $sizelog`"
  echo "$((id++)) const $sizelog $binrep"
  ((idindex = id - 1))
  echo "$((id++)) read 32 $idarray $idindex"
  ((idx = id - 1))
  ((idsum = idzero))
  for ((j = 0; j < 32; j++))
  do
    echo "$((id++)) constd 5 $j"
    ((lastid = id - 1))
    echo "$((id++)) sll 32 $idone $lastid"
    ((lastid = id - 1))
    echo "$((id++)) and 32 $idx $lastid"
    ((lastid = id - 1))
    echo "$((id++)) ne 1 $lastid $idzero"
    ((idcond = id - 1))
    echo "$((id++)) inc 32 $idsum"
    ((lastid = id - 1))
    echo "$((id++)) cond 32 $idcond $lastid $idsum"
    ((idsum = id - 1))
  done
  echo "$((id++)) add 32 $idresult2 $idsum"
  ((idresult2 = id - 1))
done

echo "$((id++)) eq 1 $idresult1 $idresult2"
((lastid = id - 1))
echo "$((id++)) root 1 -$lastid"
