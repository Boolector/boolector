#!/bin/bash
if [[ $# -ne 2 ]]; then
  echo "Usage: ./bubblesortnext <bit-width> <power>"
  exit
fi
bw=$1
power=$2
id=1
((size=2 ** power))
echo "$((id++)) array $bw $power"
for ((i=0;i<size;i++))
do
  echo "$((id++)) constd $power $i"
  if [[ i -eq 1 ]]; then
    ((idone=id-1))
  fi
done
((idlastconst=id-1))
echo ""
echo "$((id++)) var $power counter"
((idvar=id-1))
echo "$((id++)) add $power $idvar $idone"
((lastid=id-1))
echo "$((id++)) next $power $idvar $lastid"
echo ""

index=2
array=1
for ((i=0;i<size-1;i++))
do
  echo "$((id++)) read $bw $array $index"
  ((idread1=id-1))
  echo "$((id++)) read $bw $array $((index + 1))"
  ((idread2=id-1))
  echo "$((id++)) ugt 1 $idread1 $idread2"
  ((idugt=id-1))
  echo "$((id++)) write $bw $array $((index + 1)) $idread1"
  ((lastid=id-1))
  echo "$((id++)) write $bw $lastid $index $idread2"
  ((lastid=id-1))
  echo "$((id++)) cond $bw $idugt $lastid $array"
  ((array=id-1))
  ((index++))
done
echo "$((id++)) next $bw 1 $array"
echo ""
echo "$((id++)) eq 1 $idvar $idlastconst"
((ideq=id-1))
echo "$((id++)) var $power pos1"
((idindex1=id-1))
echo "$((id++)) var $power pos2"
((idindex2=id-1))
echo "$((id++)) ult 1 $idindex1 $idindex2"
((idult=id-1))
echo "$((id++)) read $bw 1 $idindex1"
((idread1=id-1))
echo "$((id++)) read $bw 1 $idindex2"
((idread2=id-1))
echo "$((id++)) ugt 1 $idread1 $idread2"
((idugt=id-1))
echo "$((id++)) and 1 $ideq $idult"
((lastid=id-1))
echo "$((id++)) and 1 $idugt $lastid"
((lastid=id-1))
echo "$((id++)) root 1 $lastid"
