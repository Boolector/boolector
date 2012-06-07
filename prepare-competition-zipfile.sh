#!/bin/sh
./configure -flto -static
make boolector
cp boolector run
b=`./run -v /dev/null|grep ersion|grep oolector|awk '{print $(NF-1);exit}'`
l=`./run -v /dev/null|grep ersion|grep ingeling|awk '{print $(NF-1);exit}'`
version=boolector-${b}-${l}
zipfile=${version}.zip
rm -f $zipfile
echo "--------------------------------------------------"
echo zip $zipfile run
zip $zipfile run
ls -l $zipfile
