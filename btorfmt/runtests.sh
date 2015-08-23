#!/bin/sh
cd `dirname $0` || exit 1
cd tests || exit 1
runtest () {
  echo -n "\r                            \r$1 ..."
  rm -f $1.log
  ../catbtor $1.in 1>$1.log 2>&1
  if diff $1.log $1.out 1>/dev/null 2>/dev/null
  then
    echo -n " ok\r"
    ok=`expr $ok + 1`
  else
    echo " failed"
    failed=`expr $failed + 1`
  fi
}
ok=0
failed=0
for i in *.in
do
  name=`basename $i .in`
  runtest $name
done
echo "$ok ok, $failed failed"
