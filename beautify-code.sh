#!/bin/sh
for i in *.h *.c
do
  rm -f $i~ || exit 0
  unexpand $i > $i~ || exit 0
  mv $i~ $i || exit 0
  sed -i -e 's,[ 	]*$,,g' $i || exit 0
done
