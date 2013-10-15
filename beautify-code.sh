#!/bin/sh
for i in *.h *.c */*.c */*.h */*/*.c */*/*.h
do
  rm -f $i~ || exit 0
  expand $i | unexpand > $i~ || exit 0
  mv $i~ $i || exit 0
  sed -i -e 's,[ 	]*$,,g' $i || exit 0
done
