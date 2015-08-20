#!/bin/sh
debug=no
while [ $# -gt 0 ]
do
  case $1 in
    -h) echo "usage: configure.sh [-h][-g]" 1>&2; exit 1;;
    -g) debug=yes;;
    *) echo "*** configure.sh: invalid option '$1'" 1>&2 exit 1;;
  esac
  shift
done
CC=gcc
if [ $debug = yes ]
then
  CFLAGS="-Wall -g3"
else
  CFLAGS="-Wall -O3 -DNDEBUG"
fi
echo "$CC $CFLAGS"
rm -f makefile
sed -e "s,@CC@,$CC," -e "s,@CFLAGS@,$CFLAGS," makefile.in > makefile
