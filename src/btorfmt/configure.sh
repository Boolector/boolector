#!/bin/sh
debug=no
coverage=no
while [ $# -gt 0 ]
do
  case $1 in
    -h) echo "usage: configure.sh [-h][-g][-c]" 1>&2; exit 1;;
    -g) debug=yes;;
    -c) coverage=yes;;
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
[ $coverage = yes ] && CFLAGS="$CFLAGS -fprofile-arcs -ftest-coverage"
echo "$CC $CFLAGS"
rm -f makefile
BINDIR="bin"
BUILDIR="build"
sed \
  -e "s,@CC@,$CC," \
  -e "s,@CFLAGS@,$CFLAGS," \
  -e "s,@BUILDIR@,$BUILDIR," \
  -e "s,@BINDIR@,$BINDIR," \
  makefile.in > makefile
echo "makefile generated"
