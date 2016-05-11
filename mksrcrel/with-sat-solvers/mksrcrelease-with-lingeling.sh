#!/bin/sh
die () {
  echo "*** mksrcrelease-with-lingeling.sh: $*" 1>&2
  exit 1
}
[ -f ../../src/boolector.h ] || \
die "need to be called from 'mksrcrel/with-sat-solvers"
minisat=yes
while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) 
      echo "usage: mksrcrelease-with-lingeling.sh [-h]"
      exit 0
      ;;
    *) 
      die "invalid command line option"
      ;;
  esac
  shift
done
btorversion=`cat ../../VERSION`
lglversion=`cat ../../../lingeling/VERSION`
name=boolector-${btorversion}-with-lingeling-${lglversion}
tmp=/tmp/$name
log=$tmp.log
tar=${tmp}.tar.bz2
rm -rf $tmp $tar $log
mkdir $tmp || exit 1
cp makefile.lingeling $tmp/makefile
cp README.lingeling $tmp/README
mkdir $tmp/archives || exit 1
cd ../..
./mksrcrel/mksrcrelease.sh >> $log
boolector=`grep boolector- $log|awk '{print $NF}'`
mv $boolector $tmp/archives
for solver in lingeling
do
  cd ../$solver
  ./mkrelease.sh >> $log
  archive=`grep ${solver}- $log|awk '{print $NF}'`
  mv $archive $tmp/archives
done
cd /tmp/
tar jcf $tar $name
ls -l $tar|awk '{print $5, $NF}'
rm -rf $tmp $log
