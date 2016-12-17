#!/bin/sh
die () {
  echo "*** mksrcrelease-with-sat-solver.sh: $*" 1>&2
  exit 1
}
minisat=yes
while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) 
      echo "usage: mksrcrelease-with-sat-solvers.sh [-h][--no-minisat]"
      exit 0
      ;;
    --no-minisat)
      minisat=no
      ;;
    *) 
      die "invalid command line option"
      ;;
  esac
  shift
done
[ -f src/boolector.h ] || die "need to be called from 'src'"
cd mksrcrel/with-sat-solvers
version=`cat ../../VERSION`
name=boolector-${version}-with-sat-solvers
tmp=/tmp/$name
log=$tmp.log
tar=${tmp}.tar.gz
rm -rf $tmp $tar $log
mkdir $tmp || exit 1
cp build.sh clean.sh makefile $tmp
date=`date`
sed -e 's,@VERSION@,'"$version," \
    -e 's,@DATE@,'"$date," \
README > $tmp/README
mkdir $tmp/archives || exit 1
cd ../..
./mksrcrel/mksrcrelease.sh >> $log || exit 1
boolector=`grep boolector- $log|awk '{print $NF}'`
mv $boolector $tmp/archives
for solver in picosat lingeling
do
  cd ../$solver
  if [ -f mkrelease ]
  then
    ./mkrelease >> $log
  else
    ./mkrelease.sh >> $log
  fi
  archive=`grep ${solver}- $log|awk '{print $NF}'`
  mv $archive $tmp/archives
done
if [ $minisat = yes ]
then
  cd ../minisat
  date=`date +%Y%m%d`
  git archive --format=tar --prefix=minisat-${date}/ HEAD | \
    gzip -c > $tmp/archives/minisat-${date}.tar.gz
fi
cd /tmp/
tar zcf $tar $name
ls -l $tar|awk '{print $5, $NF}'
rm -rf $tmp $log
