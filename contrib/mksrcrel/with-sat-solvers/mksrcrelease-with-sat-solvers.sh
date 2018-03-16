#!/bin/sh
die () {
  echo "*** mksrcrelease-with-sat-solver.sh: $*" 1>&2
  exit 1
}
[ -f src/boolector.h ] || \
  die "can not find 'boolector.h' (call from boolector base directory)"
BASEDIR=$(pwd)

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

cd contrib/mksrcrel/with-sat-solvers
version=`cat $BASEDIR/VERSION`
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
cd $BASEDIR
./contrib/mksrcrel/mksrcrelease.sh >> $log || exit 1
boolector=`grep boolector- $log|awk '{print $NF}'`
mv $boolector $tmp/archives
for solver in picosat lingeling cadical
do
  cd $BASEDIR/../$solver
  if [ -f mkrelease ]
  then
    ./mkrelease >> $log
  elif [ -f mkrelease.sh ]
  then
    ./mkrelease.sh >> $log
  else # CaDiCaL
    ./scripts/make-src-release.sh >> $log
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
