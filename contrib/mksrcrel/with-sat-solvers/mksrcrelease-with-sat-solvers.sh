#!/bin/sh

die () {
  echo "*** mksrcrelease-with-sat-solver.sh: $*" 1>&2
  exit 1
}

[ -f src/boolector.h ] || \
  die "can not find 'boolector.h' (call from boolector base directory)"

readonly BASEDIR=$(pwd)
readonly BTOR2TOOLSDIR=$BASEDIR/../btor2tools
[ -e $BTOR2TOOLSDIR ] || die "can not find Btor2Tools"


minisat=yes
onlylingeling=no
while [ $# -gt 0 ]
do
  case $1 in
    -h|--help)
      echo -n "usage: mksrcrelease-with-sat-solvers.sh "
      echo    "[-h][--no-minisat] [--only-lingeling]"
      exit 0
      ;;
    --no-minisat)
      minisat=no
      ;;
    --only-lingeling)
      onlylingeling=yes
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
if [ $onlylingeling = yes ]
then
  name=boolector-${version}-with-lingeling
else
  name=boolector-${version}-with-sat-solvers
fi
tmp=/tmp/$name
log=$tmp.log
tar=${tmp}.tar.xz
rm -rf $tmp $tar $log
mkdir $tmp || exit 1

cp build.sh clean.sh makefile $tmp
date=`date`
if [ $onlylingeling = yes ]
then
  satsolversinfo="Lingeling"
else
  satsolversinfo="supported SAT solvers"
fi
sed -e 's,@VERSION@,'"$version," \
    -e 's,@DATE@,'"$date," \
    -e 's,@SATSOLVERS@,'"$satsolversinfo," \
README > $tmp/README
mkdir $tmp/archives || exit 1

# Boolector
cd $BASEDIR
./contrib/mksrcrel/mksrcrelease.sh >> $log || exit 1
boolector=`grep boolector- $log|awk '{print $NF}'`
mv $boolector $tmp/archives

# Btor2Tools
cd $BTOR2TOOLSDIR
./mksrcrelease.sh >> $log
archive=`grep btor2tools- $log|awk '{print $NF}'`
mv $archive $tmp/archives

# SAT solvers
if [ $onlylingeling = yes ]
then
  satsolvers="lingeling"
else
  satsolvers="picosat lingeling cadical"
fi
for solver in $satsolvers
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

# Create archive
cd /tmp/
tar Jcf $tar $name
ls -l $tar|awk '{print $5, $NF}'
rm -rf $tmp $log
