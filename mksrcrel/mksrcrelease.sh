#!/bin/sh

force=no

die () {
  echo "*** mksrcrelease.sh: $*" 1>&2
  exit 1
}

[ -f src/boolector.h ] || \
die "can not find 'boolector.h' (call from boolector base directory)"

while [ $# -gt 0 ]
do
  case $1 in
    -h) echo "usage: mksrcrelease.sh [-f][-h][-t]";exit 0;;
    -f) force=yes;;
    *) die "invalid command line option '$1'";;
  esac
  shift
done

if [ ! -d doc/_build/html ]; then
  die "can not find documentation. generate documentation with 'make html' in directory ../doc/"
fi

LC_TIME="en_US.UTF-8"
export LC_TIME

date=`date +%y%m%d`
version=`cat VERSION`
gitid=`./getgitid.sh|sed -e 's,^.*\.,,' -e 's,\",,' -e 's,^\(.......\).*,\1,'`

id="$version-$gitid-$date"
name=boolector-$id
dir="/tmp/$name"

if [ -d $dir ]
then
  [ $force = no ] && die "$dir already exists (use '-f')"
fi

rm -rf $dir
mkdir $dir || exit 1

mkdir $dir/src || exit 1

cp -p \
  VERSION \
  COPYING \
  NEWS \
  README \
  configure.sh \
$dir/

cd src

cp -p --parents \
  boolector.[ch] \
  boolectormain.[ch] \
  boolectormc.[ch] \
  aigprop.[ch] \
  `ls btor*.[ch]|grep -v btoribv.h` \
  `ls btor*.cc |grep -v btoribv|grep -v btorimc` \
  btorfmt/LICENSE \
  btorfmt/btorfmt.[ch] \
  btorfmt/configure.sh \
  btorfmt/makefile.in \
$dir/src

for subdir in dumper mcapi normalizer parser sat simplifier utils
do
  mkdir $dir/src/$subdir/
  cp -p $subdir/*.[ch] $dir/src/$subdir/
done
cp -p sat/*.cc $dir/src/sat/

mkdir $dir/src/api/
mkdir $dir/src/api/python
for file in boolector_py.h boolector_py.c boolector.pyx btorapi.pxd \
	    api_usage_examples.py README
do
  cp -p api/python/$file $dir/src/api/python/
done

cp -p \
  BitVector.hh \
  btoribv.hh \
  btoribv.cc \
  btorimc.cc \
$dir/src/

cd ..

mkdir $dir/doc
cp -pr \
  doc/_build/html/* \
$dir/doc/

tar cf - \
  examples/array/*.c \
  examples/array/makefile \
  examples/btormc \
  examples/bv/*.c \
  examples/bv/makefile \
  examples/Makefile \
  examples/makefile.common | \
( cd $dir; tar xf -; )

# remove tabs from source files and replace them with whitespaces
# one tab -> 8 whitespaces
for f in `find $dir -type f -and \( -name "*.c" -o -name "*.h" -o  -name "*.cc" \)`
do
  sed -i 's/\t/        /g' $f
done

cp -p \
  makefile.in \
  ibv.mk \
  mbt.mk \
  mc.mk \
$dir/

date=`date`
version=`cat VERSION`
sed -e 's,@VERSION@,'"$version," \
    -e 's,@DATE@,'"$date," \
mksrcrel/README > $dir/README

sed -e "s,^BTOR_DEF_DATE=.*,BTOR_DEF_DATE=\"$date\"," \
    -e "s,^BTOR_DEF_VERSION=.*,BTOR_DEF_VERSION=\"$version\"," \
    -e "s,^BTOR_DEF_ID=.*,BTOR_DEF_ID=\"`./getgitid.sh`\"," \
    mkconfig.sh > $dir/mkconfig.sh

chmod 755 $dir/mkconfig.sh

cd /tmp/
rm -f $name.tar.gz
tar zcf $name.tar.gz $name
ls -l /tmp/$name.tar.gz | awk '{print $5, $NF}'
rm -rf $dir
