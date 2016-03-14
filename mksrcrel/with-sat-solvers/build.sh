#!/bin/sh

die () {
  echo "*** build.sh: $*" 1>&2
  exit 1
}

for component in boolector picosat precosat lingeling minisat
do
  archive="`ls archives/${component}-*.tar.gz 2>/dev/null`"
  case x$archive in
    xarchives/$component*) ;;
    *) continue;;
  esac
  name=`basename $archive .tar.gz`
  tar xf $archive
  rm -rf $component
  mv $name $component
  echo "extracted $component"
done

if [ -d minisat ]
then
  echo "building minisat"
  cd minisat
  make r >/dev/null || die "'make r' failed in 'minisat'"
  cd ..
fi

for component in picosat precosat lingeling boolector
do
  [ -d $component ] || continue
  echo "building $component"
  cd $component
  if [ -f configure ]; then configure=configure; else configure=configure.sh; fi
  ./$configure >/dev/null || die "'./configure' failed in '$component'"
  make >/dev/null || die "'make' failed in '$component'"
  cd ..
done
