#!/bin/sh

for component in boolector picosat precosat lingeling
do
  archive=`ls archives/${component}-*.tar.gz`
  name=`basename $archive .tar.gz`
  tar xf $archive
  rm -rf $component
  mv $name $component
  echo "extracted $component"
done

for component in picosat precosat lingeling
do
  echo "building $component"
  cd $component
  ./configure -O >/dev/null || exit 1
  make >/dev/null || exit 1
  cd ..
done

echo "building boolector"
cd boolector
./configure -precosat -lingeling >/dev/null || exit 1
make >/dev/null || exit 1
cd ..
