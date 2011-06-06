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
echo "building picosat"
cd picosat
./configure -O >/dev/null || exit 1
make >/dev/null || exit 1
