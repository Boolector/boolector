#!/bin/sh
revision=`cat VERSION`-`cat ../lingeling/VERSION`
name=boolector-$revision
dir=/tmp/$name
tar=/tmp/${name}.tar.bz2
rm -rf $dir $tar
mkdir $dir
cp boolector $dir/
tar jcf $tar $dir
rm -rf $dir
ls -l $tar
