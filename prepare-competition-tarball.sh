#!/bin/sh
revision=`cat VERSION`-`cat ../lingeling/VERSION`
name=boolector-$revision
dir=/tmp/$name
tar=/tmp/${name}.tar.bz2
rm -rf $dir $tar
mkdir $dir
strip boolector
cp boolector $dir/
cat >$dir/run <<EOF
#!/bin/sh
exec ./boolector \$*
EOF
chmod 755 $dir/run
cp $HOME/papers/boolector-sc2011/boolector-sc2011.pdf $dir
cd $dir
tar jcf $tar *
rm -rf $dir
ls -l $tar
