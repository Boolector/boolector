#!/bin/sh
revision=`cat VERSION`-`cat ../lingeling/VERSION`
name=boolector-$revision
dir=/tmp/$name
tar=/tmp/${name}.tar.bz2
rm -rf $dir $tar
mkdir $dir
install -s boolector $dir/
cat >$dir/run <<EOF
#!/bin/sh
exec boolector \$*
EOF
chmod 755 $dir/run
cd /tmp
tar jcf $tar $name
rm -rf $dir
ls -l $tar
