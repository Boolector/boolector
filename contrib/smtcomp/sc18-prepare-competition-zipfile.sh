#!/bin/sh

# main track QF_ABV, QF_AUFBV, QF_UFBV, QF_BV, BV (with lingeling + CaDiCaL)
make clean

./configure.sh -static --cadical --lingeling --no-minisat --no-picosat -flto
make
b=`./bin/boolector -v /dev/null|grep -i version|grep -i boolector|awk '{print $(NF-1);exit}'`
l=`./bin/boolector -v /dev/null|grep -i version|grep -i lingeling|awk '{print $(NF-1);exit}'`
version=boolector-${b}-${l}
dir=/tmp/boolector-smtcomp
rm -rf $dir

archive=${version}-main.tar.gz
mkdir $dir
mkdir $dir/bin
cp bin/boolector $dir/bin
echo "#!/bin/sh

./boolector -uc --fun:preprop --prop:nprops=10000 -nadd 0 --default-cadical \$1" > $dir/bin/starexec_run_default

echo "Boolector main track configuration 2018" > $dir/starexec_description.txt
chmod +x $dir/bin/starexec_run_default
tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive

archive=${version}-application.tar.gz
mkdir $dir
mkdir $dir/bin
cp bin/boolector $dir/bin
echo "#!/bin/sh

./boolector -i -bra --declsort-bv-width=16 \$1" > $dir/bin/starexec_run_default

echo "Boolector application track configuration 2018" > $dir/starexec_description.txt
chmod +x $dir/bin/starexec_run_default
tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive
