#!/bin/sh
make clean

./configure.sh -static --only-lingeling -flto
make
b=`./bin/boolector -v /dev/null|grep -i version|grep -i boolector|awk '{print $(NF-1);exit}'`
l=`./bin/boolector -v /dev/null|grep -i version|grep -i lingeling|awk '{print $(NF-1);exit}'`
version=boolector-${b}-${l}
dir=/tmp/boolector-smtcomp
rm -rf $dir

# configuration QF_ABV, QF_UFBV, QF_AUFBV, BV, QF_BV
archive=${version}-main.tar.gz
mkdir $dir
mkdir $dir/bin
cp bin/boolector $dir/bin
echo "#!/bin/sh

./boolector -uc --fun:preprop --prop:nprops=10000 \$1" > $dir/bin/starexec_run_boolector

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive

make clean
./configure.sh -static --only-cadical -flto
make
b=`./bin/boolector -v /dev/null|grep -i version|grep -i boolector|awk '{print $(NF-1);exit}'`
version=boolector-${b}
dir=/tmp/boolector-smtcomp
rm -rf $dir

# configuration QF_BV with CaDiCaL
archive=${version}-cadical-main-qf_bv.tar.gz
mkdir $dir
mkdir $dir/bin
cp bin/boolector $dir/bin
echo "#!/bin/sh

./boolector -uc --fun:preprop --prop:nprops=10000 \$1" > $dir/bin/starexec_run_boolector

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive
