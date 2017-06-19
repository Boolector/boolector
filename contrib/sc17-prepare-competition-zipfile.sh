#!/bin/sh
make clean
./configure.sh -static --only-lingeling -flto
make
b=`./bin/boolector -v /dev/null|grep -i version|grep -i boolector|awk '{print $(NF-1);exit}'`
l=`./bin/boolector -v /dev/null|grep -i version|grep -i lingeling|awk '{print $(NF-1);exit}'`
version=boolector-${b}-${l}
dir=/tmp/boolector-smtcomp
rm -rf $dir

# create starexec configurations

## configuration for QF_BV
#archive=${version}-qf_bv.tar.gz
#mkdir $dir
#mkdir $dir/bin
#cp boolector $dir/bin
#echo "#!/bin/sh
#
#./boolector -bra -uc \$1" > $dir/bin/starexec_run_boolector_qf_bv
#
#tar -C $dir -zcf $archive .
#rm -rf $dir
#ls -l $archive

# configuration QF_ABV, QF_UFBV, QF_AUFBV, BV, UFBV, QF_BV
archive=${version}-main.tar.gz
mkdir $dir
mkdir $dir/bin
cp bin/boolector $dir/bin
echo "#!/bin/sh

./boolector -uc \$1" > $dir/bin/starexec_run_boolector

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive
