#!/bin/sh
make clean
./configure -static #-flto -static
make boolector
b=`./boolector -v /dev/null|grep -i version|grep -i boolector|awk '{print $(NF-1);exit}'`
l=`./boolector -v /dev/null|grep -i version|grep -i lingeling|awk '{print $(NF-1);exit}'`
version=boolector-${b}-${l}
archive=${version}.tar.gz
dir=/tmp/boolector-smtcomp
rm -rf $dir

mkdir $dir
mkdir $dir/bin
cp boolector $dir/bin

# create starexec configurations

# configuration for QF_BV
echo "#!/bin/sh

./boolector -bra -uc \$1" > $dir/bin/starexec_run_boolector_qf_bv

# configuration QF_ABV justification
echo "#!/bin/sh

./boolector -uc \$1" > $dir/bin/starexec_run_boolector_qf_aufbv

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive
