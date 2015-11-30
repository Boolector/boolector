#!/bin/sh
make clean
./configure -static --only-lingeling #-flto -static
make boolector
b=`./boolector -v /dev/null|grep -i version|grep -i boolector|awk '{print $(NF-1);exit}'`
l=`./boolector -v /dev/null|grep -i version|grep -i lingeling|awk '{print $(NF-1);exit}'`
version=boolector-${b}-${l}
dir=/tmp/boolector-smtcomp
rm -rf $dir

# create starexec configurations

# configuration for QF_BV
archive=${version}-qf_bv.tar.gz
mkdir $dir
mkdir $dir/bin
cp boolector $dir/bin
echo "#!/bin/sh

./boolector -bra -uc \$1" > $dir/bin/starexec_run_boolector_qf_bv

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive

# configuration for QF_BV incremental
archive=${version}-qf_bv_inc.tar.gz
mkdir $dir
mkdir $dir/bin
cp boolector $dir/bin
echo "#!/bin/sh

./boolector -i -bra -uc -sp=0 \$1" > $dir/bin/starexec_run_boolector_qf_bv_inc

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive

# configuration QF_ABV, QF_UFBV, QF_AUFBV
archive=${version}-qf_aufbv.tar.gz
mkdir $dir
mkdir $dir/bin
cp boolector $dir/bin
echo "#!/bin/sh

./boolector -uc -es=0 \$1" > $dir/bin/starexec_run_boolector_qf_aufbv

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive
