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
cp ./contrib/smtcomp14-extwrapper/boolector-1.5.118 $dir/bin
cp ./contrib/smtcomp14-extwrapper/boolector_ext.sh $dir/bin/boolector_ext

# create starexec configurations

# configuration for QF_BV
echo "#!/bin/sh

./boolector -bra -uc \$1" > $dir/bin/starexec_run_boolector

# configuration QF_ABV justification
echo "#!/bin/sh

./boolector_ext -ju -uc \$1" > $dir/bin/starexec_run_boolectorj

# configuration QF_ABV dual propagation 
echo "#!/bin/sh

./boolector_ext -dp -uc \$1" > $dir/bin/starexec_run_boolectord

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive
