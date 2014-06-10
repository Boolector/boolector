#!/bin/sh
make clean
./configure -static #-flto -static
make boolector
b=`./boolector -v /dev/null|grep ersion|grep oolector|awk '{print $(NF-1);exit}'`
l=`./boolector -v /dev/null|grep ersion|grep ingeling|awk '{print $(NF-1);exit}'`
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

./boolector -bra \$1" > $dir/bin/starexec_run_boolector

# configuration QF_AUFBV justification
echo "#!/bin/sh

./boolector -ju \$1" > $dir/bin/starexec_run_boolectorj

# configuration QF_AUFBV dual propagation 
echo "#!/bin/sh

./boolector -dp \$1" > $dir/bin/starexec_run_boolectord

tar -C $dir -zcf $archive .
rm -rf $dir
ls -l $archive
