#!/bin/sh
msg () {
  echo "[`basename $0`] $*" | tee -a $log
}
die () {
  echo "*** `basename $0`: $*" | tee -a $log | tee -a $err 1>&2
  exit 1
}

[ -f src/boolector.h ] || \
  die "can not find 'boolector.h' (call from boolector base directory)"

build () {
  CC=$1
  CXX=$2
  shift;shift;
  msg "CC=$CC CXX=$CXX ./configure.sh $*"
  if [ -f makefile ]
  then
    make clean 1>> $log 2>>$err || die "'make clean' failed"
  fi
  CC=$CC CXX=$CXX ./configure.sh $* 1>> $log 2>>$err || \
    die "'configure.sh' failed"
  make -j`nproc` 1>> $log 2>>$err || die "'make' failed"
  [ -f bin/test ] || die "'./bin/test' not found"
  ./bin/test 1>> $log 2>>$err || die "'./bin/test' failed"
  passed=`expr $passed + 1`
}

msg "begin `date`"

log="/tmp/`basename $0 .sh`.log"
err="/tmp/`basename $0 .sh`.err"
rm -f $log $err

msg "logging 'stdout' to '$log'"
msg "logging 'stderr' to '$err'"
msg "warning and error messages on 'stderr' are also shown here"

# keep these on seperate lines in order to be able to
# copy failing configurations to the top for debugging

build clang clang++ --only-lingeling
build clang clang++ --only-lingeling -g
build clang clang++ --only-lingeling -c
build clang clang++ --only-lingeling -l

build gcc g++ --only-lingeling
build gcc g++ --only-lingeling -g
build gcc g++ --only-lingeling -c
build gcc g++ --only-lingeling -l

msg "all $passed configurations passed"
msg "end `date`"
