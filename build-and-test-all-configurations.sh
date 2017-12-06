#!/bin/sh
msg () {
  echo "[`basename $0`] $*" | tee -a $log
}
die () {
  echo "*** `basenae $0`: $*" | tee -a $log 1>&2
  exit 1
}
build () {
  CC=$1
  CXX=$2
  shift;shift;
  msg "CC=$CC CXX=$CXX ./configure.sh $*"
  if [ -f makefile ]
  then
    make clean >> $log || die "'make clean' failed"
  fi
  CC=$CC CXX=$CXX ./configure.sh $* >> $log || die "'configure.sh' failed"
  make >> $log || die "'make' failed"
  [ -f bin/test ] || die "'./bin/test' not found"
  ./bin/test >> $log || die "'./bin/test' failed"
  passed=`expr $passed + 1`
}


msg "begin `date`"

log="/tmp/`basename $0 .sh`.log"
rm -f $log
msg "logging stdout in '$log'"

# we keep these on seperate lines to be able to move
# failing configurations to the top for debugging

build clang clang++ --only-lingeling -g
build clang clang++ --only-lingeling
build clang clang++ --only-lingeling -c
build clang clang++ --only-lingeling -l

build gcc g++ --only-lingeling
build gcc g++ --only-lingeling -g
build gcc g++ --only-lingeling -c
build gcc g++ --only-lingeling -l

msg "all $passed configurations passed"
msg "end `date`"
