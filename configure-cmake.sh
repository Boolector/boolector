#!/bin/sh
#--------------------------------------------------------------------------#

SCRIPTDIR=`dirname "$(readlink -f $0)"`
BUILDDIR=$SCRIPTDIR/cmake-build

#--------------------------------------------------------------------------#

asan=no
debug=no
check=no
log=no
shared=no

lingeling=unknown
minisat=unknown
picosat=unknown
cadical=unknown

gcov=no
gprof=no
python=no
timestats=no

flags=none

#--------------------------------------------------------------------------#

usage () {
cat <<EOF
usage: ./configure.sh [<option> ...]

where <option> is one of the following:

  -h, --help        print this message and exit

  -g                compile with debugging support
  -f...|-m...       add compiler options

  --shared          shared library

  -l                compile with logging support (default for '-g')
  -c                check assertions even in optimized compilation
  --asan            compile with -fsanitize=address -fsanitize-recover=address
  --gcov            compile with -fprofile-arcs -ftest-coverage
  --gprof           compile with -pg

  --python          compile python API
  --time-stats      compile with time statistics

By default all supported SAT solvers available are used and linked.
If explicitly enabled, configuration will fail if the SAT solver library 
can not be found.

  --cadical         use and link with CaDiCaL
  --lingeling       use and link with Lingeling
  --minisat         use and link with MiniSAT
  --picosat         use and link with PicoSAT

  --no-cadical      do not use CaDiCaL
  --no-lingeling    do not use Lingeling
  --no-minisat      do not use MiniSAT
  --no-picosat      do not use PicoSAT

  --only-cadical    only use CaDiCaL
  --only-lingeling  only use Lingeling
  --only-minisat    only use MiniSAT
  --only-picosat    only use PicoSAT
EOF
  exit 0
}

#--------------------------------------------------------------------------#

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}

msg () {
  echo "[configure.sh] $*"
}

#--------------------------------------------------------------------------#

while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) usage;;

    -g) debug=yes;;
    -f*|-m*) if [ $flags = none ]; then flags=$1; else flags="$flags $1"; fi;;

    --shared) shared=yes;;

    -l) log=yes;;
    -c) check=yes;;
    --asan) asan=yes;;
    --gcov) gcov=yes;;
    --gprof) gprof=yes;;

    --python) python=yes;;
    --time-stats) timestats=yes;;

    --cadical) cadical=yes;;
    --lingeling) lingeling=yes;;
    --minisat) minisat=yes;;
    --picosat) picosat=yes;;

    --no-cadical) cadical=no;;
    --no-lingeling) lingeling=no;;
    --no-minisat) minisat=no;;
    --no-picosat) picosat=no;;

    --only-cadical) lingeling=no;minisat=no;picosat=no;cadical=yes;;
    --only-lingeling) lingeling=yes;minisat=no;picosat=no;cadical=no;;
    --only-minisat) lingeling=no;minisat=yes;picosat=no;cadical=no;;
    --only-picosat) lingeling=no;minisat=no;picosat=yes;cadical=no;;

    -*) die "invalid option '$1' (try '-h')";;
  esac
  shift
done

#--------------------------------------------------------------------------#

mkdir -p $BUILDDIR
cd $BUILDDIR

cmake_opts=""

[ $asan = yes ] && cmake_opts="$cmake_opts -DASAN=ON"
[ $debug = yes ] && cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=Debug"
[ $check = yes ] && cmake_opts="$cmake_opts -DCHECK=ON"
[ $log = yes ] && cmake_opts="$cmake_opts -DLOG=ON"
[ $shared = yes ] && cmake_opts="$cmake_opts -DSHARED=ON"

[ $cadical = yes ] && cmake_opts="$cmake_opts -DCADICAL=ON"
[ $lingeling = yes ] && cmake_opts="$cmake_opts -DLINGELING=ON"
[ $minisat = yes ] && cmake_opts="$cmake_opts -DMINISAT=ON"
[ $picosat = yes ] && cmake_opts="$cmake_opts -DPICOSAT=ON"

[ $cadical = no ] && cmake_opts="$cmake_opts -DCADICAL=OFF"
[ $lingeling = no ] && cmake_opts="$cmake_opts -DLINGELING=OFF"
[ $minisat = no ] && cmake_opts="$cmake_opts -DMINISAT=OFF"
[ $picosat = no ] && cmake_opts="$cmake_opts -DPICOSAT=OFF"

[ $gcov = yes ] && cmake_opts="$cmake_opts -DGCOV=ON"
[ $gprof = yes ] && cmake_opts="$cmake_opts -DGPROF=ON"

[ $python = yes ] && cmake_opts="$cmake_opts -DPYTHON=ON"
[ $timestats = yes ] && cmake_opts="$cmake_opts -DTIME_STATS=ON"

[ $flags = none ] || cmake_opts="$cmake_opts -DFLAGS=$flags"

cd $BUILDDIR
cmake .. $cmake_opts
cd - > /dev/null

