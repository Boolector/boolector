#!/bin/sh
#--------------------------------------------------------------------------#

BUILDDIR=build

#--------------------------------------------------------------------------#

asan=no
debug=no
check=no
log=no
shared=no

btor2_dir=unknown

lingeling=unknown
minisat=unknown
picosat=unknown
cadical=unknown

lingeling_dir=unknown
minisat_dir=unknown
picosat_dir=unknown
cadical_dir=unknown

gcov=no
gprof=no
python=no
timestats=no

flags=""

#--------------------------------------------------------------------------#

usage () {
cat <<EOF
usage: $0 [<option> ...]

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

  --btor2tools-dir  the location of the btor2tools package (optional)
                    default: <boolector_root_dir>/../btor2tools

By default all supported SAT solvers available are used and linked.
If explicitly enabled, configuration will fail if the SAT solver library 
can not be found.

  --no-cadical           do not use CaDiCaL
  --no-lingeling         do not use Lingeling
  --no-minisat           do not use MiniSAT
  --no-picosat           do not use PicoSAT

  --only-cadical         only use CaDiCaL
  --only-lingeling       only use Lingeling
  --only-minisat         only use MiniSAT
  --only-picosat         only use PicoSAT

  --cadical-dir <dir>    CaDiCaL root directory (optional)
                         default: <boolector_root_dir>/../cadical
  --lingeling-dir <dir>  Lingeling root directory (optional)
                         default: <boolector_root_dir>/../lingeling
  --minisat-dir <dir>    MiniSat root directory (optional)
                         default: <boolector_root_dir>/../minisat
  --picosat-dir <dir>    PicoSAT root directory (optional)
                         default: <boolector_root_dir>/../picosat
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

[ ! -e src/boolector.h ] && die "$0 not called from Boolector base directory"

while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) usage;;

    -g) debug=yes;;
    -f*|-m*) if [ -z "$flags" ]; then flags=$1; else flags="$flags;$1"; fi;;

    --shared) shared=yes;;

    -l)      log=yes;;
    -c)      check=yes;;
    --asan)  asan=yes;;
    --gcov)  gcov=yes;;
    --gprof) gprof=yes;;

    --python)     python=yes;;
    --time-stats) timestats=yes;;

    --btor2tools-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --btor2tools-dir"
      fi
      btor2_dir=$1
      ;;
    --no-cadical)   cadical=no;;
    --no-lingeling) lingeling=no;;
    --no-minisat)   minisat=no;;
    --no-picosat)   picosat=no;;

    --only-cadical)   lingeling=no;minisat=no;picosat=no;cadical=yes;;
    --only-lingeling) lingeling=yes;minisat=no;picosat=no;cadical=no;;
    --only-minisat)   lingeling=no;minisat=yes;picosat=no;cadical=no;;
    --only-picosat)   lingeling=no;minisat=no;picosat=yes;cadical=no;;

    --cadical-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --cadical-dir"
      fi
      cadical_dir=$1
      ;;
    --lingeling-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --lingeling-dir"
      fi
      lingeling_dir=$1
      ;;
    --minisat-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --minisat-dir"
      fi
      minisat_dir=$1
      ;;
    --picosat-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --picosat-dir"
      fi
      picosat_dir=$1
      ;;

    -*) die "invalid option '$1' (try '-h')";;
  esac
  shift
done

#--------------------------------------------------------------------------#

cmake_opts=""

[ $asan = yes ] && cmake_opts="$cmake_opts -DASAN=ON"
[ $debug = yes ] && cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=Debug"
[ $check = yes ] && cmake_opts="$cmake_opts -DCHECK=ON"
[ $log = yes ] && cmake_opts="$cmake_opts -DLOG=ON"
[ $shared = yes ] && cmake_opts="$cmake_opts -DSHARED=ON"

[ $btor2_dir = unknown ] || cmake_opts="$cmake_opts -DBTOR2_ROOT_DIR=$btor2_dir"

[ $cadical = yes ] && cmake_opts="$cmake_opts -DUSE_CADICAL=ON"
[ $lingeling = yes ] && cmake_opts="$cmake_opts -DUSE_LINGELING=ON"
[ $minisat = yes ] && cmake_opts="$cmake_opts -DUSE_MINISAT=ON"
[ $picosat = yes ] && cmake_opts="$cmake_opts -DUSE_PICOSAT=ON"

[ $cadical = no ] && cmake_opts="$cmake_opts -DUSE_CADICAL=OFF"
[ $lingeling = no ] && cmake_opts="$cmake_opts -DUSE_LINGELING=OFF"
[ $minisat = no ] && cmake_opts="$cmake_opts -DUSE_MINISAT=OFF"
[ $picosat = no ] && cmake_opts="$cmake_opts -DUSE_PICOSAT=OFF"

[ $gcov = yes ] && cmake_opts="$cmake_opts -DGCOV=ON"
[ $gprof = yes ] && cmake_opts="$cmake_opts -DGPROF=ON"

[ $python = yes ] && cmake_opts="$cmake_opts -DPYTHON=ON"
[ $timestats = yes ] && cmake_opts="$cmake_opts -DTIME_STATS=ON"

[ -n "$flags" ] && cmake_opts="$cmake_opts -DFLAGS=$flags"

[ $cadical_dir = unknown ] || cmake_opts="$cmake_opts -DCADICAL_ROOT_DIR=$cadical_dir"
[ $lingeling_dir = unknown ] || cmake_opts="$cmake_opts -DLINGELING_ROOT_DIR=$lingeling_dir"
[ $minisat_dir = unknown ] || cmake_opts="$cmake_opts -DMINISAT_ROOT_DIR=$minisat_dir"
[ $picosat_dir = unknown ] || cmake_opts="$cmake_opts -DPICOSAT_ROOT_DIR=$picosat_dir"

mkdir -p $BUILDDIR
cd $BUILDDIR

[ -e CMakeCache.txt ] && rm CMakeCache.txt
cmake .. $cmake_opts
