#!/bin/sh

cd `dirname $0`

asan=no
debug=unknown
check=no
log=unknown
flto=no
shared=no
static=no

ROOT=`dirname "$(readlink -f $0)"|sed -e 's, ,\\ ,g'`

lingeling=yes
minisat=unknown
picosat=unknown
cadical=unknown
btor2tools=yes   # Note: required dependency, may change in the future

onlylingeling=no
onlyminisat=no
onlypicosat=no
onlycadical=no

gcov=no
gprof=no
python=no
timestats=no

flags=none

#--------------------------------------------------------------------------#

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}

msg () {
  echo "[configure.sh] $*"
}

#--------------------------------------------------------------------------#

usage () {
cat <<EOF
usage: ./configure.sh [<option> ...]

where <option> is one of the following:

  -O                optimized compilation (default)
  -flto             enable link time optimization
  -static           static compilation
  -g                compile with debugging support
  -l                compile with logging support (default for '-g')
  -c                check assertions even in optimized compilation
  -m{32,64}         force 32-bit or 64-bit compilation
  -shared           shared library
  -asan             compile with -fsanitize=address -fsanitize-recover=address
  -gcov             compile with -fprofile-arcs -ftest-coverage
  -gprof            compile with -pg
  -python           compile python API
  --time-stats      compile with time statistics
  -f...|-m...       add compiler options

By default all supported SAT solvers are used and linked into
the binary if they can be found in the parent directory.

By specifying one of them 'configure.sh' fails if it can not be used.

  --lingeling       use and link with Lingeling (default)
  --picosat         use and link with PicoSAT
  --minisat         use and link with MiniSAT
  --cadical         use and link with CaDiCaL

Disable compilation of specific SAT solver back-ends:

  --no-lingeling    do not use Lingeling
  --no-picosat      do not use PicoSAT
  --no-minisat      do not use MiniSAT
  --no-cadical      do not use CaDiCaL

  --only-lingeling  only use Lingeling
  --only-picosat    only use PicoSAT
  --only-minisat    only use MiniSAT
  --only-cadical    only use CaDiCaL

You might also want to use the environment variables
CC and CXX to specify the used C and C++ compiler, as in

  CC=gcc-4.4 CXX=g++-4.4 ./configure.sh

which forces to use 'gcc-4.4' and 'g++-4.4'.
EOF
  exit 0
}

#--------------------------------------------------------------------------#

while [ $# -gt 0 ]
do
  case $1 in
    -g) debug=yes;;
    -l) log=yes;;
    -O) debug=no;;
    -c) check=yes;;
    -flto) flto=yes;;
    -shared) shared=yes;;
    -static) static=yes;;
    -picosat|--picosat) picosat=yes;;
    -no-picosat|--no-picosat) picosat=no;;
    -lingeling|--lingeling) lingeling=yes;;
    -no-lingeling|--no-lingeling) lingeling=no;;
    -only-lingeling|--only-lingeling) lingeling=yes;minisat=no;picosat=no;cadical=no;;
    -only-picosat|--only-picosat) lingeling=no;minisat=no;picosat=yes;cadical=no;;
    -only-minisat|--only-minisat) lingeling=no;minisat=yes;picosat=no;cadical=no;;
    -only-cadical|--only-cadical) lingeling=no;minisat=no;picosat=no;cadical=yes;;
    -minisat|--minisat) minisat=yes;;
    -no-minisat|--no-minisat) minisat=no;;
    -cadical|--cadical) cadical=yes;;
    -no-cadical|--no-cadical) cadical=no;;
    -h|-help|--help) usage;;
    -asan) asan=yes;;
    -gcov) gcov=yes;;
    -gprof) gprof=yes;;
    -python) python=yes;shared=yes;;
    --time-stats) timestats=yes;;
    -f*|-m*) if [ $flags = none ]; then flags=$1; else flags="$flags $1"; fi;;
    -*) die "invalid option '$1' (try '-h')";;
  esac
  shift
done

#--------------------------------------------------------------------------#

addstcpp () {
  if [ X"`echo "$LIBS" | grep 'lstdc++'`" = X ]
  then
    [ X"$LIBS" = X ] || LIBS="$LIBS "
    LIBS="${LIBS}-lstdc++"
    msg "need to link against 'libstdc++'"
  fi
}

#--------------------------------------------------------------------------#

if [ $debug = yes ]
then
  msg "compiling for debugging as specified"
  timestats=yes
else
  msg "optimized compilation (no '-g')"
fi

#--------------------------------------------------------------------------#

BINDIR="bin"
BUILDIR="build"
TESTDIR="tests"
SRCDIR="src"

SRCDIRS="src src/dumper src/parser src/sat src/simplifier src/normalizer src/utils"
if [ $python = yes ]
then
  SRCDIRS="$SRCDIRS $SRCDIR/api/python"
fi
for additional in tests
do
  [ -d src/$additional ] && SRCDIRS="$SRCDIRS src/$additional"
done


#--------------------------------------------------------------------------#

TARGETS="$BINDIR/boolector"
[ $shared = yes ] && TARGETS="$TARGETS $BUILDIR/libboolector.so"

#--------------------------------------------------------------------------#

if [ X"$CFLAGS" = X ]
then
  [ $debug = unknown ] && debug=no
  CFLAGS="-W -Wall -Wextra -Wredundant-decls"
  [ $static = yes ] && CFLAGS="$CFLAGS -static"
  [ $shared = yes ] && CFLAGS="$CFLAGS -fPIC"
  if [ $debug = yes ]
  then
    CFLAGS="$CFLAGS -g3 -ggdb"
  else
    CFLAGS="$CFLAGS -O3"
    [ $check = no ] && CFLAGS="$CFLAGS -DNDEBUG"
    [ $flto = yes ] && CFLAGS="$CFLAGS -flto"
  fi
  [ $flags = none ] || CFLAGS="$CFLAGS $flags"
elif [ $debug = yes ]
then
  die "CFLAGS environment variable defined and '-g' used"
elif [ $debug = no ]
then
  die "CFLAGS environment variable defined and '-O' used"
fi

[ $timestats = yes ] && CFLAGS="$CFLAGS -DBTOR_TIME_STATISTICS"
[ $timestats = no ] && msg "time statistics are disabled (no '--time-stats')"

#--------------------------------------------------------------------------#

if [ $log = yes ]
then
  msg "compiling with logging support (as specified)"
elif [ $log = no ]
then
  die "internal configuration error: logging disabled"
elif [ $debug = yes ]
then
  msg "compiling with logging support (default for debugging)"
  log=yes
else
  msg "compiling without logging support (default for no debugging)"
  log=no
fi

[ $log = no ] && CFLAGS="$CFLAGS -DNBTORLOG"
[ $asan = yes ] && CFLAGS="$CFLAGS -fsanitize=address -fsanitize-recover=address"
[ $gcov = yes ] && CFLAGS="$CFLAGS -fprofile-arcs -ftest-coverage"
[ $gprof = yes ] && CFLAGS="$CFLAGS -pg"

#--------------------------------------------------------------------------#

LIBS="-L$BUILDIR -lpthread"
OBJS=""
INCS="-I$SRCDIR -I$BUILDIR"
LDEPS="$BUILDIR/libboolector.a"

LIBZ=no
LIBM=no
LIBSTDCPP=no
RPATHS="-rpath\,$ROOT/$BUILDIR"
if [ $shared = yes ]
then
  LDEPS="$BUILDIR/libboolector.so"
  LIBSTDCPP=yes
fi

#--------------------------------------------------------------------------#

if [ $btor2tools = yes ]
then
  if [ ! -d $ROOT/../btor2tools ]
  then
    die "btor2tools missing"
  fi
  if [ $shared = yes -a ! -f $ROOT/../btor2tools/build/libbtor2parser.so ]
  then
    die "libbtor2parser.so not found. Compile btor2tools as shared library"
  elif [ $shared = no -a ! -f $ROOT/../btor2tools/build/libbtor2parser.a ]
  then
    die "libbtor2parser.a library not found. Compile btor2tools first."
  fi
  if [ $shared = yes ]
  then
    LIBS="${LIBS} -L$ROOT/../btor2tools/build -lbtor2parser"
    LDEPS="${LDEPS} $ROOT/../btor2tools/build/libbtor2parser.so"
  else
    LIBS="${LIBS} -L$ROOT/../btor2tools/build -lbtor2parser"
    LDEPS="${LDEPS} $ROOT/../btor2tools/build/libbtor2parser.a"
  fi
  INCS="${INCS} -I$ROOT/../btor2tools/src"
  RPATHS="${RPATHS}\,-rpath\,$ROOT/../btor2tools/build"
else
  msg "no using BTOR2Tools"
fi

#--------------------------------------------------------------------------#

if [ $picosat = no ]
then
  msg "not using PicoSAT"
else

  if [ -d $ROOT/../picosat ]
  then
    for path in $ROOT/../picosat/picosat.o $ROOT/../picosat/version.o allfound
    do
      [ -f $path ] || break
    done
  else
    path=$ROOT/../picosat
  fi

  if [ $path = allfound ]
  then
    msg "using PicoSAT in '$ROOT/../picosat'"
    picosat=yes
  elif [ $picosat = yes ]
  then
    die "impossible to use PicoSAT: '$path' missing"
  else
    msg "disabling PicoSAT: '$path' missing"
    picosat=no
  fi

  if [ $picosat = yes ]
  then
    [ X"$CFLAGS" = X ] || CFLAGS="$CFLAGS "
    [ X"$INCS" = X ] || INCS="$INCS "
    [ X"$LDEPS" = X ] || LDEPS="$LDEPS "
    [ X"$LIBS" = X ] || LIBS="$LIBS "
    CFLAGS="${CFLAGS}-DBTOR_USE_PICOSAT"
    RPATHS="${RPATHS}\,-rpath\,$ROOT/../picosat/"
    if [ $shared = yes ]		
    then
      LIBS="${LIBS}-L$ROOT/../picosat -lpicosat"
      LDEPS="${LDEPS}$ROOT/../picosat/libpicosat.so"
    else
      LIBS="${LIBS}-L$ROOT/../picosat -lpicosat"
      LDEPS="${LDEPS}$ROOT/../picosat/libpicosat.a"
    fi
    INCS="${INCS}-I$ROOT/../picosat"
  fi
fi

#--------------------------------------------------------------------------#

if [ $lingeling = no ]
then
  msg "not using Lingeling as requested by command line option"
else

  if [ -d $ROOT/../lingeling ]
  then
    for path in $ROOT/../lingeling/lglib.h $ROOT/../lingeling/liblgl.a allfound
    do
      [ -f $path ] || break
    done
  else
    path=$ROOT/../lingeling
  fi

  if [ $path = allfound ]
  then
    msg "using Lingeling in '$ROOT/../lingeling'"
    lingeling=yes
  elif [ $lingeling = yes ]
  then
    die "impossible to use Lingeling: '$path' missing"
  else
    msg "disabling Lingeling: '$path' missing"
    lingeling=no
  fi

  if [ $lingeling = yes ]
  then
    [ X"$CFLAGS" = X ] || CFLAGS="$CFLAGS "
    [ X"$LDEPS" = X ] || LDEPS="$LDEPS "
    [ X"$LIBS" = X ] || LIBS="$LIBS "
    [ X"$INCS" = X ] || INCS="$INCS "
    CFLAGS="${CFLAGS}-DBTOR_USE_LINGELING"
    LIBS="${LIBS}-L$ROOT/../lingeling -llgl"
    LDEPS="${LDEPS}$ROOT/../lingeling/liblgl.a"
    LIBM=yes
    INCS="${INCS}-I$ROOT/../lingeling"
  fi

  if [ -d $ROOT/../yalsat ]
  then
    for path in $ROOT/../yalsat/yals.h $ROOT/../yalsat/libyals.a allfound
    do
      [ -f $path ] || break
    done
  else
    path=$ROOT/../yalsat
  fi

  if [ $path = allfound ]
  then
    msg "using YalSAT in '$ROOT/../yalsat' too"
    yalsat=yes
  else
    msg "not using YalSAT"
    yalsat=no
  fi

  if [ $yalsat = yes ]
  then
    [ X"$LDEPS" = X ] || LDEPS="$LDEPS "
    [ X"$LIBS" = X ] || LIBS="$LIBS "
    LIBS="${LIBS}-L$ROOT/../yalsat -lyals"
    LDEPS="${LDEPS}$ROOT/../yalsat/libyals.a"
  fi

  if [ -d $ROOT/../druplig ]
  then
    for path in $ROOT/../druplig/druplig.h $ROOT/../druplig/libdruplig.a allfound
    do
      [ -f $path ] || break
    done
  else
    path=$ROOT/../druplig
  fi

  if [ $path = allfound ]
  then
    msg "using Druplig in '$ROOT/../druplig' too"
    druplig=yes
  else
    msg "not using Druplig"
    druplig=no
  fi

  if [ $druplig = yes ]
  then
    [ X"$LDEPS" = X ] || LDEPS="$LDEPS "
    [ X"$LIBS" = X ] || LIBS="$LIBS "
    LIBS="${LIBS}-L$ROOT/../druplig -ldruplig"
    LDEPS="${LDEPS}$ROOT/../druplig/libdruplig.a"
  fi
fi

#--------------------------------------------------------------------------#

if [ $minisat = no ]
then
  msg "not using MiniSAT"
else

  for path in \
    $ROOT/../minisat \
    $ROOT/../minisat/minisat \
    $ROOT/../minisat/minisat/simp \
    $ROOT/../minisat/build/release \
    allfound
  do
    [ -d $path ] || break
  done

  if [ $path = allfound ]
  then
    for path in \
      $ROOT/../minisat/minisat/simp/SimpSolver.h \
      $ROOT/../minisat/build/release/lib/libminisat.a \
      allfound
    do
      [ -f $path ] || break
    done
  fi

  if [ $path = allfound ]
  then
    msg "using MiniSAT in '$ROOT/../minisat'"
    minisat=yes
  elif [ $minisat = yes ]
  then
    die "impossible to use MiniSAT: '$path' missing"
  else
    msg "disabling MiniSAT: '$path' missing"
  fi

  if [ $minisat = yes ]
  then
    [ X"$CFLAGS" = X ] || CFLAGS="$CFLAGS "
    [ X"$OBJS" = X ] || OBJS="$OBJS "
    [ X"$LDEPS" = X ] || LDEPS="$LDEPS "
    [ X"$LIBS" = X ] || LIBS="$LIBS "
    [ X"$INCS" = X ] || INCS="$INCS "
    CFLAGS="${CFLAGS}-DBTOR_USE_MINISAT"
    OBJS="${OBJS}$BUILDIR/sat/btorminisat.o"
    RPATHS="${RPATHS}\,-rpath\,$ROOT/../minisat/build/dynamic/lib"
    if [ $shared = yes ]
    then
      LIBS="${LIBS}-L$ROOT/../minisat/build/dynamic/lib -lminisat"
      LDEPS="${LDEPS}$ROOT/../minisat/build/dynamic/lib/libminisat.so"
    else
      LIBS="${LIBS}-L$ROOT/../minisat/build/release/lib -lminisat"
      LDEPS="${LDEPS}$ROOT/../minisat/build/release/lib/libminisat.a"
    fi
    LIBSTDCPP=yes
    LIBZ=yes
    LIBM=yes
    INCS="${INCS}-I$ROOT/../minisat"
  fi

fi

if [ $cadical = no ]
then
  msg "not using CaDiCaL"
else

  for path in \
    $ROOT/../cadical \
    $ROOT/../cadical/build \
    allfound
  do
    [ -d $path ] || break
  done

  if [ $path = allfound ]
  then
    for path in \
      $ROOT/../cadical/build/libcadical.a \
      allfound
    do
      [ -f $path ] || break
    done
  fi

  if [ $path = allfound ]
  then
    msg "using CaDiCaL in '$ROOT/../cadical'"
    cadical=yes
  elif [ $cadical = yes ]
  then
    die "impossible to use CaDiCaL: '$path' missing"
  else
    msg "disabling CaDiCaL: '$path' missing"
  fi

  if [ $cadical = yes ]
  then
    [ X"$CFLAGS" = X ] || CFLAGS="$CFLAGS "
    [ X"$OBJS" = X ] || OBJS="$OBJS "
    [ X"$LDEPS" = X ] || LDEPS="$LDEPS "
    [ X"$LIBS" = X ] || LIBS="$LIBS "
    [ X"$INCS" = X ] || INCS="$INCS "
    CFLAGS="${CFLAGS}-DBTOR_USE_CADICAL"
    RPATHS="${RPATHS}\,-rpath=$ROOT/../cadical/build/"
    if [ $shared = yes ]
    then
      LIBS="${LIBS}-L$ROOT/../cadical/build -lcadical"
      LDEPS="${LDEPS}$ROOT/../cadical/build/libcadical.a"
    else
      LIBS="${LIBS}-L$ROOT/../cadical/build -lcadical"
      LDEPS="${LDEPS}$ROOT/../cadical/build/libcadical.a"
    fi
    LIBSTDCPP=yes
    LIBM=yes
    INCS="${INCS}-I$ROOT/../cadical/src"
  fi
fi

#--------------------------------------------------------------------------#

[ $picosat = no -a $lingeling = no -a $minisat = no -a $cadical = no ] && \
  die "either need MiniSAT, PicoSAT, Lingeling or CaDiCaL"

#--------------------------------------------------------------------------#


if [ $LIBSTDCPP = yes ]
then
  [ X"$LIBS" = X ] || LIBS="$LIBS "
  LIBS="${LIBS}-lstdc++"
  msg "linking against 'libstdc++'"
fi

if [ $LIBZ = yes ]
then
  [ X"$LIBS" = X ] || LIBS="$LIBS "
  LIBS="${LIBS}-lz"
  msg "linking against 'libz'"
fi

if [ $LIBM = yes ]
then
  [ X"$LIBS" = X ] || LIBS="$LIBS "
  LIBS="${LIBS}-lm"
  msg "linking against 'libm'"
fi

#--------------------------------------------------------------------------#

LIBS="-Wl\,${RPATHS} ${LIBS}"

if [ $python = yes ]
then
  # set default python command if no PYTHON environment variable was set
  [ -z "$PYTHON" ] && PYTHON="python"
  # check if set python command exists
  type "$PYTHON" > /dev/null 2>&1
  [ $? -gt 0 ] && die "Python command '$PYTHON' does not exist"

  py_libraries="boolector"
  py_library_dirs="$ROOT/$BUILDIR"
  py_inc_dirs=""
  if [ $lingeling = yes ]; then
    py_libraries="$py_libraries lgl"
    py_library_dirs="$py_library_dirs $ROOT/../lingeling"
    py_inc_dirs="$py_inc_dirs $ROOT/../lingeling"
  fi
  if [ $picosat = yes ]; then
    py_libraries="$py_libraries picosat"
    py_library_dirs="$py_library_dirs $ROOT/../picosat"
    py_inc_dirs="$py_inc_dirs $ROOT/../picosat"
  fi
  if [ $minisat = yes ]; then
    py_libraries="$py_libraries minisat"
    py_library_dirs="$py_library_dirs $ROOT/../minisat/build/dynamic/lib"
    py_inc_dirs="$py_inc_dirs $ROOT/../minisat/build/dynamic/lib"
  fi
  if [ $cadical = yes ]; then
    py_libraries="$py_libraries cadical"
    py_library_dirs="$py_library_dirs $ROOT/../cadical/build"
    py_inc_dirs="$py_inc_dirs $ROOT/../cadical/build"
  fi
  if [ $btor2tools = yes ]; then
    py_libraries="$py_libraries btor2parser"
    py_library_dirs="$py_library_dirs $ROOT/../btor2tools/build"
    py_inc_dirs="$py_inc_dirs $ROOT/../btor2tools/build"
  fi
  OBJS="$BUILDIR/api/python/boolector_py.o $OBJS"
  pyinc=`$PYTHON -c "import sysconfig; print(sysconfig.get_config_var('CONFINCLUDEPY'))"`
  pylib=`$PYTHON -c "import sysconfig; print(sysconfig.get_config_var('BINLIBDEST'))"`
  pyld=`basename $pyinc`
  INCS="${INCS} -I$pyinc"
  LIBS="${LIBS} -L$pylib -l$pyld"
  cat > setup.py <<EOF
import os
from distutils.core import setup
from distutils.extension import Extension
from Cython.Build import cythonize
cwd=os.getcwd()
ext_modules=[
    Extension("boolector",
        sources=["$SRCDIR/api/python/boolector.pyx"],
        include_dirs="$SRCDIR $SRCDIR/api/python $py_inc_dirs".split(),
        library_dirs="$py_library_dirs".split(),
        libraries="$py_libraries".split(),
        extra_compile_args=[s for s in "$CFLAGS".split() if "-D" in s],
        extra_link_args=["-Wl,-rpath,"+":".join("$py_library_dirs".split())]
    ),
]
setup(ext_modules=cythonize(ext_modules,
                            build_dir="$BUILDIR",
                            include_path=["$BUILDIR/api/python"]))
EOF

cat > python.mk <<EOF

all: python

python: \$(BUILDIR)/api/python/boolector_py.o setup.py
	$PYTHON setup.py build_ext -b $BUILDIR
	@echo "Compiled Boolector Python module."
	@echo "Please read $SRCDIR/api/python/README on how to use the module"

python-clean:
	rm -f python.mk setup.py

clean: python-clean

EOF

opts=`grep "BTOR_OPT.*," $SRCDIR/btortypes.h | awk 'BEGIN{i=0} { gsub(",", "="); print $1i; i += 1}'`
mkdir -p $BUILDIR/api/python/
echo "$opts" > $BUILDIR/api/python/options.pxd

else
  touch python.mk
fi


#--------------------------------------------------------------------------#

[ "X$CC" = X ] && CC=gcc
[ "X$CXX" = X ] && CXX=g++

msg "CC=$CC"
msg "CFLAGS=$CFLAGS"
msg "LIBS=$LIBS"
msg "OBJS=$OBJS"
msg "INCS=$INCS"

sed \
  -e "s,@CC@,$CC," \
  -e "s,@CXX@,$CXX," \
  -e "s,@INCS@,$INCS," \
  -e "s,@CFLAGS@,$CFLAGS," \
  -e "s,@LIBS@,$LIBS," \
  -e "s,@LDEPS@,$LDEPS," \
  -e "s,@OBJS@,$OBJS," \
  -e "s,@TARGETS@,$TARGETS," \
  -e "s,@SRCDIR@,$SRCDIR," \
  -e "s,@SRCDIRS@,$SRCDIRS," \
  -e "s,@BUILDIR@,$BUILDIR," \
  -e "s,@BINDIR@,$BINDIR," \
  -e "s,@TESTDIR@,$TESTDIR," \
  -e "s,@ROOT@,$ROOT,"\
  $ROOT/makefile.in > $ROOT/makefile
msg "makefile generated"
