#!/bin/sh

cd `dirname $0`

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
arch=unknown

onlylingeling=no
onlyminisat=no
onlypicosat=no

gcov=no
gprof=no
python=no

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
  -python           compile python API

By default all supported SAT solvers are used and linked into
the binary if they can be found in the parent directory.

By specifying one of them 'configure.sh' fails if it can not be used.

  --lingeling       use and link with Lingeling (default)
  --picosat         use and link with PicoSAT
  --minisat         use and link with MiniSAT

Disable compilation of specific SAT solver back-ends:

  --no-lingeling    do not use Lingeling
  --no-picosat      do not use PicoSAT
  --no-minisat      do not use MiniSAT

  --only-lingeling  only use Lingeling
  --only-picosat    only use PicoSAT
  --only-minisat    only use MiniSAT

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
    -m32|--m32) arch=32;;
    -m64|--m64) arch=64;;
    -flto) flto=yes;;
    -shared) shared=yes;;
    -static) static=yes;;
    -picosat|--picosat) picosat=yes;;
    -no-picosat|--no-picosat) picosat=no;;
    -lingeling|--lingeling) lingeling=yes;;
    -no-lingeling|--no-lingeling) lingeling=no;;
    -only-lingeling|--only-lingeling) lingeling=yes;minisat=no;picosat=no;;
    -only-picosat|--only-picosat) lingeling=no;minisat=no;picosat=yes;;
    -only-minisat|--only-minisat) lingeling=no;minisat=yes;picosat=no;;
    -minisat|--minisat) minisat=yes;;
    -no-minisat|--no-minisat) minisat=no;;
    -h|-help|--help) usage;;
    -gcov) gcov=yes;;
    -gprof) gprof=yes;;
    -python) python=yes;shared=yes;;
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
else
  msg "optimized compilation (no '-g')"
fi

#--------------------------------------------------------------------------#

BINDIR="bin"
BUILDIR="build"
TESTDIR="tests"
SRCDIR="src"

SRCDIRS="src src/dumper src/parser src/simplifier src/utils"
if [ $python = yes ]
then
  SRCDIRS="$SRCDIRS $SRCDIR/api/python"
fi
for additional in btorfmt tests
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
  [ $arch = 32 ] && CFLAGS="$CFLAGS -m32"
  [ $arch = 64 ] && CFLAGS="$CFLAGS -m64"
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
elif [ $debug = yes ]
then
  die "CFLAGS environment variable defined and '-g' used"
elif [ $debug = no ]
then
  die "CFLAGS environment variable defined and '-O' used"
fi

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
[ $gcov = yes ] && CFLAGS="$CFLAGS -fprofile-arcs -ftest-coverage"
[ $gprof = yes ] && CFLAGS="$CFLAGS -pg"

#--------------------------------------------------------------------------#

LIBS="-L$BUILDIR"
OBJS=""
INCS="-I$SRCDIR -I$BUILDIR "
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
    OBJS="${OBJS}$BUILDIR/btorminisat.o"
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

#--------------------------------------------------------------------------#

[ $picosat = no -a $lingeling = no -a $minisat = no ] && \
  die "either need MiniSAT, PicoSAT or Lingeling"

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
from Cython.Distutils import build_ext
cwd=os.getcwd()
incdirs=["$SRCDIR"]
incdirs.extend("$py_inc_dirs".split())
ext_modules=[
    Extension("boolector",
              sources=["$SRCDIR/api/python/boolector.pyx"],
              include_dirs=incdirs,
              library_dirs=[s for s in "$py_library_dirs".split()],
              libraries="$py_libraries".split(),
              extra_compile_args=[s for s in "$CFLAGS".split() if "-D" in s],
       extra_link_args=["-Wl,-rpath,"+":".join([s for s in "$py_library_dirs".split()])]
    )
]
setup(cmdclass={'build_ext': build_ext}, ext_modules=ext_modules)
EOF

cat > python.mk <<EOF

all: python

python: \$(BUILDIR)/api/python/boolector_py.o setup.py
	$PYTHON setup.py build_ext -b $BUILDIR -t $BUILDIR/api/python/tmp
	@echo "Compiled Boolector Python module. Please read $SRCDIR/api/python/README on how to use the module"

python-clean:
	rm -rf build/api/python/boolector_py.o
	rm -f \$(SRCDIR)/api/python/boolector.c boolector.cpython*.so
	rm -f \$(SRCDIR)/api/python/boolector.pix

python-clean-mk:
	rm -f python.mk setup.py

clean: python-clean python-clean-mk

EOF

opts=`grep "BTOR_OPT.*," $SRCDIR/btortypes.h | awk 'BEGIN{i=0} { gsub(",", "="); print $1i; i += 1}'`
cat > $SRCDIR/api/python/boolector.pix << EOF
$opts
EOF

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
