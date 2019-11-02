#!/bin/sh

mkdir -p /build
cd /build

echo "Hello from PyPi build.sh"

BUILD_DIR=`pwd`
if test -f /proc/cpuinfo; then
  N_CORES=1
else
  N_CORES=1
fi

CMAKE_DIR=cmake-3.3.0-Linux-x86_64

if test ! -f ${CMAKE_DIR}.tar.gz; then
  curl -L -O https://cmake.org/files/v3.3/cmake-3.3.0-Linux-x86_64.tar.gz
  if test $? -ne 0; then exit 1; fi
fi      

cp -r /boolector .

if test ! -f lingeling-master.zip; then
  curl -L -o lingeling-master.zip https://github.com/arminbiere/lingeling/archive/master.zip
  if test $? -ne 0; then exit 1; fi
fi

if test ! -f btor2tools-master.zip; then
  curl -L -o btor2tools-master.zip https://github.com/Boolector/btor2tools/archive/master.zip
  if test $? -ne 0; then exit 1; fi
fi

#rm -rf boolector-master
#rm -rf ${CMAKE_DIR}

tar xvzf ${CMAKE_DIR}.tar.gz

export PATH=${BUILD_DIR}/${CMAKE_DIR}/bin:$PATH

#unzip -o boolector-master.zip
#if test $? -ne 0; then exit 1; fi

mkdir -p boolector/deps
mkdir -p boolector/deps/install/lib
mkdir -p boolector/deps/install/include/btor2parser

ngeling
#************************************************************************************************
cd ${BUILD_DIR}
  
unzip -o lingeling-master.zip
if test $? -ne 0; then exit 1; fi

mv lingeling-master boolector/deps/lingeling
if test $? -ne 0; then exit 1; fi

cd boolector/deps/lingeling
if test $? -ne 0; then exit 1; fi
  
# GCC doesn't like having a field named 'clone'
sed -i -e 's/\<clone\>/_clone/g' ilingeling.c
if test $? -ne 0; then exit 1; fi

./configure.sh -fPIC
if test $? -ne 0; then exit 1; fi

# Define STDVERSION so we can find LLONG_MAX
sed -i -e 's/\(CFLAGS=.*\)/\1\nCFLAGS+=-D__STDC_VERSION__=199901L/g' makefile
if test $? -ne 0; then exit 1; fi

make -j${N_CORES}
if test $? -ne 0; then exit 1; fi

cp liblgl.a ${BUILD_DIR}/boolector/deps/install/lib
if test $? -ne 0; then exit 1; fi
cp lglib.h  ${BUILD_DIR}/boolector/deps/install/include
if test $? -ne 0; then exit 1; fi

#************************************************************************************************
#* btor2tools
#************************************************************************************************
cd ${BUILD_DIR}

unzip -o btor2tools-master.zip
if test $? -ne 0; then exit 1; fi

mv btor2tools-master boolector/deps/btor2tools
if test $? -ne 0; then exit 1; fi

cd boolector/deps/btor2tools
if test $? -ne 0; then exit 1; fi

./configure.sh -fPIC
if test $? -ne 0; then exit 1; fi

make -j${N_CORES}
if test $? -ne 0; then exit 1; fi

cp build/libbtor2parser.a ${BUILD_DIR}/boolector/deps/install/lib
if test $? -ne 0; then exit 1; fi
cp src/btor2parser/btor2parser.h  ${BUILD_DIR}/boolector/deps/install/include/btor2parser
if test $? -ne 0; then exit 1; fi

#********************************************************************
#* boolector
#********************************************************************
cd ${BUILD_DIR}

sed -i -e 's/add_check_c_cxx_flag("-W")/add_check_c_cxx_flag("-W")\nadd_check_c_cxx_flag("-fPIC")/g' \
  boolector/CMakeLists.txt

cd boolector

./configure.sh -fPIC --shared --prefix /usr
if test $? -ne 0; then exit 1; fi

cd build

make -j${N_CORES}
if test $? -ne 0; then exit 1; fi

make install
if test $? -ne 0; then exit 1; fi


