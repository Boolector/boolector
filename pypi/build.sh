#!/bin/sh

mkdir -p /build
cd /build

echo "Hello from PyPi build.sh"

BUILD_DIR=`pwd`
if test -f /proc/cpuinfo; then
  echo "cpuinfo exists"
  N_CORES=`cat /proc/cpuinfo | grep processor | wc -l`
else
  echo "cpuinfo DOES NOT exist"
  N_CORES=1
fi

CMAKE_DIR=cmake-3.5.0-Linux-x86_64

if test ! -f ${CMAKE_DIR}.tar.gz; then
  curl -L -O https://cmake.org/files/v3.5/${CMAKE_DIR}.tar.gz
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

#********************************************************************
#* pyboolector
#********************************************************************
cd ${BUILD_DIR}
rm -rf pyboolector

cp -r /boolector/pypi pyboolector

cd pyboolector

# for py in python27 rh-python35 rh-python36; do
for py in cp27-cp27m cp34-cp34m cp35-cp35m cp36-cp36m cp37-cp37m cp38-cp38; do
  echo "Python: ${py}"
  python=/opt/python/${py}/bin/python
  cd ${BUILD_DIR}/pyboolector
  rm -rf src
  cp -r ${BUILD_DIR}/boolector/src/api/python src
  sed -i -e 's/override//g' \
     -e 's/noexcept/_GLIBCXX_USE_NOEXCEPT/g' \
     -e 's/\(BoolectorException (const.*\)/\1\n    virtual ~BoolectorException() _GLIBCXX_USE_NOEXCEPT {}/' \
       src/pyboolector_abort.cpp
  if test $? -ne 0; then exit 1; fi
  mkdir -p src/utils
  cp ${BUILD_DIR}/boolector/src/*.h src
  cp ${BUILD_DIR}/boolector/src/utils/*.h src/utils
  $python ./src/mkoptions.py ./src/btortypes.h ./src/pyboolector_options.pxd
  if test $? -ne 0; then exit 1; fi
  $python setup.py sdist bdist_wheel
  if test $? -ne 0; then exit 1; fi
done

for whl in dist/*.whl; do
  auditwheel repair $whl
  if test $? -ne 0; then exit 1; fi
done

rm -rf /boolector/result
mkdir -p /boolector/result

cp -r wheelhouse dist /boolector/result


