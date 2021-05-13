#!/usr/bin/env bash
set -e -o pipefail

mkdir -p /build
cd /build

echo "Hello from PyPi build.sh"

BUILD_DIR=`pwd`
N_CORES=`nproc`

cp -r /boolector .

# Setup dependencies
cd boolector
/bin/sh ./contrib/setup-btor2tools.sh
/bin/sh ./contrib/setup-cadical.sh
/bin/sh ./contrib/setup-lingeling.sh

#********************************************************************
#* boolector
#********************************************************************
cd ${BUILD_DIR}

cd boolector

./configure.sh --shared --prefix /usr

cd build

make -j${N_CORES}

make install

#********************************************************************
#* pyboolector
#********************************************************************
cd ${BUILD_DIR}
rm -rf pyboolector

# Specify path to CmakeLists.txt so setup.py can extract the version
export CMAKELISTS_TXT=/boolector/CMakeLists.txt

cp -r /boolector/pypi pyboolector

# Grab the main license file
cp /boolector/COPYING pyboolector/LICENSE

cd pyboolector

for py in /opt/python/cp3{6,7,8,9}-*; do
  echo "Python: ${py}"
  python=/opt/python/${py}/bin/python
  cd ${BUILD_DIR}/pyboolector
  rm -rf src
  cp -r ${BUILD_DIR}/boolector/src/api/python src
  sed -i -e 's/override//g' \
     -e 's/noexcept/_GLIBCXX_USE_NOEXCEPT/g' \
     -e 's/\(BoolectorException (const.*\)/\1\n    virtual ~BoolectorException() _GLIBCXX_USE_NOEXCEPT {}/' \
       src/pyboolector_abort.cpp
  mkdir -p src/utils
  cp ${BUILD_DIR}/boolector/src/*.h src
  cp ${BUILD_DIR}/boolector/src/utils/*.h src/utils
  $python ./src/mkenums.py ./src/btortypes.h ./src/pyboolector_enums.pxd
  $python setup.py sdist bdist_wheel
done

for whl in dist/*.whl; do
  auditwheel repair $whl
done

rm -rf /boolector/result
mkdir -p /boolector/result

cp -r wheelhouse dist /boolector/result

