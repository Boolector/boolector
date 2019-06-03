#!/bin/sh

BUILD_DIR="$(pwd)/build"
BOOLECTOR_BINARY="$BUILD_DIR/bin/boolector"
POOLECTOR_BINARY="$(pwd)/contrib/poolector.py"
YEAR="2019"

[ -d "$BUILD_DIR" ] && echo "build directory already exists" && exit 1

rm -rf "$(pwd)/deps"

./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh
./contrib/setup-lingeling.sh
./contrib/setup-cms.sh

# main track QF_ABV, QF_AUFBV, QF_UFBV, QF_BV, BV (with lingeling + CaDiCaL)

./configure.sh --no-minisat --no-picosat --no-cms --gmp
(
  cd "$BUILD_DIR" || exit 1
  make -j $(nproc)
)

b=$($BOOLECTOR_BINARY -v /dev/null | grep -i version | grep -i boolector | awk '{print $(NF-1);exit}')
#l=$($BOOLECTOR_BINARY -v /dev/null | grep -i version | grep -i lingeling | awk '{print $(NF-1);exit}')
version=boolector-${b}

dir="/tmp/boolector-smtcomp"
rm -rf $dir
RUN_DEFAULT="$dir/bin/starexec_run_default"
DESCRIPTION="$dir/starexec_description.txt"

# Non-incremental track configuration
archive=${version}-non-incremental.tar.gz
mkdir -p $dir/bin
cp "$BOOLECTOR_BINARY" $dir/bin

cat > "$RUN_DEFAULT" << EOF
#!/bin/sh
./boolector -uc -br fun --fun:preprop --prop:nprops=10000 --simp-norm-adds --declsort-bv-width=16 \$1
EOF

echo "Boolector non incremental track configuration $YEAR" > "$DESCRIPTION"
chmod +x "$RUN_DEFAULT"
tar -C "$dir" -zcf "$archive" .
ls -l "$archive"

rm -rf $dir

# Incremental track configuration
archive=${version}-incremental.tar.gz
mkdir -p $dir/bin
cp "$BOOLECTOR_BINARY" $dir/bin

cat > "$RUN_DEFAULT" << EOF
#!/bin/sh
./boolector -i -br fun --nondestr-subst --declsort-bv-width=16 \$1
EOF

echo "Boolector incremental track configuration $YEAR" > "$DESCRIPTION"
chmod +x "$RUN_DEFAULT"
tar -C "$dir" -zcf "$archive" .
ls -l "$archive"

rm -rf "$dir"

# Poolector
rm -rf "$BUILD_DIR"
./configure.sh --no-minisat --no-picosat --gmp
(
  cd "$BUILD_DIR" || exit 1
  make -j $(nproc)
)

archive=${version}-poolector.tar.gz
mkdir -p $dir/bin
cp "$BOOLECTOR_BINARY" $dir/bin
cp "$POOLECTOR_BINARY" $dir/bin

cat > "$RUN_DEFAULT" << EOF
#!/bin/sh
python2.7 ./poolector.py \$1
EOF

echo "Poolector non incremental track configuration $YEAR" > "$DESCRIPTION"
chmod +x "$RUN_DEFAULT"
tar -C "$dir" -zcf "$archive" .
ls -l "$archive"

rm -rf "$dir"
