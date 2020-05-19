#!/usr/bin/env bash
# https://github.com/Boolector/boolector

# clean
rm -f 3.2.1.zip
rm -rf boolector-*

# download
wget https://github.com/Boolector/boolector/archive/3.2.1.zip
unzip 3.2.1.zip

# compile
cd boolector-3.2.1/
./contrib/setup-lingeling.sh
./contrib/setup-btor2tools.sh
./configure.sh
cd build
make -j`nproc`
cd ..

# test
./build/bin/btormc -kmax 1 ../test.btor

# copy
cd ..
rm -r boolector-3.2.1/build/bin/examples
rm -r boolector-3.2.1/build/bin/tests
mv boolector-3.2.1/build/bin/ bin-btor/
