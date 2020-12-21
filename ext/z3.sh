#!/usr/bin/env bash
# https://github.com/Z3Prover/z3

# clean
rm -rf z3-*

# download
wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.9/z3-4.8.9-x64-ubuntu-16.04.zip
unzip z3-4.8.9-x64-ubuntu-16.04.zip

# test
./z3-4.8.9-x64-ubuntu-16.04/bin/z3 test.smt2

# copy
mkdir -p bin-z3/
mv z3-4.8.9-x64-ubuntu-16.04/bin/z3 bin-z3/
