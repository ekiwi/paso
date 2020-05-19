#!/usr/bin/env bash
# https://github.com/Z3Prover/z3

# clean
rm -rf z3-*

# download
wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.8/z3-4.8.8-x64-ubuntu-16.04.zip
unzip z3-4.8.8-x64-ubuntu-16.04.zip

# test
./z3-4.8.8-x64-ubuntu-16.04/bin/z3 test.smt2

# copy
mv z3-4.8.8-x64-ubuntu-16.04/bin/ bin-z3/
