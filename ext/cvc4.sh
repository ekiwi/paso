#!/usr/bin/env bash
# https://github.com/CVC4/CVC4

# clean
rm -rf cvc4-*
rm -f cvc4

# download
wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
mv cvc4-1.8-x86_64-linux-opt cvc4
chmod +x cvc4

# test
./cvc4 --incremental test.smt2

# move
mkdir -p bin-cvc4
mv cvc4 bin-cvc4/
