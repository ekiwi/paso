#!/usr/bin/env bash
# https://github.com/SRI-CSL/yices2

# clean
rm -rf Yices-*
rm -rf yices2-*

# install ubuntu packets
if [ `lsb_release -si` == "Ubuntu" ]; then
  sudo apt install -y gperf
fi

# download
wget https://github.com/SRI-CSL/yices2/archive/Yices-2.6.2.zip
unzip Yices-2.6.2.zip

# compile
cd yices2-Yices-2.6.2/
autoconf
./configure
make -j`nproc`

# test
./build/x86_64-pc-linux-gnu-release/bin/yices_smt2 --incremental ../test.smt2

# copy
cd ..
mv yices2-Yices-2.6.2/build/x86_64-pc-linux-gnu-release/dist/bin/ bin-yices/
mv yices2-Yices-2.6.2/build/x86_64-pc-linux-gnu-release/dist/lib/ lib-yices/

# rename shared object
mv lib-yices/libyices.so.2* lib-yices/libyices.so
