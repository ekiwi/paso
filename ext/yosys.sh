#!/usr/bin/env bash
# https://github.com/YosysHQ/yosys

VERSION=026fed31356faa5a1b21a6270dd5cf0c745bb76e

# clean
rm -rf yosys-*

# install ubuntu packets
if [ `lsb_release -si` == "Ubuntu" ]; then
sudo apt install -y build-essential clang bison flex \
     libreadline-dev gawk tcl-dev libffi-dev git \
     graphviz xdot pkg-config python3 libboost-system-dev \
     libboost-python-dev libboost-filesystem-dev zlib1g-dev
fi

# clone git repo
git clone https://github.com/YosysHQ/yosys.git yosys-git
cd yosys-git
git checkout $VERSION

# compile
make config-gcc
make -j`nproc`

# copy
cd ..
mkdir -p bin-yosys
cp yosys-git/yosys bin-yosys/

# print
./bin-yosys/yosys -V
