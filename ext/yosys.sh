#!/usr/bin/env bash
# https://github.com/YosysHQ/yosys

# clean
rm -rf yosys-*

# install ubuntu packets
if [ `lsb_release -si` == "Ubuntu" ]; then
sudo apt install -y build-essential clang bison flex \
     libreadline-dev gawk tcl-dev libffi-dev git \
     graphviz xdot pkg-config python3 libboost-system-dev \
     libboost-python-dev libboost-filesystem-dev zlib1g-dev
fi

# download
wget https://github.com/YosysHQ/yosys/archive/yosys-0.9.zip
unzip yosys-0.9.zip
cd yosys-yosys-0.9

# compile
make -j`nproc`

# copy
cd ..
mkdir -p bin-z3
cp yosys-yosys-0.9/yosys bin-z3/
