#!/usr/bin/env bash

# using a sbt plugin
# this script is a hack to work around
# https://github.com/djspiewak/sbt-github-packages/issues/16

set -e

mkdir -p project
cp publish/plugins.sbt project/plugins.sbt
cp build.sbt build.sbt.bck
cat publish/build.foot >> build.sbt
sbt publish

# clean up
rm project/plugins.sbt
mv build.sbt.bck build.sbt
