#! /usr/bin/env bats
# vim: filetype=sh

# Copyright (C) 2016-2016 Philip H. Smith

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

function setup {
  export ROOT=$(pwd)
  export EXAMPLE_PROJECT=$(mktemp --tmpdir -d example-project-XXXX)
  export TEST=true
  export SOFTLINK=~/$(basename $EXAMPLE_PROJECT)
  cd $EXAMPLE_PROJECT
}

@test 'install runs' {
  $ROOT/install
}

@test 'install stages all generated files' {
  run $ROOT/install
  git diff --exit-code
}

@test 'install output passes infrastructure tests' {
  run $ROOT/install
  make infrastructure-tests
}

function teardown {
  rm -rf $EXAMPLE_PROJECT
  test -L $SOFTLINK && rm $SOFTLINK
}
