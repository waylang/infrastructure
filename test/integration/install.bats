#! /usr/bin/env bats

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
