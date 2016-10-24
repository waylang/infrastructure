#! /usr/bin/env bats

@test 'bin is a directory' {
  test -d bin
}

@test 'bin/bats is a soft link' {
  test -L bin/bats
}

@test 'bin/bats resolves' {
  test -e bin/bats
}

@test 'bin/bump-version is a soft link' {
  test -L bin/bump-version
}

@test 'bin/bump-version resolves' {
  test -e bin/bump-version
}

@test 'provisioning is a directory' {
  test -d provisioning
}

@test 'provisioning/common is a file' {
  test -f provisioning/common
}

@test 'provisioning/vagrant is a file' {
  test -f provisioning/vagrant
}

@test '.editorconfig is a file' {
  test -f .editorconfig
}

@test '.gitignore is a file' {
  test -f .gitignore
}

@test '.gitignore ignores vagrant dir' {
  egrep -q '\.vagrant' .gitignore
}

@test '.gitmodules does not include github ssh urls' {
  # It doesn't have to exist
  test ! -e .gitmodules || ! egrep -q 'git@github\.com' .gitmodules
}

@test 'Makefile is a file' {
  test -f Makefile
}

@test 'README.md is a file' {
  test -f README.md
}

@test 'Vagrantfile is a file' {
  test -f Vagrantfile
}

@test 'version is a file' {
  test -f version
}

@test 'version is one line' {
  run wc -l version
  test "$output" = '1 version'
}

@test 'version content is dotted numeric triple' {
  egrep -q '^[0-9]+\.[0-9]+\.[0-9]+$' version
}
