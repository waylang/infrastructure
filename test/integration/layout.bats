#! /usr/bin/env bats
# vim: filetype=sh

# Copyright (C) 2016-2017 Philip H. Smith

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

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

@test 'bin/check-boilerplate is a soft link' {
  test -L bin/check-boilerplate
}

@test 'bin/check-boilerplate resolves' {
  test -e bin/check-boilerplate
}

@test 'bin/release-to-github is a soft link' {
  test -L bin/release-to-github
}

@test 'bin/release-to-github resolves' {
  test -e bin/release-to-github
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

@test 'GPL-3 is a file' {
  test -f GPL-3
}

@test 'LICENSE is a file' {
  test -f LICENSE
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

@test 'files have their boilerplate' {
  ./bin/check-boilerplate
}
