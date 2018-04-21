#! /usr/bin/env bats
# vim: filetype=sh

# Copyright (C) 2016-2018 Philip H. Smith

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

@test 'bats is executable' {
  type bats
}

@test 'bump-version is executable' {
  type bump-version
}

@test 'check-boilerplate is executable' {
  type check-boilerplate
}

@test 'release-to-github is executable' {
  type release-to-github
}

@test 'make is executable' {
  type make
}

@test 'sha256sum is executable' {
  type sha256sum
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
  check-boilerplate
}
