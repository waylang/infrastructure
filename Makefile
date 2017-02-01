# vim: filetype=make
# Copyright (C) 2016-2017 Philip H. Smith

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

include vendor/infrastructure/make/common

default: tests

travis: tests

compile:
	coqtop.opt -R src '' -compile Way

tests: check-metatheory infrastructure-tests

check-metatheory: compile
	coqchk.opt -R src '' Way

clean:
	find src -type f '(' -name '*.glob' -o -name '*.vo' ')' -exec rm '{}' ';'
