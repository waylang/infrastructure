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
	coqtop.opt -I src/Way -as Way -compile Tactics
	coqtop.opt -I src/Way -as Way -compile Nat
	coqtop.opt -I src/Way -as Way -compile List
	coqtop.opt -I src/Way -as Way -compile ListNat
	coqtop.opt -I src/Way -as Way -compile Atom
	coqtop.opt -I src/Way -as Way -compile Preterm
	coqtop.opt -I src/Way -as Way -compile Context
	coqtop.opt -I src/Way -as Way -compile FreeVariables
	coqtop.opt -I src/Way -as Way -compile StaleAtoms
	coqtop.opt -I src/Way -as Way -compile Relation
	coqtop.opt -I src/Way -as Way -compile Open
	coqtop.opt -I src/Way -as Way -compile Term
	coqtop.opt -I src/Way -as Way -compile Beta
	coqtop.opt -I src/Way -as Way -compile Conversion
	coqtop.opt -I src/Way -as Way -compile Subtyping
	coqtop.opt -I src/Way -as Way -compile Typing
	coqtop.opt -I src/Way -as Way -compile Repl

tests: check-metatheory infrastructure-tests

check-metatheory: compile
	coqchk.opt -R src '' Way.Repl

repl:
	rlwrap -pGREEN coqtop.opt -R src '' -require Repl

clean:
	find src -type f '(' -name '*.glob' -o -name '*.vo' ')' -exec rm '{}' ';'
