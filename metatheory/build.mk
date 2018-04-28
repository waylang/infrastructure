# vim: filetype=make
# Copyright (C) 2016-2018 Philip H. Smith

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

COQ_SRCS := $(wildcard metatheory/Way/*.v)
COQ_DEPS := $(patsubst metatheory/Way/%.v,$(BUILD)/Way/%.d,$(COQ_SRCS))
COQ_OBJS := $(patsubst metatheory/Way/%.v,$(BUILD)/Way/%.vo,$(COQ_SRCS))

ALL += $(COQ_OBJS)

TEST += verify-metatheory

.PHONY: verify-metatheory
verify-metatheory: $(COQ_OBJS)
	coqchk.opt -R $(BUILD) '' Way.Repl

.PHONY: coq-repl
coq-repl: $(COQ_OBJS)
	rlwrap -pGREEN coqtop.opt -R $(BUILD) '' -require Repl

$(BUILD)/Way: | $(BUILD)
	mkdir -p $(BUILD)/Way

$(BUILD)/Way/%.d: metatheory/Way/%.v | $(BUILD)/Way
	coqdep -I metatheory/Way -as Way $< | sed 's|metatheory|$(BUILD)|g' > $@

include $(COQ_DEPS)

# coqc is simply unable to build files in a separate directory, so copy over the source
$(BUILD)/Way/%.v: metatheory/Way/%.v | $(BUILD)/Way
	cp $< $@

$(BUILD)/Way/%.vo: $(BUILD)/Way/%.v
	coqc -opt -noglob -I $(BUILD)/Way -as Way $<
