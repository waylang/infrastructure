include make/common

default: tests

travis: tests

tests: integration

integration:
	bats test/integration
