.PHONY: build test clean help

build:
	swift build

test:
	swift test

clean:
	swift package clean

help:
	@echo "Colibrì-DB Makefile"
	@echo "  make build - Build project"
	@echo "  make test  - Run tests"
	@echo "  make clean - Clean build"

