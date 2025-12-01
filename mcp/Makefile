# SPaDE mcp Makefile
# Model Context Protocol Subsystem

.PHONY: all clean current mcp docs test help

# Python source files to be checked
PYMODULES = mcpcd001.py mcpcd002.py mcpte001.py

# Python test scripts to be run
PYTESTS = mcpte001.py

include ../common/rules.mkf

LDDS=$(PYCHECKLDD) $(PYTESTLDD)

# Default target
default: test

# Targets

check: $(PYCHECKLDD)

build: check

test: build $(PYTESTLDD)

clean:
	rm -f $(LDDS) *.err
	rm -f **/__pycache__/*.pyc 2>/dev/null || true
	rm -rf **/__pycache__ 2>/dev/null || true
