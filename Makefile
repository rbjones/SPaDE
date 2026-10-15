# SPaDE Project Makefile
# Synthetic Philosophy and Deductive Engineering

# This makefile no longer builds the spade database unless explicitly requested.
# When used for testing in a container,
# it expects the spade container to have the necessary database prebuilt.

.PHONY: all build clean current pa di dk kr test help

# Default target
default: test

# Component targets with argument passthrough
pa-%:
	$(MAKE) -C docs -f tlci001.mkf $*

kr-%:
	$(MAKE) -C kr -f krci001.mkf $*

dk-%:
	$(MAKE) -C dk -f dkci001.mkf $*

di-%:
#	$(MAKE) -C di $*

mcp-%:
	$(MAKE) -C mcp -f mcpci001.mkf $*

# Shorthand targets
di: di-all
dk: dk-all
kr: kr-all
mcp: mcp-all
pa: pa-all

# Check
check: pa-check kr-check # dk-check mcp-check di-check

# Build
build: check pa-build kr-build mcp-build # dk-build di-build

# Testing
test: build pa-test kr-test mcp-test # dk-test di-test

# Cleanup
clean: pa-clean kr-clean mcp-clean # dk-clean di-clean

# spade.ldd ProofPower database for SPaDE project

ppdb-clean:
	rm -f spade.ldd retro/spade.ldd

spade.ldd:
	$(MAKE) -C retro -f retro.mkf spade.ldd

# Help
help:
	@echo "SPaDE Project - Synthetic Philosophy and Deductive Engineering"
	@echo ""
	@echo "Available targets:"
	@echo ""
	@echo "  all		   - Build and test everything)"
	@echo ""
	@echo "  di            - Build deductive intelligence"
	@echo "  dk            - Build deductive kernel"
	@echo "  kr            - Build knowledge repository"
	@echo "  mcp           - Build MCP subsystem"
	@echo "  pa            - Build PA subsystem"
	@echo ""
	@echo "Component-specific targets:"
	@echo "  di-<target>   - Run <target> in di directory"
	@echo "  dk-<target>   - Run <target> in dk directory"
	@echo "  kr-<target>   - Run <target> in kr directory"
	@echo "  mcp-<target>  - Run <target> in mcp directory"
	@echo "  pa-<target>   - Run <target> in pa directory"
	@echo ""
	@echo "Common operations:"
	@echo "  build         - Build all components"
	@echo "  test          - Run all tests"
	@echo "  clean         - Clean all builds"
	@echo ""
	@echo "Examples:"
	@echo "  make dk-test    # Run tests in dk directory"
	@echo "  make kr-clean   # Clean kr directory"
