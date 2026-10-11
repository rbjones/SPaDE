# SPaDE Project Makefile
# Synthetic Philosophy and Deductive Engineering

.PHONY: all build clean current pa di dk kr test help

# Default target
current: pa-build kr-test mcp-test

all: pa kr dk di mcp

# Component targets with argument passthrough
di-%:
	$(MAKE) -C di $*

dk-%:
	$(MAKE) -C dk $*

kr-%:
	$(MAKE) -C kr -f krci001.mkf $*

mcp-%:
	$(MAKE) -C mcp -f mcpci001.mkf $*

pa-%:
	$(MAKE) -C pa -f tlci001.mkf $*

# Shorthand targets
di: di-all
dk: dk-all
kr: kr-all
mcp: mcp-all
pa: pa-all

# Build
build: di-build dk-build kr-build mcp-build pa-build

# Testing
test: di-test dk-test kr-test mcp-test

%-test: %-build

# Cleanup
clean: kr-clean mcp-clean di-clean dk-clean pa-clean

# Help
help:
	@echo "SPaDE Project - Synthetic Philosophy and Deductive Engineering"
	@echo ""
	@echo "Available targets:"
	@echo "  all           - Build all components"
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
