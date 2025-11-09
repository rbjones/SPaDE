# SPaDE Project Makefile
# Synthetic Philosophy and Deductive Engineering

.PHONY: all build clean current di dk kr test help

# Default target
current: kr-test

all: di dk kr

# Component targets with argument passthrough
di-%:
	$(MAKE) -C di $*

dk-%:
	$(MAKE) -C dk $*

kr-%:
	$(MAKE) -C kr -f krci001.mkf $*

# Shorthand targets
di: di-all
dk: dk-all
kr: kr-all

# Build
build: di-build dk-build kr-build

# Testing
test: di-test dk-test kr-test

%-test: %-build

# Cleanup
clean: di-clean dk-clean kr-clean

# Help
help:
	@echo "SPaDE Project - Synthetic Philosophy and Deductive Engineering"
	@echo ""
	@echo "Available targets:"
	@echo "  all           - Build all components"
	@echo "  di            - Build deductive intelligence"
	@echo "  dk            - Build deductive kernel"
	@echo "  kr            - Build knowledge repository"
	@echo ""
	@echo "Component-specific targets:"
	@echo "  di-<target>   - Run <target> in di directory"
	@echo "  dk-<target>   - Run <target> in dk directory"
	@echo "  kr-<target>   - Run <target> in kr directory"
	@echo ""
	@echo "Common operations:"
	@echo "  build         - Run all tests"
	@echo "  test          - Run all tests"
	@echo "  clean         - Clean all builds"
	@echo ""
	@echo "Examples:"
	@echo "  make dk-test    # Run tests in dk directory"
	@echo "  make kr-clean   # Clean kr directory"
