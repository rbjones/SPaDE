# SPaDE Project Makefile
# Synthetic Philosophy and Deductive Engineering

.PHONY: all clean dk kr docs test help

# Default target
all: dk kr docs

# Component targets with argument passthrough
dk-%:
	$(MAKE) -C dk $*

kr-%:
	$(MAKE) -C kr $*

docs-%:
	$(MAKE) -C docs $*

# Shorthand targets
dk: dk-all
kr: kr-all
docs: docs-all

# Testing
test: test-dk test-kr
test-dk: dk-test
test-kr: kr-test

# Cleanup
clean: clean-dk clean-kr clean-docs
clean-dk: dk-clean
clean-kr: kr-clean
clean-docs: docs-clean

# Documentation
build-docs: docs-build
serve-docs: docs-serve

# Development
dev: dev-dk dev-kr
dev-dk: dk-dev
dev-kr: kr-dev

# Help
help:
	@echo "SPaDE Project - Synthetic Philosophy and Deductive Engineering"
	@echo ""
	@echo "Available targets:"
	@echo "  all           - Build all components"
	@echo "  dk            - Build deductive kernel"
	@echo "  kr            - Build knowledge repository"
	@echo "  docs          - Build documentation"
	@echo ""
	@echo "Component-specific targets:"
	@echo "  dk-<target>   - Run <target> in dk directory"
	@echo "  kr-<target>   - Run <target> in kr directory"
	@echo "  docs-<target> - Run <target> in docs directory"
	@echo ""
	@echo "Common operations:"
	@echo "  test          - Run all tests"
	@echo "  clean         - Clean all builds"
	@echo "  build-docs    - Build documentation"
	@echo "  serve-docs    - Serve documentation locally"
	@echo "  dev           - Start development mode"
	@echo ""
	@echo "Examples:"
	@echo "  make dk-test    # Run tests in dk directory"
	@echo "  make kr-clean   # Clean kr directory"
	@echo "  make docs-serve # Serve docs locally"
