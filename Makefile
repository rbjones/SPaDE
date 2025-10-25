.PHONY: all test python_test sml_test

SUBSYSTEMS := subsystems/python subsystems/sml

all: test

test:
	@echo "=== Top-level: running subsystem tests ==="
	@for d in $(SUBSYSTEMS); do \
	  if [ -f $$d/Makefile ]; then \
	    echo "-> running $$d tests"; \
	    $(MAKE) -C $$d test || exit $$?; \
	  else \
	    echo "-> no Makefile in $$d; skipping"; \
	  fi \
	done
	@echo "=== Top-level: tests complete ==="
