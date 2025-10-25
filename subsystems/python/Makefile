.PHONY: test venv install-dev clean

VENV ?= .venv

test: install-dev
	@echo "Running python tests"
	if [ -d tests ]; then \
	  if [ -d $(VENV) ]; then \
	    . $(VENV)/bin/activate && pytest -q; \
	  else \
	    pytest -q || true; \
	  fi; \
	else \
	  echo "No tests directory found; skipping pytest"; \
	fi

venv:
	python3 -m venv $(VENV)
	@echo "Created virtualenv at $(VENV)"

install-dev: venv
	@echo "Installing dev dependencies (if requirements-dev.txt exists)"
	. $(VENV)/bin/activate && pip install --upgrade pip || true
	@if [ -f requirements-dev.txt ]; then . $(VENV)/bin/activate && pip install -r requirements-dev.txt || true; fi
	. $(VENV)/bin/activate && pip install pytest || true

clean:
	rm -rf $(VENV) dist build *.egg-info
