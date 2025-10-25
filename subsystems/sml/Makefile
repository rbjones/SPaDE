.PHONY: test local-test

test:
	@echo "SML test target: run the SML proof/convert process"
	@if [ -x ../../.ci/run_sml.sh ]; then \
	  ../../.ci/run_sml.sh; \
	else \
	  echo "Please add an executable .ci/run_sml.sh to run the ProofPower/PolyML conversion"; \
	  exit 1; \
	fi

local-test:
	@echo "Local SML test: you can edit this target to run your local ProofPower/PolyML commands"
	@echo "Done (placeholder)"
