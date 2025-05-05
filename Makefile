.PHONY: all clean resources test

GREP = ggrep
GUILE = guile3
export GUILE_LOAD_PATH := $(CURDIR)/src:$(GUILE_LOAD_PATH)

all: help

run-all: ## Run all tests and examples
	@echo "Running all tests and examples..."
	@$(GUILE) -L src -s run-all.scm
	@echo "All tests and examples completed."

resources: ## Create resources directory
	mkdir -p $@

resources/recursive.pdf: resources ## Download McCarthy's original paper
	wget -O $@ https://www-formal.stanford.edu/jmc/recursive.pdf

src:
	mkdir -p $@

examples-dir:
	mkdir -p examples

tests:
	mkdir -p $@

docs:
	mkdir -p $@

setup: src examples-dir tests docs resources/recursive.pdf ## Setup the project structure and download the paper

clean: ## Clean the resources
	rm -rf resources/*.pdf

test: ## Run the tests
	@echo "Running tests..."
	@$(GUILE) -L src -s tests/test-core.scm
	@$(GUILE) -L src -s tests/test-evaluator.scm
	@$(GUILE) -L src -s tests/test-math-functions.scm
	@echo "All tests completed."

examples: ## Run example code
	@echo "Running examples..."
	@$(GUILE) -L src -s examples/math-functions.scm
	@echo "All examples completed."

trace: ## Run tests with tracing enabled
	@echo "Running tests with tracing..."
	@MCCARTHY_TRACE=1 $(GUILE) -L src -s tests/test-core.scm
	@MCCARTHY_TRACE=1 $(GUILE) -L src -s tests/test-evaluator.scm
	@MCCARTHY_TRACE=1 $(GUILE) -L src -s tests/test-math-functions.scm
	@echo "All traced tests completed."

help: ## Show this help menu
	@echo 'Usage: make [TARGET]'
	@echo ''
	@echo 'TARGETS:'
	@$(GREP) -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'
