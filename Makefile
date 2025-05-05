.PHONY: all clean resources test deps

GREP = ggrep
GUILE = guile3
export GUILE_LOAD_PATH := $(CURDIR)/src:$(GUILE_LOAD_PATH)

deps: ## Install dependencies
	@scripts/deps.sh

.init: 
	opam init
	eval `opam env`
	opam install coq-stdlib

init: .init ## Initialize repository 
	touch .init

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

test: scheme-test coq-test ## Run all tests (Scheme and Coq)
	@echo "All tests completed."

scheme-test: ## Run Scheme tests
	@echo "Running Scheme tests..."
	@$(GUILE) -L src -s tests/test-core.scm
	@$(GUILE) -L src -s tests/test-evaluator.scm
	@$(GUILE) -L src -s tests/test-math-functions.scm
	@$(GUILE) -L src -s tests/test-mccarthy-functions.scm
	@echo "Scheme tests completed."

coq-test: ## Run Coq proofs
	@echo "Running Coq proofs..."
	@cd proofs && bash ./setup.sh && coqc all_tests.v
	@echo "Coq proofs completed."

examples: ## Run example code
	@echo "Running examples..."
	@$(GUILE) -L src -s examples/math-functions.scm
	@$(GUILE) -L src -s examples/mccarthy-examples.scm
	@$(GUILE) -L src -s examples/mccarthy-1960.scm
	@echo "All examples completed."

trace: ## Run Scheme tests with tracing enabled
	@echo "Running Scheme tests with tracing..."
	@MCCARTHY_TRACE=1 $(GUILE) -L src -s tests/test-core.scm
	@MCCARTHY_TRACE=1 $(GUILE) -L src -s tests/test-evaluator.scm
	@MCCARTHY_TRACE=1 $(GUILE) -L src -s tests/test-math-functions.scm
	@MCCARTHY_TRACE=1 $(GUILE) -L src -s tests/test-mccarthy-functions.scm
	@echo "All traced tests completed."

tangle: ## Tangle code from coq-proofs.org
	@echo "Tangling coq-proofs.org..."
	@emacs --batch --eval "(load-file \"mccarthy-tangle.el\")" --eval "(require 'org)" \
		--eval "(org-babel-tangle-file \"coq-proofs.org\")"
	@echo "Tangling complete."

tangle-all: ## Tangle code from all Org files
	@echo "Tangling all org files..."
	@emacs --batch --eval "(load-file \"mccarthy-tangle.el\")" --eval "(require 'org)" \
		--eval "(mapc #'org-babel-tangle-file '(\"coq-proofs.org\" \"EXERCISES.org\"))"
	@echo "Tangling all files complete."

org-exercises: ## Load org and run all scheme src blocks in EXERCISES.org
	@echo "Running exercises from EXERCISES.org..."
	@emacs --batch --eval "(load-file \"mccarthy-tangle.el\")" --eval "(require 'org)" \
		--eval "(with-temp-buffer (insert-file-contents \"EXERCISES.org\") (org-mode) (org-babel-execute-buffer))"
	@echo "Exercises completed."

presentation.pdf: presentation.org ## McCarthy ...
	@echo "Slides built"

help: ## Show this help menu
	@echo 'Usage: make [TARGET]'
	@echo ''
	@echo 'TARGETS:'
	@$(GREP) -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'
