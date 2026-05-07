.PHONY: help build check check-all check-fresh clean clean-all gen prove repl status test test-cache

# Symlink-friendly: re-resolve PP2LP_ROOT every Make invocation.
export PP2LP_ROOT := $(CURDIR)

PP2LP := ocaml/_build/default/bin/main.exe

SUITE ?= prv

help:
	@echo "Targets (default SUITE=$(SUITE); set SUITE=og for the og suite):"
	@echo "  build               build the OCaml binary"
	@echo "  check               cached check on SUITE (fast-fails on first error)"
	@echo "  check-all           cached check on SUITE, report every failure"
	@echo "  check-fresh         wipe cache + .lpo, then check-all"
	@echo "  test NAME=Y         single-test run on SUITE (bypasses cache)"
	@echo "  test-cache          dune unit tests for the cache module"
	@echo "  gen [ALLOC=N]       regenerate replays for SUITE"
	@echo "  prove FORMULA=...   prove a formula on the fly"
	@echo "  status              pass/fail/gen-fail counts (all suites)"
	@echo "  clean               clear SUITE's cache + outputs"
	@echo "  clean-all           full reset across every suite + .lpo + dune"
	@echo "  repl                OCaml REPL with project loaded"
	@echo "Optional: JOB=PFX filters check/check-all/check-fresh by name prefix."

build:
	@cd ocaml && dune build

repl:
	@cd ocaml && dune utop src -- -init .utop-init.ml

check: build
	@$(PP2LP) check --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

check-all: build
	@$(PP2LP) check --all-failures --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

check-fresh: build
	@$(PP2LP) check --fresh --all-failures --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

# Single-test (bypasses cache). Errors if the replay is missing.
# Usage: make test NAME=Foo [SUITE=prv]
test: build
	@[ -n "$(NAME)" ] || { echo "Usage: make test NAME=<test> [SUITE=$(SUITE)]"; exit 1; }
	@replay="bench/$(SUITE)/$(NAME).replay"; \
	  [ -f "$$replay" ] || { echo "No replay $$replay"; exit 1; }
	@$(PP2LP) check --suite=$(SUITE) --name=$(NAME)

test-cache:
	@cd ocaml && dune test --force 2>&1 | sed 's/^/  /'

gen: build
	@$(PP2LP) gen --suite=$(SUITE) $(if $(ALLOC),--alloc=$(ALLOC))

prove: build
	@[ -n "$(FORMULA)" ] || { echo "Usage: make prove FORMULA='(p and q) => (q and p)'"; exit 1; }
	@$(PP2LP) prove $(if $(NAME),--name $(NAME)) '$(subst ','\'',$(FORMULA))'

status: build
	@$(PP2LP) status

# Per-suite reset. og's replays are checked in, so only prv loses traces/replays.
clean: build
	@$(PP2LP) clean --cache --suite=$(SUITE)
	@rm -rf lp/bench/$(SUITE)
	@rm -f bench/$(SUITE)/.gen_status.tsv
	@if [ "$(SUITE)" = "prv" ]; then rm -f bench/prv/*.trace bench/prv/*.replay; fi

clean-all: build
	@$(PP2LP) clean --all
	@rm -rf lp/bench
	@rm -f bench/*/.gen_status.tsv
	@rm -f bench/prv/*.trace bench/prv/*.replay
