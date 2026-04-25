.PHONY: build check check-all check-fresh clean-lpo gen clean prove status coverage test \
        check-claude check-claude-arith check-prv check-og check-fuzz \
        gen-claude gen-claude-arith gen-prv gen-fuzz gen-all test-cache

# Symlink-friendly: re-resolve PP2LP_ROOT every Make invocation.
export PP2LP_ROOT := $(CURDIR)

PP2LP := ocaml/_build/default/bin/main.exe

SUITE ?= prv

# -- Build --------------------------------------------------------------------
build:
	@cd ocaml && dune build

# -- Check (orchestration goes through the OCaml CLI) ------------------------
check: build
	@$(PP2LP) check --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

check-all: build
	@$(PP2LP) check --all-failures --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

check-fresh: build
	@$(PP2LP) check --fresh --all-failures --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

check-claude:;       @$(MAKE) --no-print-directory check-all SUITE=claude
check-claude-arith:; @$(MAKE) --no-print-directory check-all SUITE=claude-arith
check-prv:;          @$(MAKE) --no-print-directory check-all SUITE=prv
check-og:;           @$(MAKE) --no-print-directory check-all SUITE=og
check-fuzz:;         @$(MAKE) --no-print-directory check-all SUITE=fuzz

# -- Single-test (bypasses cache) --------------------------------------------
# Usage: make test SUITE=prv NAME=Foo
#        make test-foo                  (shortcut: SUITE=claude NAME=foo)
# Synth-based suites regenerate .but/.replay on demand if missing.
test: build
	@[ -n "$(NAME)" ] || { echo "Usage: make test SUITE=<suite> NAME=<test>"; exit 1; }
	@dir="bench/$(SUITE)"; replay="$$dir/$(NAME).replay"; \
	  if [ ! -f "$$replay" ]; then \
	    case "$(SUITE)" in claude|claude-arith) \
	      [ -f "$$dir/$(NAME).but" ] || $(PP2LP) synth $$dir/goals.txt $$dir >/dev/null; \
	      [ -f "$$dir/$(NAME).but" ] || { echo "No goal '$(NAME)' in $$dir/goals.txt"; exit 1; }; \
	      python3 bench/gen_traces.py -q -o $$dir "$$dir/$(NAME).but" >/dev/null; \
	      [ -f "$$replay" ] || { echo "PP/REPLAY failed for $(NAME)"; exit 1; } ;; \
	    *) echo "No replay $$replay (suite '$(SUITE)' has no goals.txt)"; exit 1 ;; \
	  esac; fi
	@$(PP2LP) check --suite=$(SUITE) --name=$(NAME)

test-%:
	@$(MAKE) --no-print-directory test SUITE=claude NAME=$*

# -- Cache tests --------------------------------------------------------------
test-cache:
	@cd ocaml && dune test --force 2>&1 | sed 's/^/  /'

# -- Generation (gen_traces.py wrapped via pp2lp gen) ------------------------
gen: build
	@$(PP2LP) gen --suite=$(SUITE) $(if $(ALLOC),--alloc=$(ALLOC))

gen-claude:;       @$(MAKE) --no-print-directory gen SUITE=claude
gen-claude-arith:; @$(MAKE) --no-print-directory gen SUITE=claude-arith
gen-prv:;          @$(MAKE) --no-print-directory gen SUITE=prv
gen-fuzz:;         @$(MAKE) --no-print-directory gen SUITE=fuzz
gen-all: build;    @$(PP2LP) gen --all

# -- Round-trip prove ---------------------------------------------------------
prove: build
	@[ -n "$(FORMULA)" ] || { echo "Usage: make prove FORMULA='(p and q) => (q and p)'"; exit 1; }
	@$(PP2LP) prove $(if $(NAME),--name $(NAME)) '$(subst ','\'',$(FORMULA))'

# -- Reporting ----------------------------------------------------------------
status:   build; @$(PP2LP) status
coverage: build; @$(PP2LP) coverage --by-suite

# -- Cleanup ------------------------------------------------------------------
clean-lpo: build
	@$(PP2LP) clean --lpo

clean: build
	@$(PP2LP) clean --all
	@rm -f bench/claude/*.but bench/claude/*.trace bench/claude/*.replay \
	       bench/claude/*.lp bench/claude/lambdapi.pkg \
	       bench/claude-arith/*.but bench/claude-arith/*.trace bench/claude-arith/*.replay \
	       bench/claude-arith/*.lp bench/claude-arith/lambdapi.pkg \
	       bench/prv/*.trace bench/prv/*.replay bench/prv/*.lp bench/prv/lambdapi.pkg \
	       bench/og/*.lp bench/og/lambdapi.pkg \
	       bench/fuzz/*.trace bench/fuzz/*.replay bench/fuzz/*.lp bench/fuzz/lambdapi.pkg
	@rm -f bench/*/.gen_status.tsv
