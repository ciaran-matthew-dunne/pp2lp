.PHONY: build check check-fresh clean prove status gen test test-cache repl

# Symlink-friendly: re-resolve PP2LP_ROOT every Make invocation.
export PP2LP_ROOT := $(CURDIR)

PP2LP := ocaml/_build/default/bin/main.exe

SUITE ?= prv

build:
	@cd ocaml && dune build

repl:
	@cd ocaml && dune utop src -- -init .utop-init.ml

check: build
	@$(PP2LP) check --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

check-fresh: build
	@$(PP2LP) check --fresh --all-failures --suite=$(SUITE) $(if $(JOB),--job=$(JOB))

# Single-test (bypasses cache). Synth-based suites regen .but/.replay if missing.
# Usage: make test SUITE=prv NAME=Foo  |  make test-foo  (≡ SUITE=claude)
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

test-cache:
	@cd ocaml && dune test --force 2>&1 | sed 's/^/  /'

gen: build
	@$(PP2LP) gen --suite=$(SUITE) $(if $(ALLOC),--alloc=$(ALLOC))

prove: build
	@[ -n "$(FORMULA)" ] || { echo "Usage: make prove FORMULA='(p and q) => (q and p)'"; exit 1; }
	@$(PP2LP) prove $(if $(NAME),--name $(NAME)) '$(subst ','\'',$(FORMULA))'

status: build
	@$(PP2LP) status

clean: build
	@$(PP2LP) clean --all
	@rm -f bench/*/*.lp bench/*/lambdapi.pkg bench/*/.gen_status.tsv
	@rm -f bench/claude/*.but bench/claude-arith/*.but
	@rm -f bench/claude/*.trace bench/claude/*.replay \
	       bench/claude-arith/*.trace bench/claude-arith/*.replay \
	       bench/prv/*.trace bench/prv/*.replay
