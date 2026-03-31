.PHONY: build unit-test test test-each test-prv test-prv-each gen-prv clean

PP2LP := dune exec --root ocaml -- pp2lp
LP_CHECK = lambdapi check --json

# --- Build ---
build:
	cd ocaml && dune build

# --- OCaml unit tests ---
unit-test: build
	dune exec --root ocaml -- ../ocaml/_build/default/test/test_pp2lp.exe

# --- Test single trace: make test-01, make test-14, etc. ---
test-%: build
	@mkdir -p lp/gen
	$(PP2LP) emit test/traces/$*.trace.replay > lp/gen/trace_$*.lp
	cd lp && $(LP_CHECK) gen/trace_$*.lp

# --- Test all 30 traces individually, report PASS/FAIL ---
test-each: build
	@mkdir -p lp/gen
	@pass=0; fail=0; fails=""; \
	for r in test/traces/*.trace.replay; do \
	  n=$$(basename $$r .trace.replay); \
	  $(PP2LP) emit $$r > lp/gen/trace_$$n.lp; \
	  if (cd lp && $(LP_CHECK) gen/trace_$$n.lp) >/dev/null 2>&1; then \
	    pass=$$((pass+1)); \
	  else \
	    fail=$$((fail+1)); fails="$$fails $$n"; \
	  fi; \
	done; \
	echo "$$pass pass, $$fail fail"; \
	if [ -n "$$fails" ]; then echo "FAIL:$$fails"; fi

# --- Test all traces in one file (original behavior) ---
test: build
	@mkdir -p lp/gen
	$(PP2LP) emit test/traces/*.trace.replay > lp/gen/Traces.lp
	cd lp && $(LP_CHECK) gen/Traces.lp

# --- Test single PRV replay: make prv-arith_ineq_001, etc. ---
# Generates lp/gen/prv/<name>.lp for inspection with lambdapi_check/goals.
prv-%: build
	@mkdir -p lp/gen/prv
	$(PP2LP) emit test/prv/gen/replay/$*.replay > lp/gen/prv/$*.lp
	cd lp && $(LP_CHECK) gen/prv/$*.lp

# --- Test PRV replays ---
# Usage:
#   make test-prv                    # test all PRV replays
#   make test-prv FILTER=arith       # test only arith_* replays
test-prv: build
	@mkdir -p lp/gen/prv
	$(PP2LP) emit $(if $(FILTER),$(wildcard test/prv/gen/replay/$(FILTER)*.replay),test/prv/gen/replay/*.replay) > lp/gen/prv/Traces.lp
	cd lp && $(LP_CHECK) gen/prv/Traces.lp

# --- Test PRV replays individually, report PASS/FAIL ---
# Usage:
#   make test-prv-each                 # test all PRV replays
#   make test-prv-each FILTER=arith    # test only arith_* replays
test-prv-each: build
	@mkdir -p lp/gen/prv
	@pass=0; fail=0; fails=""; \
	for r in $(if $(FILTER),$(wildcard test/prv/gen/replay/$(FILTER)*.replay),test/prv/gen/replay/*.replay); do \
	  n=$$(basename $$r .replay); \
	  if $(PP2LP) emit $$r > lp/gen/prv/$$n.lp 2>/dev/null && \
	     (cd lp && $(LP_CHECK) gen/prv/$$n.lp) >/dev/null 2>&1; then \
	    printf "PASS %s\n" "$$n"; \
	    pass=$$((pass+1)); \
	  else \
	    printf "FAIL %s\n" "$$n"; \
	    fail=$$((fail+1)); fails="$$fails $$n"; \
	  fi; \
	done; \
	echo "---"; \
	echo "$$pass pass, $$fail fail"; \
	if [ -n "$$fails" ]; then echo "FAIL:$$fails"; fi

# --- Generate PRV traces and replays from .but files ---
gen-prv:
	python3 test/gen_traces.py test/prv

# --- Clean ---
clean:
	cd ocaml && dune clean
	rm -rf lp/gen
	rm -f .pp2lp-cache
