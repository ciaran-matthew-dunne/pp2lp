.PHONY: build test test-each test-prv gen-prv clean

PP2LP := dune exec --root ocaml -- pp2lp

# --- Build ---
build:
	cd ocaml && dune build

# --- Test single trace: make test-01, make test-14, etc. ---
test-%: build
	@mkdir -p lp/gen
	$(PP2LP) emit test/traces/$*.trace.replay > lp/gen/trace_$*.lp
	cd lp && lambdapi check gen/trace_$*.lp

# --- Test all 30 traces individually, report PASS/FAIL ---
test-each: build
	@mkdir -p lp/gen
	@pass=0; fail=0; fails=""; \
	for r in test/traces/*.trace.replay; do \
	  n=$$(basename $$r .trace.replay); \
	  $(PP2LP) emit $$r > lp/gen/trace_$$n.lp 2>/dev/null; \
	  if (cd lp && lambdapi check gen/trace_$$n.lp) >/dev/null 2>&1; then \
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
	cd lp && lambdapi check gen/Traces.lp

# --- Test PRV replays ---
# Usage:
#   make test-prv                    # test all PRV replays
#   make test-prv FILTER=arith       # test only arith_* replays
test-prv: build
	@mkdir -p lp/gen/prv
	$(PP2LP) emit $(if $(FILTER),$(wildcard test/prv/gen/replay/$(FILTER)*.replay),test/prv/gen/replay/*.replay) > lp/gen/prv/Traces.lp
	cd lp && lambdapi check gen/prv/Traces.lp

# --- Generate PRV traces and replays from .but files ---
gen-prv:
	python3 test/gen_traces.py test/prv

# --- Clean ---
clean:
	cd ocaml && dune clean
	rm -rf lp/gen
	rm -f .pp2lp-cache
