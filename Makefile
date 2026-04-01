.PHONY: build unit-test test test-each test-prv test-prv-each test-prv-complete gen-prv clean

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

# --- Test all 30 traces (stop on first failure) ---
test-each: build
	@mkdir -p lp/gen
	@pass=0; \
	for r in test/traces/*.trace.replay; do \
	  n=$$(basename $$r .trace.replay); \
	  $(PP2LP) emit $$r > lp/gen/trace_$$n.lp 2>/dev/null; \
	  if (cd lp && $(LP_CHECK) gen/trace_$$n.lp) >/dev/null 2>&1; then \
	    pass=$$((pass+1)); \
	  else \
	    echo "FAIL trace $$n ($$pass passed before failure)"; \
	    echo "  Debug: make test-$$n"; \
	    exit 1; \
	  fi; \
	done; \
	echo "$$pass pass, 0 fail"

# --- Test all traces in one file ---
test: build
	@mkdir -p lp/gen
	$(PP2LP) emit test/traces/*.trace.replay > lp/gen/Traces.lp
	cd lp && $(LP_CHECK) gen/Traces.lp

# --- Test single PRV replay: make prv-arith_ineq_001, etc. ---
prv-%: build
	@mkdir -p lp/gen/prv
	$(PP2LP) emit test/prv/gen/replay/$*.replay > lp/gen/prv/$*.lp
	cd lp && $(LP_CHECK) gen/prv/$*.lp

# --- Test PRV replays (all, summary) ---
test-prv: build
	@mkdir -p lp/gen/prv
	$(PP2LP) emit $(if $(FILTER),$(wildcard test/prv/gen/replay/$(FILTER)*.replay),test/prv/gen/replay/*.replay) > lp/gen/prv/Traces.lp
	cd lp && $(LP_CHECK) gen/prv/Traces.lp

# --- Test PRV replays individually, report PASS/FAIL ---
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

# --- Show error messages for failing PRV tests ---
test-prv-errors: build
	@mkdir -p lp/gen/prv
	@for r in $(if $(FILTER),$(wildcard test/prv/gen/replay/$(FILTER)*.replay),test/prv/gen/replay/*.replay); do \
	  n=$$(basename $$r .replay); \
	  $(PP2LP) emit $$r > lp/gen/prv/$$n.lp 2>/dev/null; \
	  out=$$(cd lp && $(LP_CHECK) gen/prv/$$n.lp 2>&1); \
	  if ! echo "$$out" | grep -q '"status":"ok"'; then \
	    msg=$$(echo "$$out" | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); print(d.get('message','?').split(chr(10))[0][:120])" 2>/dev/null || echo "$$out" | head -c 120); \
	    printf "FAIL %-25s %s\n" "$$n" "$$msg"; \
	  fi; \
	done

# --- Test complete PRV replays (stop on first failure) ---
# Only tests replays where REPLAY fully expanded the trace.
# List maintained in test/prv/complete_replays.txt.
PRV_COMPLETE := $(shell grep -v '^\#' test/prv/complete_replays.txt 2>/dev/null | sed '/^$$/d')
test-prv-complete: build
	@mkdir -p lp/gen/prv
	@pass=0; \
	for n in $(PRV_COMPLETE); do \
	  r=test/prv/gen/replay/$$n.replay; \
	  if $(PP2LP) emit $$r > lp/gen/prv/$$n.lp 2>/dev/null && \
	     (cd lp && $(LP_CHECK) gen/prv/$$n.lp) >/dev/null 2>&1; then \
	    pass=$$((pass+1)); \
	  else \
	    echo "FAIL $$n ($$pass passed before failure)"; \
	    echo "  Debug: make prv-$$n"; \
	    exit 1; \
	  fi; \
	done; \
	echo "$$pass pass, 0 fail (of $$(echo $(PRV_COMPLETE) | wc -w) complete replays)"

# --- Generate PRV traces and replays from .but files ---
gen-prv:
	python3 test/gen_traces.py test/prv

# --- Clean ---
clean:
	cd ocaml && dune clean
	rm -rf lp/gen
	rm -f .pp2lp-cache
