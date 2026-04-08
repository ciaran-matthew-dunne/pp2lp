.PHONY: build check gen clean

PP2LP        := dune exec --root ocaml -- pp2lp
LP_CHECK      = lambdapi check --json
FORMAT_ERROR  = PP2LP_ROOT=$(CURDIR) python3 test/format_error.py

# -- Expected failures (known issues, tolerated by check) ---------------------
XFAIL =

# -- Benchmark suite ----------------------------------------------------------
TESTS = trace_01 trace_02 trace_14 trace_18 trace_19 trace_26 \
        arith_ineq_001 arith_ineq_003 negation_001 general_005 \
        equality_002 equality_004 equality_005 range_eq_001 \
        range_subset_001 set_product_001 set_product_004 \
        set_subset_001 set_type_001

# -- Replay generation --------------------------------------------------------
# replay/ is generated (gitignored). Two sources:
#   og traces:  test/traces/NN.trace.replay → replay/trace_NN.replay
#   PRV goals:  test/prv/*.but → gen_traces.py → replay/*.replay
gen:
	@mkdir -p replay
	@for f in test/traces/*.trace.replay; do \
	  n=$$(basename "$$f" .trace.replay); \
	  cp "$$f" "replay/trace_$$n.replay"; \
	done
	@python3 test/gen_traces.py test/prv
	@for f in test/prv/gen/replay/*.replay; do \
	  cp "$$f" "replay/"; \
	done
	@echo "replay/ populated ($$(ls replay/*.replay 2>/dev/null | wc -l) files)"

# -- check: build + run all benchmark tests -----------------------------------
check: build
	@for n in $(TESTS); do \
	  [ -f "replay/$$n.replay" ] || { echo "replay/$$n.replay missing — run 'make gen' first"; exit 1; }; \
	done
	@t=$$(date +%s); pass=0; fail=0; xfail=0; \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	mkdir -p lp/gen; \
	for n in $(TESTS); do \
	  outfile="lp/gen/$$n.lp"; \
	  emit_warn=$$({ $(PP2LP) emit "replay/$$n.replay" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	  (cd lp && $(LP_CHECK) "gen/$$n.lp") 2>"$$lp_tmp"; \
	  if grep -q '"status":"ok"' "$$lp_tmp"; then pass=$$((pass+1)); \
	  else \
	    is_xfail=0; for xf in $(XFAIL); do [ "$$n" = "$$xf" ] && is_xfail=1 && break; done; \
	    if [ $$is_xfail -eq 1 ]; then xfail=$$((xfail+1)); \
	    else fail=$$((fail+1)); echo "FAIL $$n"; \
	      $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp" || echo "  (no details)"; \
	      echo "$$pass passed, $$fail failed ($$(( $$(date +%s) - t ))s)"; exit 1; \
	    fi; \
	  fi; \
	done; \
	msg="$$pass passed, $$fail failed"; \
	[ $$xfail -gt 0 ] && msg="$$msg, $$xfail xfail"; \
	echo "$$msg ($$(( $$(date +%s) - t ))s)"

# -- Individual target: make test-<name> --------------------------------------
test-%: build
	@[ -f "replay/$*.replay" ] || { echo "replay/$*.replay missing — run 'make gen' first"; exit 1; }
	@mkdir -p lp/gen; \
	n="$*"; \
	outfile="lp/gen/$$n.lp"; \
	emit_warn=$$({ $(PP2LP) emit "replay/$$n.replay" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	(cd lp && $(LP_CHECK) "gen/$$n.lp") 2>"$$lp_tmp"; \
	if grep -q '"status":"ok"' "$$lp_tmp"; then echo "OK $$n"; \
	else echo "FAIL $$n"; $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp"; exit 1; fi

# -- Build ---------------------------------------------------------------------
build:
	@cd ocaml && dune build

# -- Misc ----------------------------------------------------------------------
clean:
	cd ocaml && dune clean
	rm -rf lp/gen replay
	rm -f .pp2lp-cache
	find lp -name '*.lpo' -delete 2>/dev/null || true
