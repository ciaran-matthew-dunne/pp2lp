.PHONY: build check clean

PP2LP        := dune exec --root ocaml -- pp2lp
LP_CHECK      = lambdapi check --json
FORMAT_ERROR  = PP2LP_ROOT=$(CURDIR) python3 test/format_error.py

# -- Expected failures (known issues, tolerated by check) ---------------------
XFAIL =

# -- Benchmark suite ----------------------------------------------------------
# Each test: name replay_file gen_dir
# og traces
TESTS  = trace_01 trace_02 trace_14 trace_18 trace_19 trace_26
# PRV tests
TESTS += arith_ineq_001 arith_ineq_003 negation_001 general_001
TESTS += equality_001 equality_002 equality_005
TESTS += range_eq_001 range_subset_001
TESTS += set_product_001 set_product_004
TESTS += set_subset_001 set_type_001

# Map test name → replay file
replay_of = $(if $(filter trace_%,$(1)),test/traces/$(patsubst trace_%,%,$(1)).trace.replay,test/prv/gen/replay/$(1).replay)
gendir_of = $(if $(filter trace_%,$(1)),lp/gen,lp/gen/prv)

# -- check: build + run all benchmark tests -----------------------------------
check: build
	@t=$$(date +%s); pass=0; fail=0; xfail=0; \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	for n in $(TESTS); do \
	  case $$n in trace_*) replay="test/traces/$${n#trace_}.trace.replay"; gdir="lp/gen";; \
	              *)        replay="test/prv/gen/replay/$$n.replay";       gdir="lp/gen/prv";; esac; \
	  mkdir -p "$$gdir"; \
	  outfile="$$gdir/$$n.lp"; \
	  emit_warn=$$({ $(PP2LP) emit "$$replay" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	  (cd lp && $(LP_CHECK) "$${outfile#lp/}") 2>"$$lp_tmp"; \
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
	@n="$*"; \
	case $$n in trace_*) replay="test/traces/$${n#trace_}.trace.replay"; gdir="lp/gen";; \
	            *)        replay="test/prv/gen/replay/$$n.replay";       gdir="lp/gen/prv";; esac; \
	mkdir -p "$$gdir"; \
	outfile="$$gdir/$$n.lp"; \
	emit_warn=$$({ $(PP2LP) emit "$$replay" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	(cd lp && $(LP_CHECK) "$${outfile#lp/}") 2>"$$lp_tmp"; \
	if grep -q '"status":"ok"' "$$lp_tmp"; then echo "OK $$n"; \
	else echo "FAIL $$n"; $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp"; exit 1; fi

# -- Build ---------------------------------------------------------------------
build:
	@cd ocaml && dune build

# -- Misc ----------------------------------------------------------------------
clean:
	cd ocaml && dune clean
	rm -rf lp/gen
	rm -f .pp2lp-cache
	find lp -name '*.lpo' -delete 2>/dev/null || true
