.PHONY: build unit-test check check-% gen gen-prv errors-prv trace-% prv-% clean

PP2LP        := dune exec --root ocaml -- pp2lp
LP_CHECK      = lambdapi check --json
FORMAT_ERROR  = PP2LP_ROOT=$(CURDIR) python3 test/format_error.py

# -- Expected failures (known issues, tolerated by check) ---------------------
XFAIL =

# -- Job configuration --------------------------------------------------------
# Add new replay jobs by defining REPLAYS_<name>, GENDIR_<name>, EXT_<name>
REPLAYS_og  = test/traces/*.trace.replay
GENDIR_og   = lp/gen
EXT_og      = .trace.replay

# PRV categories (auto-derived from test/prv/gen/replay/ filenames)
PRV_CATS = arith_ineq bool_eq cardinality equality general negation \
           range_eq range_subset set_product set_subset set_type

$(foreach c,$(PRV_CATS),\
  $(eval REPLAYS_prv-$(c) = test/prv/gen/replay/$(c)_*.replay)\
  $(eval GENDIR_prv-$(c)  = lp/gen/prv)\
  $(eval EXT_prv-$(c)     = .replay))

# prv = all PRV categories combined
REPLAYS_prv = test/prv/gen/replay/*.replay
GENDIR_prv  = lp/gen/prv
EXT_prv     = .replay

PRV_JOBS = $(addprefix prv-,$(PRV_CATS))
JOBS = og $(PRV_JOBS)

# -- Full pipeline -------------------------------------------------------------
# make check                    - build + all jobs (og + all prv categories)
# make check JOB=prv            - all PRV categories
# make check JOB=prv-equality   - one PRV category
# make check JOB=og             - 30 original traces only
JOB ?= all

ifeq ($(JOB),all)
  CHECK_JOBS = $(JOBS)
else ifeq ($(JOB),prv)
  CHECK_JOBS = $(PRV_JOBS)
else
  CHECK_JOBS = $(JOB)
endif

check: build
	@T0=$$(date +%s); \
	for j in $(CHECK_JOBS); do \
	  $(MAKE) -s --no-print-directory check-$$j || exit 1; \
	  echo ""; \
	done; \
	echo "total: $$(( $$(date +%s) - T0 ))s"

# -- Generic job checker (pattern rule) ----------------------------------------
check-%: build
	@echo "=== $* ==="; \
	t=$$(date +%s); \
	ext="$(EXT_$*)"; \
	mkdir -p "$(GENDIR_$*)"; \
	pass=0; fail=0; xfail=0; \
	lp_tmp=$$(mktemp); \
	trap "rm -f $$lp_tmp" EXIT; \
	for r in $(REPLAYS_$*); do \
	  n=$$(basename "$$r" "$$ext"); \
	  outfile="$(GENDIR_$*)/$$n.lp"; \
	  emit_warn=$$({ $(PP2LP) emit "$$r" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	  (cd lp && $(LP_CHECK) "$${outfile#lp/}") 2>"$$lp_tmp"; \
	  if grep -q '"status":"ok"' "$$lp_tmp"; then \
	    pass=$$((pass+1)); \
	  else \
	    is_xfail=0; \
	    for xf in $(XFAIL); do [ "$$n" = "$$xf" ] && is_xfail=1 && break; done; \
	    if [ $$is_xfail -eq 1 ]; then \
	      xfail=$$((xfail+1)); \
	    else \
	      fail=$$((fail+1)); \
	      echo "FAIL $$n"; \
	      $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp" || echo "  (no details)"; \
	      echo "$$pass passed, $$fail failed ($$(( $$(date +%s) - t ))s)"; \
	      exit 1; \
	    fi; \
	  fi; \
	done; \
	msg="$$pass passed, $$fail failed"; \
	[ $$xfail -gt 0 ] && msg="$$msg, $$xfail xfail"; \
	echo "$$msg ($$(( $$(date +%s) - t ))s)"

# -- Build ---------------------------------------------------------------------
build:
	@cd ocaml && dune build

unit-test: build
	dune exec --root ocaml -- ../ocaml/_build/default/test/test_pp2lp.exe

# -- Generation ----------------------------------------------------------------
gen: gen-prv

gen-prv:
	python3 test/gen_traces.py test/prv

# -- Individual tests ----------------------------------------------------------
trace-%: build
	@mkdir -p lp/gen
	@emit_warn=$$({ $(PP2LP) emit test/traces/$*.trace.replay > lp/gen/trace_$*.lp; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	lp_tmp=$$(mktemp); \
	trap "rm -f $$lp_tmp" EXIT; \
	(cd lp && $(LP_CHECK) gen/trace_$*.lp) 2>"$$lp_tmp"; \
	if grep -q '"status":"ok"' "$$lp_tmp"; then \
	  echo "OK trace_$*"; \
	else \
	  echo "FAIL trace_$*"; \
	  $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp"; \
	  exit 1; \
	fi

prv-%: build
	@mkdir -p lp/gen/prv
	@emit_warn=$$({ $(PP2LP) emit test/prv/gen/replay/$*.replay > lp/gen/prv/$*.lp; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	lp_tmp=$$(mktemp); \
	trap "rm -f $$lp_tmp" EXIT; \
	(cd lp && $(LP_CHECK) gen/prv/$*.lp) 2>"$$lp_tmp"; \
	if grep -q '"status":"ok"' "$$lp_tmp"; then \
	  echo "OK $*"; \
	else \
	  echo "FAIL $*"; \
	  $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp"; \
	  exit 1; \
	fi

# -- Diagnostics ---------------------------------------------------------------
# Show ALL failing PRV tests (doesn't stop on first failure)
errors-prv: build
	@mkdir -p lp/gen/prv; \
	pass=0; fail=0; \
	lp_tmp=$$(mktemp); \
	trap "rm -f $$lp_tmp" EXIT; \
	for r in $(if $(FILTER),$(wildcard test/prv/gen/replay/$(FILTER)*.replay),test/prv/gen/replay/*.replay); do \
	  n=$$(basename $$r .replay); \
	  emit_warn=$$({ $(PP2LP) emit $$r > lp/gen/prv/$$n.lp; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	  (cd lp && $(LP_CHECK) gen/prv/$$n.lp) 2>"$$lp_tmp"; \
	  if grep -q '"status":"ok"' "$$lp_tmp"; then \
	    pass=$$((pass+1)); \
	  else \
	    fail=$$((fail+1)); \
	    echo "FAIL $$n"; \
	    $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp" || echo "  (no details)"; \
	    echo ""; \
	  fi; \
	done; \
	echo "$$pass passed, $$fail failed"

# -- Misc ----------------------------------------------------------------------
clean:
	cd ocaml && dune clean
	rm -rf lp/gen
	rm -f .pp2lp-cache
