.PHONY: build check check-all gen unit-test clean prove status coverage

export PP2LP_ROOT := $(CURDIR)

PP2LP        := ocaml/_build/default/bin/main.exe
LP_CHECK      = lambdapi check --json -c
FORMAT_ERROR  = python3 bench/format_error.py

# -- Expected failures (known issues, tolerated by check) ---------------------
XFAIL =

# -- Replay discovery ---------------------------------------------------------
REPLAYS      := $(wildcard bench/gen/*.replay)
TESTS        := $(patsubst bench/gen/%.replay,%,$(REPLAYS))

# JOB= filter
ifdef JOB
  TESTS := $(filter $(JOB)%,$(TESTS))
endif

# -- Replay generation --------------------------------------------------------
gen: build
	@mkdir -p bench/gen
	@$(PP2LP) synth bench/goals.txt bench/gen
	@python3 bench/gen_traces.py -q -o bench/gen bench/gen

# -- Shared check logic (used by check and check-all) ------------------------
# Args: FAST_FAIL (0 or 1)
define RUN_CHECK
	@if [ -z "$(TESTS)" ]; then echo "No replay files found — run 'make gen' first"; exit 1; fi
	@printf 'package_name = pp2lp_bench\nroot_path = pp2lp_bench\n' > bench/gen/lambdapi.pkg
	@rm -f bench/gen/*.lp
	@t=$$(date +%s); pass=0; fail=0; skip=0; \
	tot_trust=0; tot_admit=0; \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	for n in $(TESTS); do \
	  replay="bench/gen/$$n.replay"; \
	  outfile="bench/gen/$$n.lp"; \
	  emit_tmp=$$(mktemp); \
	  $(PP2LP) emit "$$replay" > "$$outfile" 2>"$$emit_tmp"; emit_rc=$$?; \
	  emit_warn=$$(grep -v '^Entering\|^Leaving' "$$emit_tmp"); rm -f "$$emit_tmp"; \
	  if [ $$emit_rc -eq 2 ]; then \
	    skip=$$((skip+1)); echo "SKIP $$n: $$emit_warn"; continue; fi; \
	  is_xfail=0; for xf in $(XFAIL); do [ "$$n" = "$$xf" ] && is_xfail=1 && break; done; \
	  if ! grep -q 'symbol' "$$outfile"; then \
	    if [ $$is_xfail -eq 1 ]; then skip=$$((skip+1)); \
	    else fail=$$((fail+1)); echo "FAIL $$n (empty emission)"; \
	      if [ $(1) -eq 1 ]; then \
	        echo "$$pass passed, $$fail failed ($$(( $$(date +%s) - t ))s)"; exit 1; \
	      fi; \
	    fi; continue; fi; \
	  $(LP_CHECK) "$$outfile" 2>"$$lp_tmp"; \
	  if grep -q '"status":"ok"' "$$lp_tmp"; then pass=$$((pass+1)); \
	    nt=$$(grep -ow 'trust' "$$outfile" | wc -l); \
	    na=$$(grep -ow 'admit' "$$outfile" | wc -l); \
	    tot_trust=$$((tot_trust + nt)); tot_admit=$$((tot_admit + na)); \
	    warns=""; \
	    [ $$nt -gt 0 ] && warns="$$nt trust"; \
	    [ $$na -gt 0 ] && warns="$${warns:+$$warns, }$$na admit"; \
	    [ -n "$$warns" ] && echo "  warn $$n: $$warns"; \
	  else \
	    if [ $$is_xfail -eq 1 ]; then skip=$$((skip+1)); \
	    else fail=$$((fail+1)); echo "FAIL $$n"; \
	      $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp" || echo "  (no details)"; \
	      if [ $(1) -eq 1 ]; then \
	        echo "$$pass passed, $$fail failed ($$(( $$(date +%s) - t ))s)"; exit 1; \
	      fi; \
	    fi; \
	  fi; \
	done; \
	msg="$$pass passed, $$fail failed"; \
	[ $$skip -gt 0 ] && msg="$$msg, $$skip skip"; \
	warns=""; \
	[ $$tot_trust -gt 0 ] && warns="$$tot_trust trust"; \
	[ $$tot_admit -gt 0 ] && warns="$${warns:+$$warns, }$$tot_admit admit"; \
	[ -n "$$warns" ] && msg="$$msg ($$warns)"; \
	echo "$$msg ($$(( $$(date +%s) - t ))s)"; \
	[ $$fail -gt 0 ] && exit 1 || true
endef

# -- check: build + benchmarks, fast-fail on first unexpected failure ---------
check: build
	$(call RUN_CHECK,1)

# -- check-all: build + benchmarks, report ALL failures ----------------------
check-all: build
	$(call RUN_CHECK,0)

# -- Individual test: make test-<name> ----------------------------------------
test-%: build
	@replay="bench/gen/$*.replay"; \
	[ -f "$$replay" ] || { echo "$$replay missing — run 'make gen' first"; exit 1; }; \
	outfile="bench/gen/$*.lp"; \
	emit_tmp=$$(mktemp); \
	$(PP2LP) emit "$$replay" > "$$outfile" 2>"$$emit_tmp"; emit_rc=$$?; \
	emit_warn=$$(grep -v '^Entering\|^Leaving' "$$emit_tmp"); rm -f "$$emit_tmp"; \
	if [ $$emit_rc -eq 2 ]; then \
	  echo "SKIP $*: $$emit_warn"; exit 0; fi; \
	if ! grep -q 'symbol' "$$outfile"; then \
	  echo "FAIL $* (empty emission)"; echo "$$emit_warn" | head -5; exit 1; fi; \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	$(LP_CHECK) "$$outfile" 2>"$$lp_tmp"; \
	if grep -q '"status":"ok"' "$$lp_tmp"; then echo "OK $*"; \
	else echo "FAIL $*"; $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp"; exit 1; fi

# -- Unit tests ---------------------------------------------------------------
unit-test: build
	@cd ocaml && dune test

# -- Prove: send formula to PP, emit LP proof --------------------------------
prove: build
	@[ -n "$(FORMULA)" ] || { echo "Usage: make prove FORMULA='(p and q) => (q and p)'"; exit 1; }
	@$(PP2LP) prove $(if $(NAME),--name $(NAME)) '$(FORMULA)'

# -- Coverage -----------------------------------------------------------------
coverage:
	@bash bench/rule_coverage.sh --by-suite

# -- Status: full overview of project health ----------------------------------
status: build
	@echo "=== pp2lp status ==="
	@goals=$$(grep -c '^[a-z]' bench/goals.txt 2>/dev/null || echo 0); \
	replays=$$(ls bench/gen/*.replay 2>/dev/null | wc -l); \
	echo "Goals: $$goals, $$replays with replays"; \
	echo "XFAIL: $(XFAIL)"; \
	echo "Unit tests:"; cd ocaml && dune exec test/test_pp2lp.exe 2>&1 | tail -1; cd ..; \
	echo "Benchmarks:"; \
	pass=0; fail=0; skip=0; \
	printf 'package_name = pp2lp_bench\nroot_path = pp2lp_bench\n' > bench/gen/lambdapi.pkg; \
	rm -f bench/gen/*.lp; \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	for n in $(TESTS); do \
	  replay="bench/gen/$$n.replay"; \
	  outfile="bench/gen/$$n.lp"; \
	  $(PP2LP) emit "$$replay" > "$$outfile" 2>/dev/null; \
	  emit_rc=$$?; \
	  if [ $$emit_rc -eq 2 ]; then skip=$$((skip+1)); continue; fi; \
	  is_xfail=0; for xf in $(XFAIL); do [ "$$n" = "$$xf" ] && is_xfail=1 && break; done; \
	  if ! grep -q 'symbol' "$$outfile"; then \
	    [ $$is_xfail -eq 1 ] && skip=$$((skip+1)) || fail=$$((fail+1)); \
	    continue; fi; \
	  $(LP_CHECK) "$$outfile" 2>"$$lp_tmp"; \
	  if grep -q '"status":"ok"' "$$lp_tmp"; then pass=$$((pass+1)); \
	  else [ $$is_xfail -eq 1 ] && skip=$$((skip+1)) || fail=$$((fail+1)); fi; \
	done; \
	msg="  $$pass passed, $$fail failed"; \
	[ $$skip -gt 0 ] && msg="$$msg, $$skip skip"; \
	echo "$$msg"

# -- Build --------------------------------------------------------------------
build:
	@cd ocaml && dune build

# -- Clean --------------------------------------------------------------------
clean:
	cd ocaml && dune clean
	rm -rf bench/gen
	rm -f .pp2lp-cache
	find lp -name '*.lpo' -delete 2>/dev/null || true
