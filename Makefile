.PHONY: build check check-all check-fresh clean-lpo gen clean prove status coverage \
        check-claude check-prv check-og check-fuzz \
        gen-claude gen-prv gen-fuzz

export PP2LP_ROOT := $(CURDIR)

PP2LP        := ocaml/_build/default/bin/main.exe
# LP_CHECK: prefer --json when lambdapi supports it (structured errors for
# format_error.py), fall back to plain check otherwise. Detected once at
# Make parse-time.
LP_CHECK_JSON := $(shell lambdapi check --help 2>&1 | grep -q -- '--json' && echo 1)
ifeq ($(LP_CHECK_JSON),1)
LP_CHECK      = lambdapi check --json -c
else
LP_CHECK      = lambdapi check -c
endif
FORMAT_ERROR  = python3 bench/format_error.py

# -- Suite selection ----------------------------------------------------------
# Each suite lives in bench/<suite>/ with .but/.replay/.lp side-by-side.
#   claude — AI-generated goals from bench/claude/goals.txt
#   prv    — Atelier B "Proof Rules Validator" corpus (.but inputs)
#   og     — original pre-baked PP trace replays (no .but source)
#   fuzz   — randomly generated goals
SUITE       ?= prv
SUITE_DIR   := bench/$(SUITE)

# -- Expected failures (known issues, tolerated by check) ---------------------
XFAIL =

# -- Replay discovery ---------------------------------------------------------
REPLAYS := $(wildcard $(SUITE_DIR)/*.replay)
TESTS   := $(patsubst $(SUITE_DIR)/%.replay,%,$(REPLAYS))

# JOB= filter
ifdef JOB
  TESTS := $(filter $(JOB)%,$(TESTS))
endif

# -- Replay generation --------------------------------------------------------
# claude needs synth (goals.txt → .but) before PP/REPLAY.
# prv/fuzz start from pre-existing .but files.
# og has no .but source; regeneration is a no-op.
#
# Per-suite krt allocator overrides: PRV goals exhaust the default goal-stack
# (10000), so we bump g50000 for that suite. Other suites stay on defaults.
# Override per-invocation with: make gen SUITE=X ALLOC=...
ALLOC_claude =
ALLOC_prv    = g50000
ALLOC_og     =
ALLOC_fuzz   =
ALLOC       ?= $(ALLOC_$(SUITE))

gen: build
	@mkdir -p $(SUITE_DIR)
	@if [ "$(SUITE)" = "claude" ]; then \
	  $(PP2LP) synth $(SUITE_DIR)/goals.txt $(SUITE_DIR); \
	fi
	@if [ "$(SUITE)" = "og" ]; then \
	  echo "og suite has no .but sources; nothing to regenerate"; \
	else \
	  python3 bench/gen_traces.py -q --alloc "$(ALLOC)" -o $(SUITE_DIR) $(SUITE_DIR); \
	fi

gen-claude:; @$(MAKE) gen SUITE=claude
gen-prv:;    @$(MAKE) gen SUITE=prv
gen-fuzz:;   @$(MAKE) gen SUITE=fuzz

# -- Shared check logic -------------------------------------------------------
# Args: FAST_FAIL, DIR, PKG_NAME, TESTS
#
# Caching: per-test markers in <DIR>/.cache/<name>.{ok,fail,skip}. A test is
# "fresh" iff its .ok marker exists and is newer than both the .replay and
# the sentinel (newest mtime across the pp2lp binary and lp/ rule files).
# Fresh tests are counted as pass without re-emitting or re-checking.
define RUN_CHECK
	@if [ -z "$(4)" ]; then echo "No replay files in $(2) — run 'make gen SUITE=$(SUITE)' first"; exit 1; fi
	@printf 'package_name = $(3)\nroot_path = $(3)\n' > $(2)/lambdapi.pkg
	@mkdir -p $(2)/.cache
	@t=$$(date +%s); pass=0; cache_pass=0; fail=0; skip=0; \
	tot_trust=0; tot_admit=0; \
	_mt() { stat -c %Y "$$1" 2>/dev/null || stat -f %m "$$1" 2>/dev/null || echo 0; }; \
	bin_mt=$$(_mt $(PP2LP)); \
	lp_mt=0; for f in $$(find lp -type f -name '*.lp'); do \
	  m=$$(_mt "$$f"); [ "$$m" -gt "$$lp_mt" ] && lp_mt=$$m; \
	done; \
	sentinel=$$(( bin_mt > lp_mt ? bin_mt : lp_mt )); \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	for n in $(4); do \
	  replay="$(2)/$$n.replay"; \
	  outfile="$(2)/$$n.lp"; \
	  ok_mark="$(2)/.cache/$$n.ok"; \
	  fail_mark="$(2)/.cache/$$n.fail"; \
	  skip_mark="$(2)/.cache/$$n.skip"; \
	  is_xfail=0; for xf in $(XFAIL); do [ "$$n" = "$$xf" ] && is_xfail=1 && break; done; \
	  if [ -f "$$ok_mark" ] && [ "$$ok_mark" -nt "$$replay" ]; then \
	    ok_mt=$$(_mt "$$ok_mark"); \
	    if [ "$$ok_mt" -ge "$$sentinel" ]; then \
	      pass=$$((pass+1)); cache_pass=$$((cache_pass+1)); \
	      if [ -s "$$ok_mark" ]; then \
	        read nt na < "$$ok_mark"; \
	        tot_trust=$$((tot_trust + nt)); tot_admit=$$((tot_admit + na)); \
	      fi; \
	      continue; \
	    fi; \
	  fi; \
	  if [ -f "$$skip_mark" ] && [ "$$skip_mark" -nt "$$replay" ]; then \
	    skip_mt=$$(_mt "$$skip_mark"); \
	    if [ "$$skip_mt" -ge "$$sentinel" ]; then \
	      skip=$$((skip+1)); cache_pass=$$((cache_pass+1)); continue; \
	    fi; \
	  fi; \
	  if [ -f "$$fail_mark" ] && [ "$$fail_mark" -nt "$$replay" ]; then \
	    fail_mt=$$(_mt "$$fail_mark"); \
	    if [ "$$fail_mt" -ge "$$sentinel" ]; then \
	      fail=$$((fail+1)); cache_pass=$$((cache_pass+1)); \
	      echo "FAIL $$n (cached)"; \
	      if [ $(1) -eq 1 ]; then \
	        echo "$$pass passed, $$fail failed ($$(( $$(date +%s) - t ))s)"; exit 1; \
	      fi; \
	      continue; \
	    fi; \
	  fi; \
	  rm -f "$$ok_mark" "$$fail_mark" "$$skip_mark"; \
	  emit_tmp=$$(mktemp); \
	  $(PP2LP) emit "$$replay" > "$$outfile" 2>"$$emit_tmp"; emit_rc=$$?; \
	  emit_warn=$$(grep -v '^Entering\|^Leaving' "$$emit_tmp"); rm -f "$$emit_tmp"; \
	  if [ $$emit_rc -eq 2 ]; then \
	    skip=$$((skip+1)); echo "SKIP $$n: $$emit_warn"; \
	    echo "$$emit_warn" > "$$skip_mark"; continue; fi; \
	  if ! grep -q 'symbol' "$$outfile"; then \
	    if [ $$is_xfail -eq 1 ]; then skip=$$((skip+1)); \
	      echo "xfail (empty emission)" > "$$skip_mark"; \
	    else fail=$$((fail+1)); echo "FAIL $$n (empty emission)"; \
	      echo "empty emission" > "$$fail_mark"; \
	      if [ $(1) -eq 1 ]; then \
	        echo "$$pass passed, $$fail failed ($$(( $$(date +%s) - t ))s)"; exit 1; \
	      fi; \
	    fi; continue; fi; \
	  $(LP_CHECK) "$$outfile" >"$$lp_tmp" 2>&1; lp_rc=$$?; \
	  if [ $$lp_rc -eq 0 ]; then pass=$$((pass+1)); \
	    nt=$$(grep -ow 'trust' "$$outfile" | wc -l); \
	    na=$$(grep -ow 'admit' "$$outfile" | wc -l); \
	    tot_trust=$$((tot_trust + nt)); tot_admit=$$((tot_admit + na)); \
	    echo "$$nt $$na" > "$$ok_mark"; \
	    warns=""; \
	    [ $$nt -gt 0 ] && warns="$$nt trust"; \
	    [ $$na -gt 0 ] && warns="$${warns:+$$warns, }$$na admit"; \
	    [ -n "$$warns" ] && echo "  warn $$n: $$warns"; \
	  else \
	    if [ $$is_xfail -eq 1 ]; then skip=$$((skip+1)); \
	      echo "xfail (lambdapi error)" > "$$skip_mark"; \
	    else fail=$$((fail+1)); echo "FAIL $$n"; \
	      $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp" || echo "  (no details)"; \
	      cp "$$lp_tmp" "$$fail_mark"; \
	      if [ $(1) -eq 1 ]; then \
	        echo "$$pass passed, $$fail failed ($$(( $$(date +%s) - t ))s)"; exit 1; \
	      fi; \
	    fi; \
	  fi; \
	done; \
	msg="$$pass passed, $$fail failed"; \
	[ $$skip -gt 0 ] && msg="$$msg, $$skip skip"; \
	[ $$cache_pass -gt 0 ] && msg="$$msg ($$cache_pass cached)"; \
	warns=""; \
	[ $$tot_trust -gt 0 ] && warns="$$tot_trust trust"; \
	[ $$tot_admit -gt 0 ] && warns="$${warns:+$$warns, }$$tot_admit admit"; \
	[ -n "$$warns" ] && msg="$$msg [$$warns]"; \
	echo "$$msg ($$(( $$(date +%s) - t ))s)"; \
	[ $$fail -gt 0 ] && exit 1 || true
endef

# -- check: current suite, fast-fail on first unexpected failure --------------
check: build
	$(call RUN_CHECK,1,$(SUITE_DIR),pp2lp_$(SUITE),$(TESTS))

# -- check-all: current suite, report ALL failures ----------------------------
check-all: build
	$(call RUN_CHECK,0,$(SUITE_DIR),pp2lp_$(SUITE),$(TESTS))

# -- Per-suite convenience aliases --------------------------------------------
check-claude:; @$(MAKE) check-all SUITE=claude
check-prv:;    @$(MAKE) check-all SUITE=prv
check-og:;     @$(MAKE) check-all SUITE=og
check-fuzz:;   @$(MAKE) check-all SUITE=fuzz

# -- Individual test: make test-<name> (claude suite) -------------------------
# Bypasses the cache to force a re-check (useful for debugging).
test-%: build
	@replay="bench/claude/$*.replay"; \
	if [ ! -f "$$replay" ]; then \
	  but="bench/claude/$*.but"; \
	  if [ ! -f "$$but" ]; then \
	    $(PP2LP) synth bench/claude/goals.txt bench/claude >/dev/null; \
	  fi; \
	  [ -f "$$but" ] || { echo "No goal named '$*' in bench/claude/goals.txt"; exit 1; }; \
	  python3 bench/gen_traces.py -q -o bench/claude "$$but"; \
	  [ -f "$$replay" ] || { echo "PP/REPLAY failed for $*"; exit 1; }; \
	fi; \
	mkdir -p bench/claude/.cache; \
	rm -f bench/claude/.cache/$*.ok bench/claude/.cache/$*.fail bench/claude/.cache/$*.skip; \
	outfile="bench/claude/$*.lp"; \
	emit_tmp=$$(mktemp); \
	$(PP2LP) emit "$$replay" > "$$outfile" 2>"$$emit_tmp"; emit_rc=$$?; \
	emit_warn=$$(grep -v '^Entering\|^Leaving' "$$emit_tmp"); rm -f "$$emit_tmp"; \
	if [ $$emit_rc -eq 2 ]; then \
	  echo "SKIP $*: $$emit_warn"; \
	  echo "$$emit_warn" > bench/claude/.cache/$*.skip; exit 0; fi; \
	if ! grep -q 'symbol' "$$outfile"; then \
	  echo "FAIL $* (empty emission)"; echo "$$emit_warn" | head -5; \
	  echo "empty emission" > bench/claude/.cache/$*.fail; exit 1; fi; \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	$(LP_CHECK) "$$outfile" >"$$lp_tmp" 2>&1; lp_rc=$$?; \
	if [ $$lp_rc -eq 0 ]; then echo "OK $*"; \
	  nt=$$(grep -ow 'trust' "$$outfile" | wc -l); \
	  na=$$(grep -ow 'admit' "$$outfile" | wc -l); \
	  echo "$$nt $$na" > bench/claude/.cache/$*.ok; \
	else echo "FAIL $*"; $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp"; \
	  cp "$$lp_tmp" bench/claude/.cache/$*.fail; exit 1; fi

# -- Prove: send formula to PP, emit LP proof --------------------------------
prove: build
	@[ -n "$(FORMULA)" ] || { echo "Usage: make prove FORMULA='(p and q) => (q and p)'"; exit 1; }
	@$(PP2LP) prove $(if $(NAME),--name $(NAME)) '$(subst ','\'',$(FORMULA))'

# -- Coverage -----------------------------------------------------------------
coverage:
	@bash bench/rule_coverage.sh --by-suite

# -- Status: read cached markers (fast, no re-check) --------------------------
# Shows per-suite: replays / .cache hits (pass/fail/skip) / stale counts.
# "stale" = replay exists but no fresh cache entry — run `make check` to fill.
status:
	@echo "=== pp2lp status ==="
	@for suite in claude prv og fuzz; do \
	  dir="bench/$$suite"; \
	  [ -d "$$dir" ] || continue; \
	  replays=$$(ls $$dir/*.replay 2>/dev/null | wc -l); \
	  [ "$$replays" -eq 0 ] && continue; \
	  if [ -d "$$dir/.cache" ]; then \
	    pass=$$(ls $$dir/.cache/*.ok 2>/dev/null | wc -l); \
	    fail=$$(ls $$dir/.cache/*.fail 2>/dev/null | wc -l); \
	    skip=$$(ls $$dir/.cache/*.skip 2>/dev/null | wc -l); \
	  else pass=0; fail=0; skip=0; fi; \
	  known=$$((pass + fail + skip)); \
	  stale=$$((replays - known)); \
	  msg="Suite $$suite: $$replays replays | $$pass pass, $$fail fail, $$skip skip"; \
	  [ $$stale -gt 0 ] && msg="$$msg, $$stale stale"; \
	  if [ -f "$$dir/.gen_status.tsv" ]; then \
	    gen_fail=$$(awk -F'\t' '$$2 ~ /^fail-/' "$$dir/.gen_status.tsv" | wc -l); \
	    [ $$gen_fail -gt 0 ] && msg="$$msg | $$gen_fail gen-fail"; \
	  fi; \
	  echo "$$msg"; \
	  if [ -f "$$dir/.gen_status.tsv" ]; then \
	    awk -F'\t' '$$2 ~ /^fail-/{print $$2, $$3}' "$$dir/.gen_status.tsv" \
	      | sort | uniq -c | awk '{c=$$1; $$1=""; printf "    %3d  %s\n", c, substr($$0,2)}'; \
	  fi; \
	done

# -- Build --------------------------------------------------------------------
build:
	@cd ocaml && dune build

# -- clean-lpo: drop stale Lambdapi object files ------------------------------
# When an LP rule signature changes, .lpo files produced by an older lambdapi
# run become incompatible. Invoke this before a check to force re-elaboration.
clean-lpo:
	@find lp -name '*.lpo' -delete 2>/dev/null; true

# -- check-fresh: force a full suite re-check (bench cache + .lpo invalidation)
# Use after edits to lp/ that rename or change symbol signatures.
check-fresh: clean-lpo
	@rm -rf $(SUITE_DIR)/.cache
	@$(MAKE) --no-print-directory check-all SUITE=$(SUITE)

# -- Clean --------------------------------------------------------------------
# Remove generated artifacts and caches from all suites, but preserve
# canonical inputs (goals.txt, .but files in prv, .replay files in og).
clean:
	cd ocaml && dune clean
	rm -rf bench/claude/.cache bench/prv/.cache bench/og/.cache bench/fuzz/.cache
	rm -f  bench/claude/.gen_status.tsv bench/prv/.gen_status.tsv bench/fuzz/.gen_status.tsv
	rm -f bench/claude/*.but bench/claude/*.trace bench/claude/*.replay \
	      bench/claude/*.lp bench/claude/*.lpo bench/claude/lambdapi.pkg
	rm -f bench/prv/*.trace bench/prv/*.replay \
	      bench/prv/*.lp bench/prv/*.lpo bench/prv/lambdapi.pkg
	rm -f bench/og/*.lp bench/og/*.lpo bench/og/lambdapi.pkg
	rm -f bench/fuzz/*.trace bench/fuzz/*.replay \
	      bench/fuzz/*.lp bench/fuzz/*.lpo bench/fuzz/lambdapi.pkg
	find lp -name '*.lpo' -delete 2>/dev/null || true
