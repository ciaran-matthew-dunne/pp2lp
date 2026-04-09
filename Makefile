.PHONY: build check gen gen-og gen-prv gen-synth unit-test clean prove status coverage

export PP2LP_ROOT := $(CURDIR)

PP2LP        := ocaml/_build/default/bin/main.exe
LP_CHECK      = lambdapi check --json
FORMAT_ERROR  = python3 bench/format_error.py

# -- Expected failures (known issues, tolerated by check) ---------------------
XFAIL = xst_flatten

# -- Replay discovery ---------------------------------------------------------
# Replays live in their source directories (no merged replay/ dir).
OG_REPLAYS   := $(wildcard bench/traces/*.trace.replay)
PRV_REPLAYS  := $(wildcard bench/prv/gen/replay/*.replay)
SYNTH_REPLAYS:= $(wildcard bench/synth/but/gen/replay/*.replay)

OG_TESTS     := $(patsubst bench/traces/%.trace.replay,trace_%,$(OG_REPLAYS))
PRV_TESTS    := $(patsubst bench/prv/gen/replay/%.replay,%,$(PRV_REPLAYS))
SYNTH_TESTS  := $(patsubst bench/synth/but/gen/replay/%.replay,%,$(SYNTH_REPLAYS))
ALL_TESTS    := $(OG_TESTS) $(PRV_TESTS) $(SYNTH_TESTS)

# JOB= filter
ifdef JOB
  ifeq ($(JOB),og)
    TESTS := $(OG_TESTS)
  else ifeq ($(JOB),prv)
    TESTS := $(PRV_TESTS)
  else ifeq ($(JOB),synth)
    TESTS := $(SYNTH_TESTS)
  else ifneq ($(filter prv-%,$(JOB)),)
    _CAT := $(patsubst prv-%,%,$(JOB))
    TESTS := $(filter $(_CAT)_%,$(PRV_TESTS))
  else
    TESTS := $(filter $(JOB)_%,$(ALL_TESTS))
  endif
else
  TESTS := $(ALL_TESTS)
endif

# -- Shell helper: resolve test name → replay path ----------------------------
# Used inside shell loops. Tries og, prv, synth in order.
define FIND_REPLAY
find_replay() { \
  local n="$$1"; \
  case "$$n" in trace_*) \
    echo "bench/traces/$${n#trace_}.trace.replay"; return ;; \
  esac; \
  local f="bench/prv/gen/replay/$$n.replay"; \
  [ -f "$$f" ] && { echo "$$f"; return; }; \
  echo "bench/synth/but/gen/replay/$$n.replay"; \
}
endef

# -- Replay generation --------------------------------------------------------
gen: gen-og gen-prv gen-synth

gen-og:
	@true  # og replays are checked in

gen-synth: build
	@mkdir -p bench/synth/but
	@$(PP2LP) synth bench/synth/goals.txt bench/synth/but
	@python3 bench/gen_traces.py -q bench/synth/but
	@echo "synth: $$(ls bench/synth/but/gen/replay/*.replay 2>/dev/null | wc -l) replays"

gen-prv:
	@python3 bench/gen_traces.py -q bench/prv
	@echo "prv: $$(ls bench/prv/gen/replay/*.replay 2>/dev/null | wc -l) replays"

# -- check: build + run benchmark tests ---------------------------------------
check: build
	@if [ -z "$(TESTS)" ]; then echo "No replay files found — run 'make gen' first"; exit 1; fi
	@rm -rf bench/lp/*.lp bench/lp/*.lpo
	@$(FIND_REPLAY); \
	t=$$(date +%s); pass=0; fail=0; xfail=0; \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	for n in $(TESTS); do \
	  replay=$$(find_replay "$$n"); \
	  outfile="bench/lp/$$n.lp"; \
	  emit_warn=$$({ $(PP2LP) emit "$$replay" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	  $(LP_CHECK) "$$outfile" 2>"$$lp_tmp"; \
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

# -- Individual test: make test-<name> ----------------------------------------
test-%: build
	@$(FIND_REPLAY); \
	replay=$$(find_replay "$*"); \
	[ -f "$$replay" ] || { echo "$$replay missing — run 'make gen' first"; exit 1; }; \
	outfile="bench/lp/$*.lp"; \
	emit_warn=$$({ $(PP2LP) emit "$$replay" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	lp_tmp=$$(mktemp); trap "rm -f $$lp_tmp" EXIT; \
	$(LP_CHECK) "$$outfile" 2>"$$lp_tmp"; \
	if grep -q '"status":"ok"' "$$lp_tmp"; then echo "OK $*"; \
	else echo "FAIL $*"; $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp"; exit 1; fi

# -- Shortcuts ----------------------------------------------------------------
trace-%: test-trace_%
	@true
prv-%: test-%
	@true

# -- errors-prv: all PRV failures with error messages (no fast-fail) ----------
errors-prv: build
	@for f in bench/prv/gen/replay/*.replay; do \
	  n=$$(basename "$$f" .replay); \
	  outfile="bench/lp/$$n.lp"; \
	  emit_warn=$$({ $(PP2LP) emit "$$f" > "$$outfile"; } 2>&1 | grep -v '^Entering\|^Leaving'); \
	  lp_tmp=$$(mktemp); \
	  $(LP_CHECK) "$$outfile" 2>"$$lp_tmp"; \
	  if ! grep -q '"status":"ok"' "$$lp_tmp"; then \
	    echo "FAIL $$n"; \
	    $(FORMAT_ERROR) "$$emit_warn" < "$$lp_tmp" || echo "  (no details)"; \
	  fi; \
	  rm -f "$$lp_tmp"; \
	done

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

# -- Status -------------------------------------------------------------------
status:
	@echo "=== pp2lp status ==="
	@echo "OG traces: $$(ls bench/traces/*.trace.replay 2>/dev/null | wc -l)"
	@echo "PRV goals: $$(ls bench/prv/*.but 2>/dev/null | wc -l) total, $$(ls bench/prv/gen/replay/*.replay 2>/dev/null | wc -l) with replays"
	@echo "Synth goals: $$(grep -c '^[a-z]' bench/synth/goals.txt 2>/dev/null || echo 0), $$(ls bench/synth/but/gen/replay/*.replay 2>/dev/null | wc -l) with replays"
	@echo "XFAIL: $(XFAIL)"

# -- Build --------------------------------------------------------------------
build:
	@cd ocaml && dune build

# -- Clean --------------------------------------------------------------------
clean:
	cd ocaml && dune clean
	rm -rf bench/lp/*.lp bench/lp/*.lpo
	rm -rf bench/prv/gen bench/synth/but
	rm -f .pp2lp-cache
	find lp -name '*.lpo' -delete 2>/dev/null || true
