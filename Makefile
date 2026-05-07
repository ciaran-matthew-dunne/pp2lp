.PHONY: help build gen-traces gen-replays check clean repl

# Symlink-friendly: re-resolve PP2LP_ROOT every Make invocation.
export PP2LP_ROOT := $(CURDIR)

PP2LP := ocaml/_build/default/bin/main.exe
LP_JSON := bench/format_lambdapi_json.py

SUITE ?= og
NAME  ?=
LP_DIR ?= lp/bench/$(SUITE)
CHECK_TRACE = $(if $(TRACE),$(TRACE),$(if $(NAME),bench/$(SUITE)/$(NAME).trace,))
CHECK_NAME = $(if $(NAME),$(NAME),$(basename $(notdir $(CHECK_TRACE))))
CHECK_SUITE = $(if $(NAME),$(SUITE),$(if $(filter bench/%,$(CHECK_TRACE)),$(word 2,$(subst /, ,$(CHECK_TRACE))),$(SUITE)))
CHECK_OUT = $(if $(OUT),$(OUT),lp/bench/$(CHECK_SUITE)/$(CHECK_NAME).lp)
DIR   ?=
OUT_DIR ?=

help:
	@echo "Targets:"
	@echo "  build                    build the OCaml binary"
	@echo "  gen-traces DIR=path      run PP and generate .trace files from .but files"
	@echo "  gen-replays DIR=path     optional: generate debug .replay files from .trace files"
	@echo "  check [SUITE=og]         lambdapi-check bench/<suite>/*.trace"
	@echo "  check TRACE=path.trace   lambdapi-check one trace"
	@echo "  clean                    remove lp/bench, .lpo files, and dune build"
	@echo "  repl                     OCaml REPL with project loaded"
	@echo ""
	@echo "Shortcut: use NAME=01 [SUITE=og] instead of TRACE=bench/og/01.trace."

build:
	@cd ocaml && dune build

repl:
	@cd ocaml && dune utop src

gen-traces:
	@[ -n "$(DIR)" ] || { echo "Usage: make gen-traces DIR=<but-dir-or-file> [OUT_DIR=<trace-dir>]"; exit 1; }
	@python3 bench/gen_traces.py $(if $(OUT_DIR),-o "$(OUT_DIR)") "$(DIR)"

gen-replays:
	@[ -n "$(DIR)" ] || { echo "Usage: make gen-replays DIR=<trace-dir-or-file> [OUT_DIR=<replay-dir>]"; exit 1; }
	@python3 bench/gen_replays.py $(if $(OUT_DIR),-o "$(OUT_DIR)") "$(DIR)"

check: build
	@set -eu; \
	if [ -n "$(CHECK_TRACE)" ]; then \
	  [ -f "$(CHECK_TRACE)" ] || { echo "No trace: $(CHECK_TRACE)"; exit 1; }; \
	  mkdir -p "$(dir $(CHECK_OUT))"; \
	  tmp="$(CHECK_OUT).tmp"; \
	  rm -f "$$tmp"; \
	  if ! $(PP2LP) "$(CHECK_TRACE)" > "$$tmp"; then \
	    rm -f "$$tmp"; \
	    exit 1; \
	  fi; \
	  mv "$$tmp" "$(CHECK_OUT)"; \
	  json="/tmp/pp2lp-$$(basename "$(CHECK_OUT)" .lp).json"; \
	  if lambdapi check --json -c "$(CHECK_OUT)" > "$$json" 2>&1; then \
	    python3 $(LP_JSON) --ok "$$json"; \
	    rm -f "$$json"; \
	  else \
	    python3 $(LP_JSON) "$$json"; \
	    rm -f "$$json"; \
	    exit 1; \
	  fi; \
	else \
	  ok=0; fail=0; \
	  for tr in bench/$(SUITE)/*.trace; do \
	    [ -f "$$tr" ] || { echo "No traces in bench/$(SUITE)"; exit 1; }; \
	    name=$$(basename "$$tr" .trace); \
	    mkdir -p "$(LP_DIR)"; \
	    out="$(LP_DIR)/$$name.lp"; \
	    tmp="$$out.tmp"; \
	    json="/tmp/pp2lp-$$name.json"; \
	    rm -f "$$tmp"; \
	    if $(PP2LP) "$$tr" > "$$tmp" 2>"/tmp/pp2lp-$$name.emit.err" \
	       && mv "$$tmp" "$$out" \
	       && lambdapi check --json -c "$$out" >"$$json" 2>&1; then \
	      ok=$$((ok + 1)); \
	    else \
	      fail=$$((fail + 1)); \
	      echo "FAIL $$tr"; \
	      if [ -s "/tmp/pp2lp-$$name.emit.err" ]; then \
	        sed -n '1,8p' "/tmp/pp2lp-$$name.emit.err"; \
	      else \
	        python3 $(LP_JSON) "$$json"; \
	      fi; \
	    fi; \
	    rm -f "/tmp/pp2lp-$$name.emit.err" "$$json" "$$tmp"; \
	  done; \
	  echo "trace checks: $$ok ok, $$fail failed"; \
	  test "$$fail" -eq 0; \
	fi

clean:
	@rm -rf lp/bench
	@find lp -name '*.lpo' -delete
	@cd ocaml && dune clean
