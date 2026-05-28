.PHONY: help build check rules tree gen-traces gen-replays clean clean-bench repl

export PP2LP_ROOT := $(CURDIR)

# ── Positional argument parsing ──────────────────────────────
# `make check og/01` → _ARG=og/01 → _SUITE=og _NAME=01
# `make check prv`   → _ARG=prv   → _SUITE=prv _NAME=
# `make tree og/27`  → _ARG=og/27 → _SUITE=og _NAME=27
FIRST_GOAL := $(firstword $(MAKECMDGOALS))
ifneq ($(filter check tree rules gen-traces gen-replays,$(FIRST_GOAL)),)
  _ARG := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  ifneq ($(_ARG),)
    $(eval $(_ARG):;@:)
  endif
endif

ifneq ($(_ARG),)
  ifneq ($(findstring /,$(_ARG)),)
    _SUITE := $(firstword $(subst /, ,$(_ARG)))
    _NAME  := $(word 2,$(subst /, ,$(_ARG)))
  else
    _SUITE := $(_ARG)
  endif
else
  _SUITE := $(if $(SUITE),$(SUITE),og)
  _NAME  := $(NAME)
endif

ARGS :=
ifdef V
  ARGS += --verbose
endif
ifdef Q
  ARGS += --quiet
endif

# ── Derived paths ────────────────────────────────────────────
PP2LP := ./ocaml/_build/default/bin/main.exe

_REPLAY_BASE  = lp/bench/$(_SUITE)/$(_NAME).replay
_REPLAY_XFAIL = lp/bench/$(_SUITE)/xfail/$(_NAME).replay
_REPLAY       = $(if $(REPLAY),$(REPLAY),$(if $(wildcard $(_REPLAY_BASE)),$(_REPLAY_BASE),$(_REPLAY_XFAIL)))

_CHECK_ARGS = $(if $(REPLAY),--replay $(REPLAY),\
              $(if $(_NAME),--name $(_NAME) --suite $(_SUITE),\
              --suite $(_SUITE)))

# ── Targets ──────────────────────────────────────────────────
help:
	@echo "Usage:"
	@echo "  make check [SUITE[/NAME]]   emit + lambdapi check"
	@echo "  make tree  SUITE/NAME       dump rebuilt proof tree"
	@echo "  make rules SUITE/NAME       dump parsed (rule, arg, kind) lines"
	@echo ""
	@echo "Examples:"
	@echo "  make check                  check og suite (default)"
	@echo "  make check og               check og suite"
	@echo "  make check prv              check prv suite"
	@echo "  make check og/01            check one replay"
	@echo "  make tree  og/27            dump proof tree"
	@echo "  make rules og/22            dump parsed rules"
	@echo "  make check og V=1           verbose output"
	@echo "  make check og Q=1           summary only"
	@echo ""
	@echo "Other:"
	@echo "  build                       build the OCaml binary"
	@echo "  gen-traces [SUITE]          .but → .trace (runs PP)"
	@echo "  gen-replays [SUITE]         .trace → .replay"
	@echo "  clean-bench                 remove emitted .lp/.lpo files"
	@echo "  clean                       clean-bench + dune clean"
	@echo "  repl                        dune utop with project loaded"
	@echo ""
	@echo "Suites: og (default), prv, prv-no-arith, synth"

build:
	@cd ocaml && dune build

repl:
	@cd ocaml && dune utop src

check: build
	@python3 bench/check.py $(_CHECK_ARGS) $(ARGS)

tree: build
	@$(if $(_NAME),,$(error usage: make tree SUITE/NAME))
	@$(PP2LP) tree $(_REPLAY)

rules: build
	@$(if $(_NAME),,$(error usage: make rules SUITE/NAME))
	@$(PP2LP) rules $(_REPLAY)

gen-traces:
	@python3 bench/gen_traces.py --suite $(_SUITE)

gen-replays:
	@python3 bench/gen_replays.py --suite $(_SUITE)

clean-bench:
	@find lp/bench -name '*.lp' -delete 2>/dev/null || true
	@find lp/bench -name '*.tmp' -delete 2>/dev/null || true
	@find lp/bench -name '*.goal' -delete 2>/dev/null || true
	@find lp/bench -name '*.res' -delete 2>/dev/null || true
	@find lp -name '*.lpo' -delete 2>/dev/null || true

clean: clean-bench
	@cd ocaml && dune clean

