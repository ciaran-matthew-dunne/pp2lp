.PHONY: help build check rules tree gen-traces gen-replays clean clean-bench repl

# Symlink-friendly: re-resolve PP2LP_ROOT every Make invocation.
export PP2LP_ROOT := $(CURDIR)

SUITE  ?= og
NAME   ?=
REPLAY ?=

# Resolve the target replay from {REPLAY, NAME, SUITE}.
# Priority: REPLAY > NAME+SUITE.  Empty if neither given.
# Support both the root bench directory and the xfail/ subdirectory.
ONE_REPLAY_BASE = $(if $(REPLAY),$(REPLAY),$(if $(NAME),lp/bench/$(SUITE)/$(NAME).replay))
ONE_REPLAY_XFAIL = $(if $(REPLAY),$(REPLAY),$(if $(NAME),lp/bench/$(SUITE)/xfail/$(NAME).replay))
ONE_REPLAY = $(if $(REPLAY),$(REPLAY),$(if $(wildcard $(ONE_REPLAY_BASE)),$(ONE_REPLAY_BASE),$(ONE_REPLAY_XFAIL)))

# Build a `bench/check.py` argument string from the three user vars.
# Priority: REPLAY > NAME+SUITE > SUITE.
CHECK_ARGS = $(if $(REPLAY),--replay $(REPLAY),\
             $(if $(NAME),--name $(NAME) --suite $(SUITE),\
             --suite $(SUITE)))

PP2LP = ./ocaml/_build/default/bin/main.exe

help:
	@echo "Common targets (SUITE defaults to og):"
	@echo "  build                            build the OCaml binary"
	@echo "  check                            emit + check the whole suite"
	@echo "  check NAME=01                    emit + check one replay in SUITE"
	@echo "  check REPLAY=path.replay         emit + check by path"
	@echo "  check ARGS='-q'                  pass-through flags to check.py"
	@echo "  tree NAME=01                     dump rebuilt proof tree"
	@echo "  rules NAME=01                    dump parsed (rule, arg, kind) lines"
	@echo "  gen-traces                       .but -> .trace (runs PP)"
	@echo "  gen-replays                      .trace -> .replay"
	@echo "  clean-bench                      just lp/bench/ generated files and lp/**/*.lpo"
	@echo "  clean                            blow away build + emitted LP + .lpo"
	@echo "  repl                             dune utop with project loaded"
	@echo ""
	@echo "Variables:"
	@echo "  SUITE   suite name under lp/bench/   (default: og)"
	@echo "  NAME    replay stem (e.g. 01)"
	@echo "  REPLAY  explicit path to a .replay"
	@echo "  ARGS    extra flags forwarded to check.py (-q, -v)"
	@echo ""
	@echo "Tips:"
	@echo "  - 'make tree NAME=27' shows the residual stack on tree-build error."
	@echo "  - 'make rules NAME=…' lists rules and flags any UNKNOWN ones."

build:
	@dune build --root ocaml

repl:
	@cd ocaml && dune utop src

check: build
	@python3 bench/check.py $(CHECK_ARGS) $(ARGS)

tree: build
	@$(if $(ONE_REPLAY),,$(error need NAME= or REPLAY=))
	@$(PP2LP) tree $(ONE_REPLAY)

rules: build
	@$(if $(ONE_REPLAY),,$(error need NAME= or REPLAY=))
	@$(PP2LP) rules $(ONE_REPLAY)

gen-traces:
	@python3 bench/gen_traces.py --suite $(SUITE)

gen-replays:
	@python3 bench/gen_replays.py --suite $(SUITE)

clean-bench:
	@find lp/bench -name '*.lp' -delete 2>/dev/null || true
	@find lp/bench -name '*.tmp' -delete 2>/dev/null || true
	@find lp/bench -name '*.goal' -delete 2>/dev/null || true
	@find lp/bench -name '*.res' -delete 2>/dev/null || true
	@find lp -name '*.lpo' -delete 2>/dev/null || true

clean: clean-bench
	@dune clean --root ocaml

