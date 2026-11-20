COQC ?= coqc
DUNE ?= dune
COQFLAGS := -Q ../theories Liquid

.PHONY: all core extract run test expected clean
all: run

# Run from the top-level Makefile, the Rocq development is built already
# (ROCQ_BUILT=1), and extracted before run and test (EXTRACTED=1): neither
# starts again, so that make -j at the top has one build and one
# extraction.  Run here, the targets build and extract first.
ifeq ($(ROCQ_BUILT)$(EXTRACTED),)
core:
	$(MAKE) -C .. rocq
else
core: ;
endif

ifeq ($(EXTRACTED),)
PREPARE := extract
endif

# Extract.v writes generated/liquid.ml.
extract: core
	mkdir -p generated
	$(COQC) $(COQFLAGS) Extract.v

run: $(PREPARE)
	$(DUNE) exec ./main.exe

test: $(PREPARE)
	$(DUNE) test

# Regenerates lecture9.expected from the current demos; review the diff.
expected: $(PREPARE)
	$(DUNE) exec ./main.exe > lecture9.expected

clean:
	rm -rf generated *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
