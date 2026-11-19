COQC ?= coqc
DUNE ?= dune
COQFLAGS := -Q ../theories Liquid

.PHONY: all core extract run test expected clean
all: run

core:
	$(MAKE) -C .. rocq

# Extract.v writes generated/liquid.ml.
extract: core
	mkdir -p generated
	$(COQC) $(COQFLAGS) Extract.v

run: extract
	$(DUNE) exec ./main.exe

test: extract
	$(DUNE) test

# Regenerates lecture9.expected from the current demos; review the diff.
expected: extract
	$(DUNE) exec ./main.exe > lecture9.expected

clean:
	rm -rf generated *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
