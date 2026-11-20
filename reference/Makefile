OCAMLFIND ?= ocamlfind
GENERATED := ../extraction/generated

.PHONY: all extract test clean
all: test

# Run from the top-level Makefile, the extract is ready (EXTRACTED=1);
# run here, it is built first.
ifeq ($(EXTRACTED),)
PREPARE := extract
endif

extract:
	$(MAKE) -C ../extraction extract

# The native reference is self-contained: it is compiled first, on its
# own, where the extract is not visible, so that a use of anything of the
# extract would fail to compile.  diff.ml, the bridge, sees both; liquid.ml
# is copied into _build and compiled there as it is.  The files here are
# compiled where they are, so that errors point at them, into _build, with
# every warning an error except fragile matches (4), record patterns
# without [_] (9), type-directed disambiguation (40-42, 44, 45) and missing
# interfaces (70).
WARNINGS := -w +A-4-9-40-41-42-44-45-70 -warn-error +A
OCAMLC := $(OCAMLFIND) ocamlc -package zarith

test: $(PREPARE)
	mkdir -p _build
	$(OCAMLC) $(WARNINGS) -c -o _build/liquid_native liquid_native.ml
	cp $(GENERATED)/liquid.ml $(GENERATED)/liquid.mli _build/
	cd _build && $(OCAMLC) -w -a -c liquid.mli liquid.ml
	$(OCAMLC) $(WARNINGS) -I _build -c -o _build/diff diff.ml
	$(OCAMLC) -linkpkg _build/liquid.cmo _build/liquid_native.cmo _build/diff.cmo -o _build/diff
	_build/diff

clean:
	rm -rf _build
