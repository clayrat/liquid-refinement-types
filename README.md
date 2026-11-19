# liquid-refinement-types

The executable companion to lecture 9, refinement types and Liquid Types.
It is built around two algorithms:

1. **Checking refinement contracts.** A first-order program in ANF with
   ordinary types, a table of contracts and a required property of the
   result. `gen` walks the program once and emits flat labelled obligations
   `H₁, …, Hₙ ⊢ g` — a body against its contract, the input of a call, the
   use of a result; it is proved to be the unfolding of `wp` relative to the
   contracts. A difference solver over ℤ answers each with `Proved` and a
   cycle, `Refuted` and a counter-model, or `Unknown`; both certificates are
   checked by code proved sound.
2. **Liquid inference.** Holes in the contracts become unknowns κ with a
   finite list of qualifiers each; the same obligations, normalized into
   Horn constraints, are solved by iterative weakening. The solution is
   substituted into the contracts and checked again by the first algorithm,
   so inference is not in the trusted base.

Around them: an evaluator with fuel and the answers `Value`, `Timeout` and
`Stuck`, the operational guarantee of the first algorithm proved against
it, and measures of termination checked as obligations of their own.

Definitions, algorithms and proofs are in Rocq, extracted to OCaml with the
exact integers of Zarith; a thin OCaml shell prints the demonstrations. The
lecture plan is [plan-ref-liquid.md](plan-ref-liquid.md); the implementation
plan, its stages and readiness levels are in
[plan-liquid-impl.md](plan-liquid-impl.md). What was taken from the earlier
projects is in [PORTING.md](PORTING.md).

## Build

```sh
make              # the Rocq development
make assumptions  # every proved contract is axiom-free
make demo         # the demonstrations of the lecture, from the extract
make test         # regressions of the extract; the native reference against it
make check        # make, make assumptions and make test
make clean
```

Rocq 9.1.1 with its Stdlib; OCaml 4.14, dune 3.0 or later, ocamlfind and
zarith for the extraction and the native reference.

## Status

Levels 1 and 2 of the implementation plan are reached; level 3 and stage 8
are open.

| Component | Status |
|---|---|
| language, typing, evaluator with fuel (stage 1) | done; typed programs fail only by a read out of bounds |
| formulas, sorted substitution, obligations (stage 2) | done |
| difference solver with certificates (stage 3) | done; certificates and `prove` proved sound |
| `wp`, `gen`, `check_prog`, `check_client` (stage 4) | done; `gen` proved to be the unfolding of `wp` |
| operational guarantee (stage 5) | proved, recursive contracts included, by induction on fuel |
| Horn constraints, templates, weakening, inference (stage 6) | done; weakening proved to end within its fuel, the result rechecked by construction |
| measures of termination (stage 7) | done; `sum` proved to terminate with its exact fuel, `loop` to diverge and to have no measure |
| lists, `len`, `append`, elimination of equalities (stage 8) | not started |
| extraction, demonstrations 1–4, regressions, native reference (stage 9) | done; the optional comparison with z3 is not |

## What is proved

[theories/Contracts.v](theories/Contracts.v) states every guarantee as a
`Prop`; a contract followed by `…_holds` is proved, one without is open.
`make assumptions` checks that the 21 proved contracts are closed under the
global context.

- **The solver.** A model certificate satisfies the graph, a cycle of
  positive weight excludes every model, a cycle with the negation of an edge
  entails it; a checked certificate of `Proved` makes the obligation valid,
  a checked counter-model falsifies it; hence `prove` is a sound oracle.
- **The language.** Typed programs fail only by a read out of bounds; more
  fuel keeps a value.
- **Algorithm 1.** `gen` is `flatten ∘ wp`; the contracts of the primitives
  agree with their semantics; for every fuel, a function of an accepted
  program run on arguments that satisfy its precondition answers `Timeout`
  or a value satisfying its postcondition, never `Stuck`, and the same for
  an accepted client in every environment satisfying its assumption.
  Termination is not assumed: `loop` with the postcondition `false` passes.
- **Algorithm 2.** Normalization keeps the meaning of obligations; templates
  are turned into contracts whole (a template of an unknown function, a
  second template, a wrong number of refinements are errors, not dropped);
  weakening never runs out of its fuel `1 + Σ|Qκ|`; an `Inferred` answer is
  accepted by the first algorithm for the definitions and every client.
- **Termination.** An accepted table of measures has every measure turned
  into obligations and all of them proved; `sum` returns the sum of its
  array with the fuel `4·len a + 4` and never reads out of bounds; `loop`
  and its client time out for every fuel; `loop` is accepted and no measure
  of it is.

## What is checked on examples

- [theories/Tests.v](theories/Tests.v): by computation in Rocq, malformed
  templates and contracts refused rather than trimmed, and the measures of
  the lecture and malformed ones.
- [extraction/regress.ml](extraction/regress.ml): the demonstrations
  against [lecture9.expected](extraction/lecture9.expected), the answers the
  lecture relies on, `gen = flatten wp` on every function of the examples,
  integers beyond the machine `int` in the evaluator and in the weights of
  cycles, a forged certificate rejected, the fuel of `sum` exact on arrays
  of lengths 0–6.
- [reference/](reference/): a self-contained native reference — its own
  syntax, generator, obligations of measure, solver (Floyd–Warshall instead
  of Bellman–Ford) and weakening; it is compiled where the extract is not
  visible. `diff.ml` translates the examples into its syntax and compares
  the obligations, the verdicts (each side checks the other's
  counter-models), the qualifiers removed, the assignments and the refusals
  of malformed input.

## What is trusted

The Rocq kernel; the extraction to OCaml, with the integers as Zarith
integers and strings as OCaml strings
([extraction/Extract.v](extraction/Extract.v)); the OCaml printer and
demonstrations ([pretty.ml](extraction/pretty.ml),
[demos.ml](extraction/demos.ml)). Not trusted: the solver, whose answers
carry checked certificates, and inference, whose result is rechecked. The
native reference is not covered by the proofs.

## Open

- Level 3, stated in Contracts.v: the solver does not answer `Unknown` on
  its fragment (`solver_complete`); with a sound and complete oracle,
  weakening returns the strongest solution in Q or refutes when there is
  none (`weaken_strongest`) and does not depend on the order of the
  constraints (`weaken_order_independent`); proved obligations of measure
  and an order of the other calls imply termination
  (`measures_imply_termination`).
- Stage 8: the elimination of equalities in the solver, with its proof.
  Until then the obligation of demonstration 2 with two calls `f 0`
  (`d = r1 − r2`) is outside the fragment and answered `Unknown`. Lists
  with `len`, `append` in both orders of the sum (demonstration 5), and the
  same obligations proved by `lia`.
- The optional comparison of the obligations with z3 through SMT-LIB.

## The modules and the lecture plan

| Module | Section of [plan-ref-liquid.md](plan-ref-liquid.md) |
|---|---|
| `Lang/Syntax.v`, `Lang/Typing.v`, `Lang/Eval.v`, `Lang/EvalFacts.v` | Язык и соглашения |
| `Logic/Formula.v`, `Logic/Subst.v`, `Logic/Obligation.v` | Язык и соглашения; Алгоритм 1, §4 |
| `Solver/Diff.v`, `Solver/Linear.v`, `Solver/Prove.v` | Алгоритм 1, §4: логический решатель и смысл ответа |
| `Refine/Spec.v`, `Refine/Wp.v`, `Refine/Gen.v`, `Refine/Check.v` | Алгоритм 1, §1–3 |
| `Refine/Sound.v` | Алгоритм 1, §5: что гарантирует принятие |
| `Refine/Measure.v` | Завершение, списки и границы гарантий |
| `Liquid/Template.v` | Алгоритм 2, §1 и §3: неизвестный инвариант, квалификаторы |
| `Liquid/Horn.v` | Алгоритм 2, §2: хорновы ограничения |
| `Liquid/Weaken.v` | Алгоритм 2, §4: итеративное ослабление |
| `Liquid/Infer.v` | Алгоритм 2, §1 и §5 |
| `Examples/Bounded.v`, `Examples/Inc.v`, `Examples/Calls.v` | Алгоритм 1, §2; особенности refhoare (имя результата, `APPᶜ`); демонстрации 1 и 2 |
| `Examples/Sum.v` | Алгоритм 2, §5: три исхода; завершение `go`; демонстрация 3 |
| `Examples/Loop.v` | Завершение, списки и границы гарантий; демонстрация 4 |
| `Contracts.v`, `extraction/`, `reference/` | Сопровождающий артефакт и доказательные задачи |
