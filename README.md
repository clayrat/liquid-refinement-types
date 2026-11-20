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
   checked by code proved sound. When the obligation as it is gets no
   answer, the solver eliminates the equalities among its hypotheses and
   tries again; the steps of elimination are a part of the certificate.
2. **Liquid inference.** Holes in the contracts become unknowns κ with a
   finite list of qualifiers each; the same obligations, normalized into
   Horn constraints, are solved by iterative weakening. The solution is
   substituted into the contracts and checked again by the first algorithm,
   so inference is not in the trusted base.

Around them: an evaluator with fuel and the answers `Value`, `Timeout` and
`Stuck`, the operational guarantee of the first algorithm proved against
it, measures of termination checked as obligations of their own, and lists
whose length `len` exists only in the logic, with `append` checked in both
orders of the summands of its contract.

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
make demo         # the demonstrations 1–5 of the lecture, from the extract
make test         # regressions of the extract; the native reference against it
make check        # make, make assumptions and make test
make clean
```

Rocq 9.1.1 with its Stdlib; OCaml 4.14, dune 3.0 or later, ocamlfind and
zarith for the extraction and the native reference.

## Status

Levels 1 and 2 of the implementation plan are reached, and stage 8; level 3
is open.

| Component | Status |
|---|---|
| language, typing, evaluator with fuel (stage 1) | done, lists included; typed programs fail only by a read out of bounds |
| formulas, sorted substitution, obligations (stage 2) | done |
| difference solver with certificates (stage 3) | done; certificates and `prove` proved sound |
| `wp`, `gen`, `check_prog`, `check_client` (stage 4) | done; `gen` proved to be the unfolding of `wp` |
| operational guarantee (stage 5) | proved, recursive contracts included, by induction on fuel |
| Horn constraints, templates, weakening, inference (stage 6) | done; weakening proved to end within its fuel, the result rechecked by construction |
| measures of termination (stage 7) | done; `sum` proved to terminate with its exact fuel, `loop` to diverge and to have no measure |
| lists, `len`, `append`, elimination of equalities (stage 8) | done; the elimination proved sound, the guarantee extended to `match`, `append` accepted in both orders and its obligations also proved by `lia` |
| extraction, demonstrations 1–5, regressions, native reference (stage 9) | done; the optional comparison with z3 is not |

## What is proved

[theories/Contracts.v](theories/Contracts.v) states every guarantee as a
`Prop`; a contract followed by `…_holds` is proved, one without is open.
`make assumptions` checks that the 27 proved contracts are closed under the
global context.

- **The solver.** A model certificate satisfies the graph, a cycle of
  positive weight excludes every model, a cycle with the negation of an edge
  entails it; the elimination of equalities keeps validity (if the reduced
  obligation is valid, so is the original); a checked certificate of
  `Proved`, with its steps of elimination, makes the obligation valid, a
  checked counter-model falsifies it; hence `prove` is a sound oracle.
- **The language.** Typed programs, lists and `match` included, fail only by
  a read out of bounds; more fuel keeps a value.
- **Algorithm 1.** `gen` is `flatten ∘ wp`; the contracts of the primitives
  agree with their semantics; for every fuel, a function of an accepted
  program run on arguments that satisfy its precondition answers `Timeout`
  or a value satisfying its postcondition, never `Stuck`, and the same for
  an accepted client in every environment satisfying its assumption.
  Termination is not assumed: `loop` with the postcondition `false` passes.
  The equations of the measure `len` enter as the contracts of `nil` and
  `cons` and as the hypotheses of the branches of `match`.
- **Algorithm 2.** Normalization keeps the meaning of obligations; templates
  are turned into contracts whole (a template of an unknown function, a
  second template, a wrong number of refinements are errors, not dropped);
  weakening never runs out of its fuel `1 + Σ|Qκ|` and asks the oracle only
  obligations without unknowns (two oracles that agree on them give the same
  run); an `Inferred` answer is accepted by the first algorithm for the
  definitions and every client.
- **Termination.** An accepted table of measures has every measure turned
  into obligations and all of them proved; `sum` returns the sum of its
  array with the fuel `4·len a + 4` and never reads out of bounds; `loop`
  and its client time out for every fuel; `loop` is accepted and no measure
  of it is.
- **Lists.** `append` is accepted with `len ν = len xs + len ys` and with
  `len ν = len ys + len xs`, and rejected with `len ν = len xs`; the
  obligations of both orders are also proved by `lia` on the semantics,
  independently of the solver; its measure `len xs` is accepted; it returns
  `xs ++ ys` with the fuel `2·len xs + 2`, and whatever it returns has the
  length of its contract. Exercise 1 (`d = y − x`, the goal `0 < d`) is
  accepted after the elimination of `d`.

## What is checked on examples

- [theories/Tests.v](theories/Tests.v): by computation in Rocq, malformed
  templates and contracts refused rather than trimmed, the measures of
  the lecture and malformed ones, the steps of elimination checked (a
  certificate without them or with a forged one fails), two calls `f 0`
  refuted, the typing of `match`, the names with a dot (the copies `r.x`
  of the rule `RuleRoot`) refused as variables of programs and clients;
  clients checked separately (against the contracts and not the bodies,
  the need for their hypotheses, malformed clients refused, a client in
  inference, first in the order of weakening, and one whose property
  refutes it); boolean refinements (a dead branch under `b ∧ ¬b`,
  counter-models with `b` true and false, a precondition `b` or `¬b`
  inferred from the client of `choose`); the answer `Undecided`, with an
  oracle that never answers (and `Unknown` is not acceptance) and with the
  difference solver on the qualifier `0 ≤ i + n`, outside its fragment;
  and the hypothesis of the open contracts of weakening: an oracle complete
  on every obligation is unsound, one complete on the obligations without
  unknowns exists (with classical axioms, used only there).
- [extraction/regress.ml](extraction/regress.ml): the demonstrations
  against [lecture9.expected](extraction/lecture9.expected), the answers the
  lecture relies on, `gen = flatten wp` on every function of the examples,
  integers beyond the machine `int` in the evaluator and in the weights of
  cycles, a forged certificate and a forged step of elimination rejected,
  the fuel of `sum` and of `append` exact.
- [reference/](reference/): a self-contained native reference — its own
  syntax, generator, obligations of measure, solver (Floyd–Warshall instead
  of Bellman–Ford, its own elimination of equalities, which picks the
  nodes in another order) and weakening; it is compiled where the extract
  is not visible. `diff.ml` translates the examples into its syntax and compares
  the obligations, the verdicts (each side checks the other's
  counter-models), the qualifiers removed (also with a client, first in the
  order of weakening), the assignments, the kind of every answer of
  inference (`Undecided` included, after the same removals) and the
  refusals of malformed input: templates, measures and unknowns (not
  declared, applied to other sorts, in a qualifier, declared twice),
  refused by the native reference with `NFailed`, not with an exception.
  The boolean refinements of `Examples/Flags.v`, their clients and their
  inference are compared the same way, and so are goals with a conjunct
  outside the fragment: the conjuncts are decided in order, so
  `⊢ false ∧ x + y = 0` is refuted and `⊢ x + y = 0 ∧ false` is `Unknown`.

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
  its fragment (`solver_complete`); with an oracle sound and complete on
  the obligations without unknowns (complete on every obligation, it could
  not be sound: `⊢ ¬κ()` is neither valid nor refutable), weakening returns the strongest solution in Q or refutes when there is
  none (`weaken_strongest`) and does not depend on the order of the
  constraints (`weaken_order_independent`); proved obligations of measure
  and an order of the other calls imply termination
  (`measures_imply_termination`).
- The optional comparison of the obligations with z3 through SMT-LIB.

## The modules and the lecture plan

| Module | Section of [plan-ref-liquid.md](plan-ref-liquid.md) |
|---|---|
| `Lang/Syntax.v`, `Lang/Typing.v`, `Lang/Eval.v`, `Lang/EvalFacts.v` | Язык и соглашения |
| `Logic/Formula.v`, `Logic/Subst.v`, `Logic/Obligation.v` | Язык и соглашения; Алгоритм 1, §4 |
| `Solver/Diff.v`, `Solver/Linear.v`, `Solver/Elim.v`, `Solver/Prove.v` | Алгоритм 1, §4: логический решатель и смысл ответа |
| `Refine/Spec.v`, `Refine/Wp.v`, `Refine/Gen.v`, `Refine/Check.v` | Алгоритм 1, §1–3 |
| `Refine/Env.v`, `Refine/Sound.v` | Алгоритм 1, §5: что гарантирует принятие |
| `Refine/Measure.v` | Завершение, списки и границы гарантий |
| `Liquid/Template.v` | Алгоритм 2, §1 и §3: неизвестный инвариант, квалификаторы |
| `Liquid/Horn.v` | Алгоритм 2, §2: хорновы ограничения |
| `Liquid/Weaken.v` | Алгоритм 2, §4: итеративное ослабление |
| `Liquid/Infer.v` | Алгоритм 2, §1 и §5 |
| `Examples/Bounded.v`, `Examples/Inc.v`, `Examples/Calls.v` | Алгоритм 1, §2; особенности refhoare (имя результата, `APPᶜ`, `δ`); демонстрации 1 и 2 |
| `Examples/Sum.v` | Алгоритм 2, §5: три исхода; завершение `go`; демонстрация 3 |
| `Examples/Loop.v` | Завершение, списки и границы гарантий; демонстрация 4 |
| `Examples/Append.v` | Завершение, списки и границы гарантий: мера `len`, контракт `append`; Алгоритм 1, §4; демонстрация 5; упражнения 1 и 8 |
| `Examples/Flags.v` | — (not in the lecture: boolean refinements for the tests) |
| `Contracts.v`, `extraction/`, `reference/` | Сопровождающий артефакт и доказательные задачи |
