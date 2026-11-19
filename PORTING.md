# Porting log

Every definition or proof taken from another project is recorded here: source
repository, commit, paths and the changes made. Ported proofs are re-checked
by this project's build. There are no submodules: the language is new and has
no syntax in common with the earlier artifacts, and the one large piece worth
taking (the graph of constraints) cannot be taken without changing its
semantics.

## Ported files

| Here | Source | Commit | Changes |
|---|---|---|---|
| `theories/Common/Result.v` | [pts-dependent-types](https://github.com/clayrat/pts-dependent-types), `theories/Common/Result.v` (itself from modules-system-fw) | `7655a28` on `cic` | none but the header line naming the route |
| `theories/Common/Traced.v` | pts-dependent-types, `theories/Common/Traced.v` | `7655a28` on `cic` | the prefix of the import (`Liquid.Common`), the header line |

## Adapted proofs and code

| Here | Source | Commit | Changes |
|---|---|---|---|
| `theories/Solver/Diff.v` | [erasure-cic](https://github.com/clayrat/erasure-cic), `theories/Universes/Graph.v` | `9560389` on `main` | Valuations in ℤ instead of ℕ, and no implicit base edges `0 ≤ a` (`base`, `relaxed` removed): over ℤ they would make `0 ≤ i` provable without hypotheses and lose the counter-model with a negative `i`. The caller adds `0 ≤ len a` and `0 ≤ b ≤ 1` (`Solver/Prove.v`). The atoms of `Level.v` are replaced by the nodes `0`, `x`, `b`, `len a`; Bellman–Ford starts from a virtual source, the default distance `0` of `dget`. The verdicts are renamed (`GModel`, `GCycle`, `GUnknown`; `Entailed`, `Countered`, `EUnknown`), and the certificate of an entailment gets its own check `entailment_ok`. `cycle_ok_sound`, `chain_ok_sum`, `solve_cycle` and the lemmas of entailment are carried over almost verbatim. |
| `Makefile`, `_CoqProject`, `.gitignore` | erasure-cic, the same files | `9560389` | no submodules; the target `assumptions` reads `theories/Contracts.v` only |
| `extraction/Makefile`, `extraction/dune`, `extraction/dune-project`, `extraction/Extract.v` | erasure-cic, `extraction/` | `9560389` | ℤ and ℕ extracted to the exact integers of Zarith (`ExtrOcamlZBigInt`, `ExtrOcamlNatBigInt`) instead of OCaml `int`; the library `zarith` linked; the demonstrations moved into a library module `demos.ml` shared by `main.ml` and `regress.ml`; the target `expected` |
| `extraction/regress.ml` | erasure-cic, `extraction/regress.ml` | `9560389` | the helper `expect`; the checks are new |
| `reference/Makefile` | erasure-cic, `reference/Makefile` | `9560389` | the compiler called through `ocamlfind` with the package `zarith` instead of bare `ocamlc`; the native reference compiled first, where the extract is not visible |

## Taken as a pattern only

- strictness-pcf, `OperationalSemantics.v`, `Safety.v`: the three answers of the
  evaluator, `evalFuel_value_mono`, `diverges := ∀ fuel, Timeout`, the shape of
  the contract `check_eval_contract`. The evaluator is new: big step, by value,
  first order.
- refhoare (`refhoare.lagda`): the structure of `prevc-soundness′` as the
  pattern of the operational guarantee. No code: Agda, predicates of the
  metalanguage, the postulated `δ`; the unused declaration `absurd` is not
  reproduced.
