# continuous-kummer-theory

Continuous Kummer theory for local fields.

## Status

**Not started.** The repository is the initial project scaffold (a single commit,
2026-07-20). The library `ContinuousKummerTheory` contains only the placeholder module
`ContinuousKummerTheory/Basic.lean`, which has no declarations: there are no definitions or theorems yet
(and so no `sorry`, `axiom` or `admit`). Everything under *Goals* below is planned, not
formalised.

No lana-agents repository depends on this one: `iut` and its pinned lana-agents
dependencies do not `require` it.

## Goals

Formalise continuous Kummer theory in a Mathlib-style API, for a field `K` with a chosen separable/algebraic closure.

The main targets are the natural equivalence

```
Kˣ/(Kˣ)ⁿ ≃ H¹_cont(G_K, μ_n)
```

its inverse-limit / profinite-completion form `H¹_cont(G_K, Ẑ(1)) ≃ Kˣ∧`, and functoriality under finite extensions (restriction, corestriction, and norm).

Also in scope: the Kummer classes of values of rational/meromorphic functions needed to state the étale theta construction.

Mathlib already contains continuous cohomology, low-degree group cohomology, Hilbert 90, and finite Kummer-extension infrastructure.

## Established sources

* Serre, *Galois Cohomology*.
* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*.
* Milne, *Étale Cohomology*.

## Related repositories

Intended as a foundation for `local-class-field-theory` (also not started) and for
`tate-curves-theta`, whose README lists it as a future dependency; neither `require`s
it. The link between the theta function and its Kummer class is not done in
`tate-curves-theta`.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`), its only direct dependency.
Library sources live under `ContinuousKummerTheory/`, and every file must be imported from
the root module `ContinuousKummerTheory.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib ContinuousKummerTheory --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#11](https://taxis.lana.merten.dev/issues/11)
