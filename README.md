# continuous-kummer-theory

Continuous Kummer theory for local fields.

## Status

**Core targets formalised, no `sorry`/`axiom`** (axioms used: `propext`, `Classical.choice`,
`Quot.sound` only). Everything below is proved in Lean 4 / Mathlib v4.32.0 and builds with
`lake build --wfail`. Not formalised: see *Not done* at the end of this section.

**Model of `H¹_cont`.** `ContH1 G M` (`ContH1/Basic.lean`) is the group of *continuous* crossed
homomorphisms `G → M` (Mathlib's `IsMulCocycle₁`, multiplicative notation) modulo principal ones
(`IsMulCoboundary₁`), for a topological group `G` acting on a commutative topological group `M`
(Serre, *Galois Cohomology*, Chapter I). This is the classical low-degree description; Mathlib's
`ContinuousCohomology` (homogeneous cochains) currently only computes `H⁰`, so no comparison with it
is proved. Coefficients `μ_n(Ω)` are the type `KummerTheory.Mu n Ω` (the roots of unity with the
discrete topology and the Galois action); Galois groups `Gal(Ω/K)` carry the Krull topology.

Proved results (namespace `KummerTheory` unless stated):

* **Hilbert 90 for infinite Galois extensions** (`Hilbert90.lean`):
  `isMulCoboundary₁_of_eventually_eq_one` — a 1-cocycle `Gal(Ω/K) → Ωˣ` that is `1` near `1`
  (i.e. continuous for the discrete topology on `Ωˣ`) is a coboundary, for any Galois `Ω/K`.
* **Kummer isomorphism** (`Kummer/Basic.lean`, `Kummer/Equiv.lean`): the Kummer map
  `kummer n K Ω : Kˣ →* ContH1 Gal(Ω/K) (Mu n Ω)`, `a ↦ [σ ↦ σ(a^{1/n})/a^{1/n}]`, has kernel
  `(Kˣ)ⁿ` (`ker_kummer`) and is surjective (`kummer_surjective`), giving
  `kummerEquiv : Kˣ ⧸ (Kˣ)ⁿ ≃* H¹_cont(Gal(Ω/K), μ_n)` for every Galois `Ω/K` containing `n`-th
  roots of all elements of `K` (`HasKummerRoots`); special cases `kummerEquivSepClosure`
  (separable closure, `n` invertible in `K`) and `kummerEquivAlgClosure` (perfect `K`, algebraic
  closure, i.e. Mathlib's `Field.absoluteGaloisGroup`).
* **Restriction** (`Kummer/Restriction.lean`): for any field extension `L/K` with compatible
  `Ω_K → Ω_L` (`Ω_K/K` normal), `galRestrict : Gal(Ω_L/L) →* Gal(Ω_K/K)` is continuous and
  `restriction_kummer : res (κ_K a) = κ_L a`.
* **Corestriction and norm** (`ContH1/Corestriction.lean`, `Kummer/Corestriction.lean`): the
  degree-one corestriction `ContH1.cor` along an injective homomorphism with image of finite index
  (cochain formula with chosen coset representatives); for a finite subextension `L` of a Galois
  `Ω/K`, `corestriction L n` and `corestriction_kummer : cor (κ_L a) = κ_K (N_{L/K} a)`, using
  `prod_corRep_eq_norm` (`N_{L/K}(a)` is the product of the conjugates over coset
  representatives). Consequence: `corestriction_restriction : cor ∘ res = (·)^[L:K]`
  (`Kummer/CorRes.lean`).
* **Inverse-limit form** (`Kummer/Limit.lean`, `Kummer/ZHat.lean`): with `n` ranging over the
  integers invertible in `K` ordered by divisibility (`KummerIndex K`), `ZHatOne K Ω = lim μ_n(Ω)`
  (`Ẑ(1)`, prime-to-`p` part in characteristic `p`) with the inverse-limit topology, and
  `KummerCompletion K = lim Kˣ/(Kˣ)ⁿ`:
  `kummerLimitEquiv : (Kˣ)^∧ ≃* lim H¹_cont(G_K, μ_n)`,
  `h1ZHatOneEquiv : H¹_cont(G_K, Ẑ(1)) ≃* lim H¹_cont(G_K, μ_n)` (no hypothesis on `K`; a
  König/compactness argument, `exists_compatible_family`), and
  `kummerZHatEquiv : H¹_cont(G_K, Ẑ(1)) ≃* (Kˣ)^∧` for `Ω` a separable closure (`IsGalois`,
  `IsSepClosed`). The `Ẑ(1)`-valued Kummer map `kummerZHat` has components `kummer i.n`
  (`h1Proj_kummerZHat`).
* **Profinite completion** (`Kummer/ProfiniteCompletion.lean`): if `char K = 0` and every
  `Kˣ/(Kˣ)ⁿ` is finite (`FiniteKummerQuotients K`, e.g. `p`-adic fields — this hypothesis is not
  proved for `p`-adic fields here), `kummerCompletionEquivProfiniteCompletion` identifies `(Kˣ)^∧`
  with Mathlib's `ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ)`, hence
  `kummerZHatEquivProfiniteCompletion : H¹_cont(G_K, Ẑ(1)) ≃* profinite completion of Kˣ`.
* **Kummer classes of values of functions** (`Kummer/Values.lean`): for a `K`-algebra `R`, a point
  `x : R →ₐ[K] L` and `f ∈ Rˣ`, `kummerValue n L Ω x f = κ_L(f(x))`, with naturality in `R`,
  constants, vanishing on `n`-th powers, `restriction_kummerValue` (a `K`-point viewed over `L`)
  and `corestriction_kummerValue` (norm of the value for a point over a finite `L/K`).

**Not done.** The comparison of `κ(f(x))` with the Kummer class of `f` in the cohomology of the
function field / étale fundamental group via the section attached to a rational point (needed to
*identify* the étale theta classes) is not formalised; nor is the identification of `ContH1` with
Mathlib's homogeneous-cochain `ContinuousCohomology` in degree 1, independence of `ContH1.cor`
from the choice of coset representatives, topologies on the cohomology groups, or the finiteness
of `Kˣ/(Kˣ)ⁿ` for `p`-adic fields.

No lana-agents repository depends on this one yet: `iut` and its pinned lana-agents
dependencies do not `require` it.

## Goals

(These were the goals when the repository was created; see *Status* for what is done.)

Formalise continuous Kummer theory in a Mathlib-style API, for a field `K` with a chosen separable/algebraic closure.

The main targets are the natural equivalence

```
Kˣ/(Kˣ)ⁿ ≃ H¹_cont(G_K, μ_n)
```

its inverse-limit / profinite-completion form `H¹_cont(G_K, Ẑ(1)) ≃ Kˣ∧`, and functoriality under finite extensions (restriction, corestriction, and norm).

Also in scope: the Kummer classes of values of rational/meromorphic functions needed to state the étale theta construction.

Mathlib already contains continuous cohomology (degree 0 computed), low-degree group cohomology,
Hilbert 90 for finite extensions, and finite Kummer-extension infrastructure.

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

License: Apache 2.0 (see LICENSE).
