# continuous-kummer-theory

Continuous Kummer theory for local fields.

## Status

**Core targets formalised, no `sorry`/`axiom`** (axioms used: `propext`, `Classical.choice`,
`Quot.sound` only). Everything below is proved in Lean 4 / Mathlib v4.32.0 and builds with
`lake build --wfail`. All five follow-up targets of work package P7 (finiteness for `p`-adic
fields, comparison with Mathlib's `continuousCohomology`, independence of corestriction from
choices, topologies, Kummer classes of functions vs. values) are done; see *Scope notes* at the
end of this section for the precise form of each statement.

**Model of `H¹_cont`.** `ContH1 G M` (`ContH1/Basic.lean`) is the group of *continuous* crossed
homomorphisms `G → M` (Mathlib's `IsMulCocycle₁`, multiplicative notation) modulo principal ones
(`IsMulCoboundary₁`), for a topological group `G` acting on a commutative topological group `M`
(Serre, *Galois Cohomology*, Chapter I). This is the classical low-degree description; it is
identified with Mathlib's homogeneous-cochain `continuousCohomology 1` in
`ContH1/Comparison.lean` (see below). Coefficients `μ_n(Ω)` are the type `KummerTheory.Mu n Ω` (the roots of unity with the
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
  (cochain formula with chosen coset representatives; by `ContH1/CorestrictionIndep.lean`,
  `ContH1.cor_mk_eq_mk_corFunWith`, any other section `r` of `G → G ⧸ φ(H)` gives the same class,
  the two cocycles differing by the coboundary of `∏ₓ r(x) • c(hₓ)`
  (`ContH1.corFunWith_eq_mul`)); for a finite subextension `L` of a Galois
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
  `Kˣ/(Kˣ)ⁿ` is finite (`FiniteKummerQuotients K`), `kummerCompletionEquivProfiniteCompletion`
  identifies `(Kˣ)^∧` with Mathlib's `ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ)`,
  hence `kummerZHatEquivProfiniteCompletion : H¹_cont(G_K, Ẑ(1)) ≃* profinite completion of Kˣ`.
* **Finiteness of `Kˣ/(Kˣ)ⁿ` for `p`-adic fields** (`Kummer/PAdic.lean`):
  `finiteKummerQuotients_of_isDiscreteValuationRing` — `FiniteKummerQuotients K` for the fraction
  field `K` (characteristic zero) of a complete DVR (`IsAdicComplete (maximalIdeal R) R`) with
  finite residue field; instances for every `IsNonarchimedeanLocalField K` of characteristic zero
  (Mathlib's notion of non-archimedean local field, i.e. finite extensions of `ℚ_p`) and for
  `ℚ_[p]`, so `kummerZHatEquivProfiniteCompletion` applies unconditionally to them
  (`padicKummerZHatEquiv` for `ℚ_p`). The proof is self-contained: an `I`-adic Banach fixed-point
  theorem (`exists_fixedPoint_of_adicContraction`) gives the Hensel-type statement
  `1 + n²ϖ𝒪 ⊆ (𝒪ˣ)ⁿ` (`exists_pow_eq_one_add`, valid also when `p ∣ n`), and
  `Kˣ = ϖ^ℤ · 𝒪ˣ` with `𝒪/(n²ϖ)` finite bounds `Kˣ/(Kˣ)ⁿ`.
* **Comparison with Mathlib's continuous cohomology** (`ContH1/Comparison.lean`): for a
  topological representation `A : TopRep k G`,
  `ContH1.continuousCohomologyOneEquiv A : continuousCohomology 1 A ≃+ Additive (ContH1 G
  (Multiplicative A))`, sending the class of a homogeneous cocycle `σ` to the class of
  `g ↦ σ(1, g)` (`continuousCohomologyOneEquiv_π`); the `k`-linear, topological part is the
  isomorphism `continuousCohomologyOneIso` in `TopModuleCat k` onto `Z¹/B¹` with its quotient
  topology. (Only `≃+`: `ContH1` is a bare multiplicative group, without `k`-module structure.)
* **Topologies** (`Kummer/Topology.lean`): `H¹_cont(G, μ_n)` and `Kˣ/(Kˣ)ⁿ` are discrete (the
  latter as a scoped instance in `KummerTheory`, since a topological `K` already induces a
  quotient topology), `lim` objects carry the inverse-limit topology, and `H¹_cont(G_K, Ẑ(1))`
  carries the initial topology of the projections to the `H¹_cont(G_K, μ_n)`. It is a Hausdorff,
  totally disconnected topological group, compact if all `Kˣ/(Kˣ)ⁿ` are finite, and
  `h1ZHatOneContinuousEquiv`, `kummerLimitContinuousEquiv`, `kummerZHatContinuousEquiv` and
  `kummerZHatContinuousEquivProfiniteCompletion : H¹_cont(G_K, Ẑ(1)) ≃ₜ* (Kˣ)^∧` (profinite
  completion, for `char K = 0` with finite `Kˣ/(Kˣ)ⁿ`, e.g. `p`-adic fields) are topological group
  isomorphisms; the Kummer map has dense image (`denseRange_kummerZHat`).
* **Kummer classes of values of functions** (`Kummer/Values.lean`): for a `K`-algebra `R`, a point
  `x : R →ₐ[K] L` and `f ∈ Rˣ`, `kummerValue n L Ω x f = κ_L(f(x))`, with naturality in `R`,
  constants, vanishing on `n`-th powers, `restriction_kummerValue` (a `K`-point viewed over `L`)
  and `corestriction_kummerValue` (norm of the value for a point over a finite `L/K`).
* **Kummer class of a function vs. its value** (`Kummer/Specialization.lean`,
  `Kummer/Decomposition.lean`): for continuous `ι : D → Gal(Ω/F)`, `π : D → Gal(Ω_K/K)`, a
  subring `B ⊆ Ω` closed under `n`-th roots and `D`-stable, and a `D`-equivariant `ψ : B → Ω_K`,
  `map_kummer_eq_map_kummer : ι^* κ_F(f) = π^* κ_K(ψ f)` (coefficients specialised by
  `specMu`), and for a continuous section `s` of `π` (the section attached to a rational point)
  `map_section_kummer : s^* ι^* κ_F(f) = κ_K(f(x))`; in terms of points `x : R →ₐ[K] K`,
  `map_kummer_eq_map_kummerValue` and `map_section_kummer_eq_kummerValue`.
  Instantiated with an actual decomposition group (`Kummer/Decomposition.lean`): for a valuation
  subring `A ⊆ Ω` containing the constants `k`, Mathlib's `A.decompositionSubgroup F` maps by the
  continuous `Decomposition.decompositionMap` (kernel = `inertiaSubgroup`) to
  `Gal(ResidueField A / k)`, and `Decomposition.decomposition_kummer` /
  `decomposition_kummerValue` state: the restriction of `κ_F(f)` to the decomposition group is
  the inflation of `κ_k(f(x))`.

**Scope notes.** (1) "Finite extension of `ℚ_p`" is expressed through Mathlib's
`IsNonarchimedeanLocalField` (or a complete DVR with finite residue field); Mathlib does not yet
equip a bare `[FiniteDimensional ℚ_[p] L]` with that structure, so the instance applies once that
structure is provided. (2) The function-vs-value comparison is formulated with decomposition
groups (equivalently with a section of `π`), not with the étale fundamental group of a scheme,
which Mathlib does not have in a usable form for curves over non-closed fields. (3) The comparison
with `continuousCohomology` is in degree 1 only (degree 0 is Mathlib's `zeroIso`).

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
