/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.ProfiniteCompletion

/-!
# Topologies on the Kummer cohomology groups

We equip the groups appearing in the inverse-limit form of Kummer theory with their natural
(profinite-style) topologies and upgrade the Kummer isomorphisms to isomorphisms of topological
groups (`≃ₜ*`).

* `H¹_cont(G, μ_n)` is discrete (an instance for `ContH1 G (KummerTheory.Mu n Ω)`).
* `Kˣ/(Kˣ)ⁿ` is discrete. Since `Kˣ ⧸ (Kˣ)ⁿ` already carries Mathlib's quotient topology whenever
  `K` is a topological field (e.g. `ℚ`, where it is *not* discrete), this is a *scoped* instance
  in the namespace `KummerTheory`.
* `KummerTheory.KummerCompletion K` and `KummerTheory.H1Limit K Ω` then carry the inverse-limit
  topology, i.e. the subspace topology of the product of the discrete factors; no new instance is
  needed for them.
* `H¹_cont(G_K, Ẑ(1))` gets the topology induced by the comparison map
  `KummerTheory.h1ToLimit : H¹_cont(G_K, Ẑ(1)) → lim_n H¹_cont(G_K, μ_n)`, i.e. the coarsest
  topology making all projections to the discrete groups `H¹_cont(G_K, μ_n)` continuous.

## Main results

* `KummerTheory.h1ZHatOneContinuousEquiv : ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃ₜ* H1Limit K Ω`.
* `KummerTheory.kummerLimitContinuousEquiv : KummerCompletion K ≃ₜ* H1Limit K Ω`.
* `KummerTheory.kummerZHatContinuousEquiv : ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃ₜ* KummerCompletion K`.
* `KummerTheory.kummerCompletionContinuousEquivProfiniteCompletion` and
  `KummerTheory.kummerZHatContinuousEquivProfiniteCompletion`: for `char K = 0` with all
  `Kˣ/(Kˣ)ⁿ` finite, `H¹_cont(G_K, Ẑ(1)) ≃ₜ* (Kˣ)^∧`, Mathlib's profinite completion of `Kˣ`.
* Under `KummerTheory.FiniteKummerQuotients K`, `H¹_cont(G_K, Ẑ(1))` is profinite: compact,
  Hausdorff and totally disconnected.
* `KummerTheory.denseRange_toKummerCompletion`, `KummerTheory.denseRange_kummerZHat`: the Kummer
  map `Kˣ → H¹_cont(G_K, Ẑ(1))` has dense image.
-/

open CategoryTheory ProfiniteGrp ProfiniteCompletion Topology

namespace KummerTheory

section Discrete

variable {G : Type*} [Group G] [TopologicalSpace G] (n : ℕ) (Ω : Type*) [Field Ω]
  [MulDistribMulAction G (Mu n Ω)]

/-- `H¹_cont(G, μ_n)` (finite discrete coefficients) carries the discrete topology. -/
instance : TopologicalSpace (ContH1 G (Mu n Ω)) := ⊥

instance : DiscreteTopology (ContH1 G (Mu n Ω)) := ⟨rfl⟩

instance : IsTopologicalGroup (ContH1 G (Mu n Ω)) where

variable (K : Type*) [Field K]

/-- The discrete topology on `Kˣ/(Kˣ)ⁿ`. This is a scoped instance, since for a topological
field `K` Mathlib's quotient topology on `Kˣ ⧸ (Kˣ)ⁿ` also applies (and need not be discrete). -/
scoped instance : TopologicalSpace (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := ⊥

scoped instance : DiscreteTopology (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := ⟨rfl⟩

scoped instance : IsTopologicalGroup (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) where

end Discrete

section Limits

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- The closedness of `lim_n H¹_cont(G_K, μ_n)` in the product of the discrete groups. -/
theorem isClosed_h1Limit :
    IsClosed (H1Limit K Ω : Set (∀ i : KummerIndex K, ContH1 Gal(Ω/K) (Mu i.n Ω))) := by
  have : (H1Limit K Ω : Set (∀ i : KummerIndex K, ContH1 Gal(Ω/K) (Mu i.n Ω))) =
      ⋂ (i) (j) (h : i ≤ j), {x | h1Transition K Ω h (x j) = x i} := by
    ext x
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h =>
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply j)) (continuous_apply i)

/-- The closedness of `lim_n Kˣ/(Kˣ)ⁿ` in the product of the discrete groups. -/
theorem isClosed_kummerCompletion :
    IsClosed (KummerCompletion K :
      Set (∀ i : KummerIndex K, Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range)) := by
  have : (KummerCompletion K :
      Set (∀ i : KummerIndex K, Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range)) =
      ⋂ (i) (j) (h : i ≤ j), {x | quotTransition K h (x j) = x i} := by
    ext x
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h =>
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply j)) (continuous_apply i)

instance [FiniteKummerQuotients K] : CompactSpace (KummerCompletion K) := by
  haveI : ∀ i : KummerIndex K, Finite (Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range) := fun i =>
    haveI := FiniteKummerQuotients.finiteIndex (K := K) i.n i.n_ne_zero
    Subgroup.finite_quotient_of_finiteIndex
  exact isCompact_iff_compactSpace.1 (isClosed_kummerCompletion K).isCompact

theorem continuous_kummerLimitEquiv [IsGalois K Ω] [IsSepClosed Ω] :
    Continuous (kummerLimitEquiv K Ω) :=
  continuous_induced_rng.2 <| continuous_pi fun i =>
    (continuous_of_discreteTopology (f := fun y : Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range =>
      kummerEquiv i.n K Ω y)).comp ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_kummerLimitEquiv_symm [IsGalois K Ω] [IsSepClosed Ω] :
    Continuous (kummerLimitEquiv K Ω).symm :=
  continuous_induced_rng.2 <| continuous_pi fun i =>
    (continuous_of_discreteTopology (f := fun y : ContH1 Gal(Ω/K) (Mu i.n Ω) =>
      (kummerEquiv i.n K Ω).symm y)).comp ((continuous_apply i).comp continuous_subtype_val)

/-- The isomorphism `(Kˣ)^∧ ≃ lim_n H¹_cont(G_K, μ_n)` is a homeomorphism. -/
noncomputable def kummerLimitContinuousEquiv [IsGalois K Ω] [IsSepClosed Ω] :
    KummerCompletion K ≃ₜ* H1Limit K Ω where
  toMulEquiv := kummerLimitEquiv K Ω
  continuous_toFun := continuous_kummerLimitEquiv K Ω
  continuous_invFun := continuous_kummerLimitEquiv_symm K Ω

@[simp]
theorem kummerLimitContinuousEquiv_apply [IsGalois K Ω] [IsSepClosed Ω] (x : KummerCompletion K) :
    kummerLimitContinuousEquiv K Ω x = kummerLimitEquiv K Ω x := rfl

instance [IsGalois K Ω] [IsSepClosed Ω] [FiniteKummerQuotients K] :
    CompactSpace (H1Limit K Ω) :=
  (kummerLimitContinuousEquiv K Ω).toHomeomorph.compactSpace

/-- The canonical map `Kˣ → (Kˣ)^∧ = lim_n Kˣ/(Kˣ)ⁿ` has dense image. -/
theorem denseRange_toKummerCompletion : DenseRange (toKummerCompletion K) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U ⟨s, hs, rfl⟩ ⟨x, hx⟩
  obtain ⟨I, u, hu, hIs⟩ := isOpen_pi_iff.1 hs _ hx
  obtain ⟨j, hj⟩ := I.exists_le
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (x.1 j)
  refine ⟨toKummerCompletion K a, hIs fun i hi => ?_, a, rfl⟩
  have : (toKummerCompletion K a).1 i = x.1 i := by
    rw [← x.2 i j (hj i hi), ← ha]
    rfl
  rw [this]
  exact (hu i hi).2

end Limits

section ZHat

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- The topology on `H¹_cont(G_K, Ẑ(1))`: the topology induced by the comparison map
`H¹_cont(G_K, Ẑ(1)) → lim_n H¹_cont(G_K, μ_n)`, i.e. the coarsest topology for which all the
projections `H¹_cont(G_K, Ẑ(1)) → H¹_cont(G_K, μ_n)` (to discrete groups) are continuous. -/
noncomputable instance : TopologicalSpace (ContH1 Gal(Ω/K) (ZHatOne K Ω)) :=
  TopologicalSpace.induced (h1ToLimit K Ω) inferInstance

theorem isInducing_h1ToLimit : IsInducing (h1ToLimit K Ω) := ⟨rfl⟩

theorem isEmbedding_h1ToLimit : IsEmbedding (h1ToLimit K Ω) :=
  ⟨isInducing_h1ToLimit K Ω, h1ToLimit_injective K Ω⟩

theorem continuous_h1ToLimit : Continuous (h1ToLimit K Ω) :=
  (isInducing_h1ToLimit K Ω).continuous

theorem continuous_h1Proj (i : KummerIndex K) : Continuous (h1Proj K Ω i) :=
  (continuous_apply i).comp (continuous_subtype_val.comp (continuous_h1ToLimit K Ω))

instance : IsTopologicalGroup (ContH1 Gal(Ω/K) (ZHatOne K Ω)) :=
  topologicalGroup_induced (h1ToLimit K Ω)

/-- **Continuous cohomology commutes with the inverse limit** `Ẑ(1) = lim_n μ_n`, as topological
groups: `H¹_cont(G_K, Ẑ(1)) ≃ₜ* lim_n H¹_cont(G_K, μ_n)`. -/
noncomputable def h1ZHatOneContinuousEquiv : ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃ₜ* H1Limit K Ω where
  toMulEquiv := h1ZHatOneEquiv K Ω
  continuous_toFun := continuous_h1ToLimit K Ω
  continuous_invFun := by
    rw [(isInducing_h1ToLimit K Ω).continuous_iff]
    convert continuous_id
    exact funext fun y => (h1ZHatOneEquiv K Ω).apply_symm_apply y

@[simp]
theorem h1ZHatOneContinuousEquiv_apply (x : ContH1 Gal(Ω/K) (ZHatOne K Ω)) :
    h1ZHatOneContinuousEquiv K Ω x = h1ToLimit K Ω x := rfl

instance : T2Space (ContH1 Gal(Ω/K) (ZHatOne K Ω)) :=
  (h1ZHatOneContinuousEquiv K Ω).toHomeomorph.symm.t2Space

instance : TotallyDisconnectedSpace (ContH1 Gal(Ω/K) (ZHatOne K Ω)) :=
  (h1ZHatOneContinuousEquiv K Ω).toHomeomorph.symm.totallyDisconnectedSpace

variable [IsGalois K Ω] [IsSepClosed Ω]

/-- **Kummer theory, inverse-limit form, topologically**: `H¹_cont(G_K, Ẑ(1)) ≃ₜ* (Kˣ)^∧`. -/
noncomputable def kummerZHatContinuousEquiv :
    ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃ₜ* KummerCompletion K :=
  (h1ZHatOneContinuousEquiv K Ω).trans (kummerLimitContinuousEquiv K Ω).symm

@[simp]
theorem kummerZHatContinuousEquiv_apply (x : ContH1 Gal(Ω/K) (ZHatOne K Ω)) :
    kummerZHatContinuousEquiv K Ω x = kummerZHatEquiv K Ω x := rfl

instance [FiniteKummerQuotients K] : CompactSpace (ContH1 Gal(Ω/K) (ZHatOne K Ω)) :=
  (kummerZHatContinuousEquiv K Ω).toHomeomorph.symm.compactSpace

/-- The `Ẑ(1)`-valued Kummer map `Kˣ → H¹_cont(G_K, Ẑ(1))` has dense image. -/
theorem denseRange_kummerZHat : DenseRange (kummerZHat K Ω) :=
  show DenseRange ((kummerZHatEquiv K Ω).symm ∘ toKummerCompletion K) from
    (kummerZHatContinuousEquiv K Ω).symm.surjective.denseRange.comp
      (denseRange_toKummerCompletion K) (kummerZHatContinuousEquiv K Ω).symm.continuous

end ZHat

section ProfiniteCompletion

variable (K : Type*) [Field K] [CharZero K] [FiniteKummerQuotients K]

/-- For `char K = 0` with all `Kˣ/(Kˣ)ⁿ` finite, the Kummer completion is homeomorphic (and
isomorphic as a topological group) to the profinite completion of `Kˣ`. -/
noncomputable def kummerCompletionContinuousEquivProfiniteCompletion :
    KummerCompletion K ≃ₜ* completion (GrpCat.of Kˣ) where
  toMulEquiv := kummerCompletionEquivProfiniteCompletion K
  continuous_toFun := continuous_induced_rng.2 <| continuous_pi fun H =>
    continuous_of_discreteTopology.comp
      ((continuous_apply (indexIdx H)).comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.2 <| continuous_pi fun i =>
    (continuous_bot (f := id)).comp
      ((continuous_apply (powSubgroup i)).comp continuous_subtype_val)

/-- **Kummer theory, profinite form, topologically**: for `K` of characteristic zero with all
`Kˣ/(Kˣ)ⁿ` finite (e.g. a `p`-adic field) and `Ω` a separable closure of `K`,
`H¹_cont(G_K, Ẑ(1)) ≃ₜ* (Kˣ)^∧`, the profinite completion of `Kˣ`. -/
noncomputable def kummerZHatContinuousEquivProfiniteCompletion (Ω : Type*) [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω] :
    ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃ₜ* completion (GrpCat.of Kˣ) :=
  (kummerZHatContinuousEquiv K Ω).trans (kummerCompletionContinuousEquivProfiniteCompletion K)

theorem kummerZHatContinuousEquivProfiniteCompletion_apply (Ω : Type*) [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω] (x : ContH1 Gal(Ω/K) (ZHatOne K Ω)) :
    kummerZHatContinuousEquivProfiniteCompletion K Ω x =
      kummerZHatEquivProfiniteCompletion K Ω x := rfl

end ProfiniteCompletion

end KummerTheory
