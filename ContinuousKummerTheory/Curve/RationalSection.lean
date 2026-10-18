/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.RationalPoint
import ContinuousKummerTheory.Curve.Constants

/-!
# The section of a rational point is a section of `Π_U ↠ G_k`

Mochizuki, *Topics in Absolute Anabelian Geometry III*, Proposition 1.6(ii) (`T3` l.1993): "For
`x ∈ X(k)`, write `s_x : G_k → Π_X` for the associated section [well-defined up to conjugation by
`Δ_X`]". In `pi1`'s Galois model, a `k`-rational point of `U` is a place `A ⊆ Ω` (`hrat`), and
`Curve.ratSectionMap : Gal(κ(A)/k) → Π_U` is its section (`Curve/RationalPoint.lean`). Here we
identify `Gal(κ(A)/k)` with `G_k = Gal(k̄/k)` and show that `s_x` is a section of the arithmetic
quotient `Curve.piToGk : Π_U → G_k`:

* `Curve.kbarResidue`: reduction `k̄ → κ(A)` of the constants (`k̄ ⊆ A`), an isomorphism of
  `k`-algebras `Curve.kbarEquiv : k̄ ≃ₐ[k] κ(A)` (`κ(A)` is algebraic over `k`, `k̄` is
  algebraically closed);
* `Curve.kbarResidue_piToGk_decompToPi`: `D_A → Π_U → G_k` and `D_A → Gal(κ(A)/k)` agree;
* `Curve.piToGk_ratSectionMap`: **`piToGk ∘ s_x = id`** under `G_k ≅ Gal(κ(A)/k)`;
* `Curve.ratSectionMap_injective`.
-/

universe u

open AffOrbicurve IsLocalRing Polynomial

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] (A : ValuationSubring Ω)
  [CharZero k] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

omit [IsGalois (K₀ k t) Ω] [CharZero k] [Algebra k (ResidueField A)] in
include hk in
theorem kbar_mem (x : kbar k Ω) : (x : Ω) ∈ A :=
  mem_of_isIntegral hk (mem_algebraicClosure_iff.mp x.2).isIntegral

/-- Reduction of the constants: `k̄ → κ(A)`. -/
noncomputable def kbarResidue : kbar k Ω →+* ResidueField A :=
  (residue A).comp ((algebraMap (kbar k Ω) Ω).codRestrict A.toSubring (kbar_mem A hk))

omit [IsGalois (K₀ k t) Ω] [CharZero k] [Algebra k (ResidueField A)] in
theorem kbarResidue_apply (x : kbar k Ω) :
    kbarResidue A hk x = residue A ⟨(x : Ω), kbar_mem A hk x⟩ := rfl

omit [IsGalois (K₀ k t) Ω] [CharZero k] in
include hkres in
theorem kbarResidue_algebraMap (c : k) :
    kbarResidue A hk (algebraMap k (kbar k Ω) c) = algebraMap k (ResidueField A) c :=
  hkres c

omit [IsGalois (K₀ k t) Ω] [CharZero k] in
include hkres in
/-- `k̄ → κ(A)` is surjective when `κ(A)` is algebraic over `k`: a root in `κ(A)` of a
polynomial over `k` is the reduction of one of its roots in the algebraically closed `k̄`. -/
theorem kbarResidue_surjective [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)] :
    Function.Surjective (kbarResidue A hk) := by
  intro y
  obtain ⟨g, hmonic, hg⟩ := Algebra.IsIntegral.isIntegral (R := k) y
  set gk := g.map (algebraMap k (kbar k Ω))
  have hprod : gk = (gk.roots.map (X - C ·)).prod := by
    have := (IsAlgClosed.splits gk).eq_prod_roots
    rwa [(hmonic.map _).leadingCoeff, C_1, one_mul] at this
  have hmap : g.map (algebraMap k (ResidueField A)) = gk.map (kbarResidue A hk) := by
    rw [map_map]
    congr 1
    exact RingHom.ext fun c => (kbarResidue_algebraMap A hk hkres c).symm
  have h0 : (gk.roots.map fun r => y - kbarResidue A hk r).prod = 0 := by
    have := congrArg (eval y) hmap
    rw [eval_map, hg, hprod, Polynomial.map_multiset_prod, eval_multiset_prod,
      Multiset.map_map, Multiset.map_map] at this
    rw [this]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h0)
  exact ⟨r, (sub_eq_zero.mp hr).symm⟩

/-- **`G_k ≅ Gal(κ(A)/k)`**: the constants `k̄` reduce isomorphically onto `κ(A)`. -/
noncomputable def kbarEquiv [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)] :
    kbar k Ω ≃ₐ[k] ResidueField A :=
  AlgEquiv.ofBijective
    { kbarResidue A hk with commutes' := kbarResidue_algebraMap A hk hkres }
    ⟨(kbarResidue A hk).injective, kbarResidue_surjective A hk hkres⟩

omit [IsGalois (K₀ k t) Ω] [CharZero k] in
theorem kbarEquiv_apply [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
    (x : kbar k Ω) :
    kbarEquiv A hk hkres x = kbarResidue A hk x := rfl

/-- **`D_A → Π_U → G_k` is `D_A → Gal(κ(A)/k)`** on the constants. -/
theorem kbarResidue_piToGk_decompToPi [IsAlgClosed Ω] (σ : A.decompositionSubgroup (F D))
    (y : kbar k Ω) :
    kbarResidue A hk (piToGk D (decompToPi D A σ) y) =
      Decomposition.decompositionMap (F D) A hk hkres σ (kbarResidue A hk y) := by
  rw [kbarResidue_apply, kbarResidue_apply, Decomposition.decompositionMap_residue]
  congr 1
  apply Subtype.ext
  change algebraMap (kbar k Ω) Ω (hToGk D (ofGalF D σ.1) y) = σ.1 (y : Ω)
  rw [algebraMap_hToGk_apply, ofGalF_apply]

variable [IsAlgClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
  (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)
  (hHL : D.HL = D.H) (ht : t ∈ A)

/-- **The section of a rational point is a section of `Π_U ↠ G_k`** ([AbsTopIII] Prop. 1.6(ii),
"the associated section"): `piToGk (s_x g)` is `g` transported to `G_k` along
`k̄ ≅ κ(A)`. -/
theorem piToGk_ratSectionMap (g : ResidueField A ≃ₐ[k] ResidueField A) :
    piToGk D (ratSectionMap D A hk hkres hrat hHL ht g) =
      (kbarEquiv A hk hkres).trans (g.trans (kbarEquiv A hk hkres).symm) := by
  obtain ⟨σ, rfl⟩ := decompositionMap_surjective_of_rational D A hk hkres hrat g
  rw [ratSectionMap_decompositionMap]
  refine AlgEquiv.ext fun y => ?_
  apply (kbarEquiv A hk hkres).injective
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, kbarEquiv_apply,
    kbarEquiv_apply, kbarResidue_piToGk_decompToPi]

/-- `s_x` is injective (it is a section). -/
theorem ratSectionMap_injective :
    Function.Injective (ratSectionMap D A hk hkres hrat hHL ht) := by
  intro g g' h
  have h' := congrArg (piToGk D) h
  rw [piToGk_ratSectionMap, piToGk_ratSectionMap] at h'
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (kbarEquiv A hk hkres).surjective y
  have := congrArg (fun e : kbar k Ω ≃ₐ[k] kbar k Ω => kbarEquiv A hk hkres (e x)) h'
  simpa using this

end Curve

end KummerTheory
