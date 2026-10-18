/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.PointSection
import ContinuousKummerTheory.Kummer.DecompositionSurjective

/-!
# The section of a rational point

Mochizuki, *Topics in Absolute Anabelian Geometry III*, Proposition 1.6(ii) (`T3` l.1993:
"For `x ∈ X(k)`, write `s_x : G_k → Π_X` for the associated section") and Proposition 1.8
(l.2061). In `pi1`'s Galois model a point of the curve is a place `A ⊆ Ω` containing `k`; it is
`k`-rational when the residue field of `A ∩ F` is `k` (`hrat`: every element of `F` integral at
`A` has residue in `k`). For such `A` the decomposition map `D_A → Gal(κ(A)/k)` is surjective
(`Decomposition.decompositionMap_surjective`), which discharges the hypothesis `hsurj` of
`Curve/Point.lean` and `Curve/PointSection.lean`:

* `Curve.decompositionMap_surjective_of_rational`;
* `Curve.ratSectionMap`: the section `s_x : Gal(κ(A)/k) → Π_U` of a rational point of `U`,
  continuous (`continuous_ratSectionMap`);
* `Curve.ratSectionMap_kummerMap`: **`s_x^* κ_U(u) = κ_k(u(x))`** ([AbsTopIII] Prop. 1.8(ii));
* `Curve.forall_ratSectionMap_kummerMap_eq_one_iff`: for `k` Kummer-faithful for `𝔾_m`,
  `κ_U(u)|_x` is trivial at every level iff `u(x) = 1` (Prop. 1.8(i));
* `Curve.forall_decomposition_kummerMap_eq_one_iff_of_rational`: the same on `D_A`;
* `Curve.exists_residue_eq_of_rational`: the value `u(x) ∈ kˣ` of a unit at a rational point.
-/

universe u

open AffOrbicurve IsLocalRing

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] (A : ValuationSubring Ω)
  [CharZero k] [IsSepClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]
  (hrat : ∀ (a : F D) (ha : (a : Ω) ∈ A),
    ∃ c : k, residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c)

include hrat in
/-- **The decomposition group of a rational point surjects onto `Gal(κ(A)/k)`.** -/
theorem decompositionMap_surjective_of_rational :
    Function.Surjective (Decomposition.decompositionMap (F D) A hk hkres) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  exact Decomposition.decompositionMap_surjective (F := F D) A hk hkres hrat

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω] [Algebra.IsIntegral k (ResidueField A)] in
include hrat in
/-- The value `u(x) ∈ kˣ` of a function `u` which is a unit at a rational point. -/
theorem exists_residue_eq_of_rational (u : (F D)ˣ) (hu : (((u : F D)) : Ω) ∈ A)
    (hu' : ((((u⁻¹ : (F D)ˣ) : F D)) : Ω) ∈ A) :
    ∃ a : kˣ, residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a := by
  obtain ⟨c, hc⟩ := hrat _ hu
  obtain ⟨c', hc'⟩ := hrat _ hu'
  have hmul : c * c' = 1 := by
    apply (algebraMap k (ResidueField A)).injective
    rw [map_mul, ← hc, ← hc', ← map_mul, map_one]
    have : (⟨_, hu⟩ : A) * ⟨_, hu'⟩ = 1 := by
      apply Subtype.ext
      change ((u : F D) : Ω) * (((u⁻¹ : (F D)ˣ) : F D) : Ω) = 1
      rw [← IntermediateField.coe_mul, Units.mul_inv, IntermediateField.coe_one]
    rw [this, map_one]
  exact ⟨⟨c, c', hmul, by rw [mul_comm, hmul]⟩, hc⟩

variable (hHL : D.HL = D.H) (ht : t ∈ A)

/-- **The section `s_x : Gal(κ(A)/k) → Π_U` of a `k`-rational point of `U = Spec R`.** -/
noncomputable def ratSectionMap : (ResidueField A ≃ₐ[k] ResidueField A) →* Pi D :=
  sectionMap D A hk hkres hHL ht (decompositionMap_surjective_of_rational D A hk hkres hrat)

theorem ratSectionMap_decompositionMap (σ : A.decompositionSubgroup (F D)) :
    ratSectionMap D A hk hkres hrat hHL ht (Decomposition.decompositionMap (F D) A hk hkres σ) =
      decompToPi D A σ :=
  sectionMap_decompositionMap D A hk hkres hHL ht _ σ

theorem continuous_ratSectionMap : Continuous (ratSectionMap D A hk hkres hrat hHL ht) :=
  continuous_sectionMap D A hk hkres hHL ht _

variable (n : ℕ) [NeZero n] [HasKummerRoots n k (ResidueField A)]

/-- **`κ_U(u)|_x = κ_k(u(x))`** ([AbsTopIII] Prop. 1.8(ii)) along the section of a rational point:
pulling `κ_U(u)` back along `s_x` (coefficients reduced modulo `𝔪_A`) gives the Kummer class
of the value `u(x) = a`. -/
theorem ratSectionMap_kummerMap (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    ContH1.map (ratSectionMap D A hk hkres hrat hHL ht)
        (continuous_ratSectionMap D A hk hkres hrat hHL ht)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_sectionMap_smul D A hk hkres hHL ht _ n) (kummerMap D n u) =
      kummer n k (ResidueField A) a :=
  sectionMap_kummerMap D A hk hkres hHL ht _ n u a hu hu' hua

omit [NeZero n] [HasKummerRoots n k (ResidueField A)] in
/-- **Kummer-faithfulness detects `f(x) = 1` along the section of a rational point**
([AbsTopIII] Prop. 1.8(i), "`η†|x₁ = 0`"). -/
theorem forall_ratSectionMap_kummerMap_eq_one_iff [IsGalois k (ResidueField A)]
    (hroots : ∀ (n : ℕ) [NeZero n], HasKummerRoots n k (ResidueField A))
    (hkf : IsKummerFaithfulGm k) (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    (∀ (n : ℕ) [NeZero n],
      ContH1.map (ratSectionMap D A hk hkres hrat hHL ht)
          (continuous_ratSectionMap D A hk hkres hrat hHL ht)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_sectionMap_smul D A hk hkres hHL ht _ n) (kummerMap D n u) = 1) ↔
      a = 1 :=
  forall_sectionMap_kummerMap_eq_one_iff D A hk hkres hHL ht _ hroots hkf u a hu hu' hua

omit [NeZero n] [HasKummerRoots n k (ResidueField A)] hHL ht in
include hrat in
/-- **Kummer-faithfulness detects `f(x) = 1` on the decomposition group of a rational point**
([AbsTopIII] Prop. 1.8(i)), with no surjectivity hypothesis. -/
theorem forall_decomposition_kummerMap_eq_one_iff_of_rational [IsGalois k (ResidueField A)]
    (hroots : ∀ (n : ℕ) [NeZero n], HasKummerRoots n k (ResidueField A))
    (hkf : IsKummerFaithfulGm k) (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    (∀ (n : ℕ) [NeZero n],
      letI := Decomposition.muAction (F D) A hk hkres n
      ContH1.map (decompToPi D A) (continuous_decompToPi D A)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) = 1) ↔ a = 1 :=
  forall_decomposition_kummerMap_eq_one_iff D A hk hkres
    (decompositionMap_surjective_of_rational D A hk hkres hrat) hroots hkf u a hu hu' hua

end Curve

end KummerTheory
