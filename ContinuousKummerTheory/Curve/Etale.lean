/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Kummer
import Pi1.Orbifold.Comparison

/-!
# Kummer maps on the étale fundamental group

`pi1` identifies the étale fundamental group `etalePi1 R A Ω` of `[Spec R / A]` (automorphisms of
the fibre functor on `A`-equivariant finite étale `R`-algebras) with the Galois model
`Π_U = H ⧸ ⟨⟨S⟩⟩` (`Pi1.Orbifold.GaloisData.equivPi1`, SGA 1 V.8.2). We transport the actions on
`μ_n(Ω)`, `Ẑ(1)` and the Kummer maps along this isomorphism:

* `Curve.etaleToPi D : etalePi1 D.R D.A Ω →* Π_U`, a continuous isomorphism;
* instances `MulDistribMulAction (etalePi1 D.R D.A Ω) (Mu n Ω)` and `(ZHatOne K Ω)`;
* `Curve.kummerMapEtale D n`, `Curve.kummerMapEtaleZHat D`: `Γ(U, 𝒪^×) → H¹(π₁ᵉᵗ, μ_n / Ẑ(1))`;
* `Curve.kummerMapEtaleZHat_injective`: [AbsTopIII] Prop. 1.6(i) for the étale fundamental group.
-/

universe u

open groupCohomology AffOrbicurve

namespace ContH1

variable {G H M : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction H M]

/-- Pulling back along a surjective homomorphism (identity on coefficients) is injective in
degree one. -/
theorem map_id_injective_of_surjective (φ : H →* G) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) (hcomp : ∀ h (m : M), φ h • m = h • m) :
    Function.Injective (map φ hφ (MonoidHom.id M) continuous_id (fun h m => (hcomp h m))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using induction_on with
  | h c =>
    rw [map_mk, mk_eq_one_iff] at hx
    obtain ⟨m, hm⟩ := hx
    rw [mk_eq_one_iff]
    refine ⟨m, fun g => ?_⟩
    obtain ⟨h, rfl⟩ := hsurj g
    rw [hcomp]
    exact hm h

end ContH1

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω]

/-- The étale fundamental group of `[Spec R / A]` (of `U = Spec R` for `A` trivial). -/
abbrev EtPi : Type u := Pi1.Orbifold.etalePi1 D.R D.A Ω

/-- `π₁ᵉᵗ([Spec R / A]) ≅ Π_U` (`pi1`'s `GaloisData.equivPi1`), as a homomorphism. -/
noncomputable def etaleToPi : EtPi D →* Pi D := D.equivPi1.toMulEquiv.toMonoidHom

theorem continuous_etaleToPi : Continuous (etaleToPi D) := D.equivPi1.continuous

theorem etaleToPi_bijective : Function.Bijective (etaleToPi D) := D.equivPi1.bijective

noncomputable instance instMulDistribMulActionEtaleMu (n : ℕ) [NeZero n] :
    MulDistribMulAction (EtPi D) (Mu n Ω) :=
  MulDistribMulAction.compHom _ (etaleToPi D)

noncomputable instance instMulDistribMulActionEtaleZHatOne (K : Type*) [Field K] :
    MulDistribMulAction (EtPi D) (ZHatOne K Ω) :=
  MulDistribMulAction.compHom _ (etaleToPi D)

/-- Pull-back `H¹(Π_U, M) → H¹(π₁ᵉᵗ, M)`, an isomorphism. -/
noncomputable abbrev toEtaleMu (n : ℕ) [NeZero n] :
    ContH1 (Pi D) (Mu n Ω) →* ContH1 (EtPi D) (Mu n Ω) :=
  ContH1.map (etaleToPi D) (continuous_etaleToPi D) (MonoidHom.id _) continuous_id
    fun _ _ => rfl

/-- Pull-back `H¹(Π_U, Ẑ(1)) → H¹(π₁ᵉᵗ, Ẑ(1))`, an isomorphism. -/
noncomputable abbrev toEtaleZHat (K : Type*) [Field K] :
    ContH1 (Pi D) (ZHatOne K Ω) →* ContH1 (EtPi D) (ZHatOne K Ω) :=
  ContH1.map (etaleToPi D) (continuous_etaleToPi D) (MonoidHom.id _) continuous_id
    fun _ _ => rfl

theorem toEtaleMu_injective (n : ℕ) [NeZero n] : Function.Injective (toEtaleMu D n) :=
  ContH1.map_id_injective_of_surjective _ _ (etaleToPi_bijective D).2 fun _ _ => rfl

theorem toEtaleZHat_injective (K : Type*) [Field K] : Function.Injective (toEtaleZHat D K) :=
  ContH1.map_id_injective_of_surjective _ _ (etaleToPi_bijective D).2 fun _ _ => rfl

variable [IsSepClosed Ω]

/-- **The `μ_n`-valued Kummer map of `U` on the étale fundamental group.** -/
noncomputable def kummerMapEtale (n : ℕ) [NeZero n] : units D →* ContH1 (EtPi D) (Mu n Ω) :=
  (toEtaleMu D n).comp (kummerMap D n)

/-- **The Kummer map `κ_U : Γ(U, 𝒪^×) → H¹(π₁ᵉᵗ(U), Ẑ(1))`.** -/
noncomputable def kummerMapEtaleZHat : units D →* ContH1 (EtPi D) (ZHatOne (F D) Ω) :=
  (toEtaleZHat D (F D)).comp (kummerMapZHat D)

/-- **[AbsTopIII] Proposition 1.6(i) for the étale fundamental group.** -/
theorem kummerMapEtaleZHat_injective
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (hkf : IsKummerFaithfulGm k) : Function.Injective (kummerMapEtaleZHat D) :=
  (toEtaleZHat_injective D (F D)).comp (kummerMapZHat_injective hk hkf)

end Curve

end KummerTheory
