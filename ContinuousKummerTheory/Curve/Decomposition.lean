/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Kummer
import ContinuousKummerTheory.Kummer.Decomposition

/-!
# Kummer classes of functions on a curve, restricted to decomposition groups of points

[AbsTopIII] Proposition 1.8 uses, for a point `x` of `U` and a class `η ∈ H¹(Π_U, M_X)`, the
restriction `η|_x = s_x^*(η)` along the (outer) homomorphism `s_x : G_{k_x} → Π_U` determined by
`x`, and the fact that for the Kummer class of a function `f` this restriction is the Kummer class
of the value `f(x)`. Here we prove this on the decomposition group of a valuation subring
`A ⊆ Ω` (a place of `Ω` above `x`): the restriction of `κ_U(u)` along `D_A → Gal(Ω/F) ≅ H → Π_U`,
with coefficients reduced modulo `𝔪_A`, is the inflation along `D_A ↠ Gal(κ(A)/k)` of the Kummer
class `κ_k(a)` of the residue `a = u(x)` (`Curve.decomposition_kummerMap`). This combines the
function-field statement `KummerTheory.Decomposition.decomposition_kummer` with
`Curve.inflation_kummerMap`.

* `Curve.galFEquiv D : H ≃ₜ* Gal(Ω / F)` (continuous bijection from a compact group to a
  Hausdorff one) and `Curve.ofGalF D` its inverse as a homomorphism.
* `Curve.decompToPi D A : D_A →* Π_U`.
-/

universe u

open groupCohomology AffOrbicurve IntermediateField IsLocalRing

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]

omit [IsGalois (K₀ k t) Ω] in
theorem toGalF_injective : Function.Injective (toGalF D) := by
  intro a b h
  apply Subtype.ext
  ext x
  exact DFunLike.congr_fun h x

/-- `H ≃ₜ* Gal(Ω / F)`. -/
noncomputable def galFEquiv : D.H ≃ₜ* (Ω ≃ₐ[F D] Ω) :=
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  { MulEquiv.ofBijective (toGalF D) ⟨toGalF_injective D, toGalF_surjective⟩ with
    continuous_toFun := continuous_toGalF
    continuous_invFun := continuous_toGalF.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective (toGalF D) ⟨toGalF_injective D, toGalF_surjective⟩).toEquiv) }

/-- The inverse `Gal(Ω / F) → H` of `toGalF`. -/
noncomputable def ofGalF : (Ω ≃ₐ[F D] Ω) →* D.H := (galFEquiv D).symm.toMonoidHom

theorem continuous_ofGalF : Continuous (ofGalF D) := (galFEquiv D).symm.continuous

@[simp]
theorem toGalF_ofGalF (τ : Ω ≃ₐ[F D] Ω) : toGalF D (ofGalF D τ) = τ :=
  (galFEquiv D).apply_symm_apply τ

theorem ofGalF_apply (τ : Ω ≃ₐ[F D] Ω) (x : Ω) : ((ofGalF D τ : D.H) : Ω ≃ₐ[K₀ k t] Ω) x = τ x :=
  DFunLike.congr_fun (toGalF_ofGalF D τ) x

instance isScalarTower_F : IsScalarTower k (F D) Ω :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (A : ValuationSubring Ω)

/-- The decomposition group `D_A ⊆ Gal(Ω / F)` of a place `A` of `Ω`, mapped to `Π_U`. -/
noncomputable def decompToPi : A.decompositionSubgroup (F D) →* Pi D :=
  (QuotientGroup.mk' _).comp ((ofGalF D).comp (A.decompositionSubgroup (F D)).subtype)

theorem continuous_decompToPi : Continuous (decompToPi D A) :=
  QuotientGroup.continuous_mk.comp ((continuous_ofGalF D).comp continuous_subtype_val)

variable [CharZero k] [IsSepClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  (n : ℕ) [NeZero n]

omit [IsSepClosed Ω] in
theorem reduceMu_decompToPi_smul (σ : A.decompositionSubgroup (F D)) (ζ : Mu n Ω) :
    letI := Decomposition.muAction (F D) A hk hkres n
    Decomposition.reduceMu A n (NeZero.ne n) (decompToPi D A σ • ζ) =
      σ • Decomposition.reduceMu A n (NeZero.ne n) ζ := by
  letI := Decomposition.muAction (F D) A hk hkres n
  rw [← Decomposition.reduceMu_smul (F D) A hk hkres n (NeZero.ne n) σ ζ]
  congr 1
  apply Mu.ext
  apply Units.ext
  exact ofGalF_apply D σ.1 _

variable [Algebra.IsIntegral k (ResidueField A)] [HasKummerRoots n k (ResidueField A)]

/-- **The restriction of `κ_U(u)` to the decomposition group of a point is the Kummer class of the
value** ([AbsTopIII] Prop. 1.8: `κ_U(f)|_x = κ(f(x))`). Let `A ⊆ Ω` be a valuation subring
containing `k`, `u ∈ Γ(U, 𝒪^×)` a unit at `A` with residue the constant `a ∈ kˣ`. Then the
pull-back of `κ_U(u) ∈ H¹(Π_U, μ_n)` along `D_A → Π_U`, with coefficients reduced modulo `𝔪_A`,
is the inflation of `κ_k(a)` along `D_A ↠ Gal(κ(A) / k)`. -/
theorem decomposition_kummerMap (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) =
      ContH1.map (Decomposition.decompositionMap (F D) A hk hkres)
        (Decomposition.continuous_decompositionMap (F D) A hk hkres)
        (MonoidHom.id _) continuous_id (fun _ _ => rfl) (kummer n k (ResidueField A) a) := by
  letI := Decomposition.muAction (F D) A hk hkres n
  rw [← Decomposition.decomposition_kummer (F D) A hk hkres n (NeZero.ne n) (u : (F D)ˣ) a hu hu'
    hua]
  have h := inflation_kummerMap n u
  -- pull back the inflation identity along `D_A → Gal(Ω/F) → H`
  have key := congrArg (ContH1.map ((ofGalF D).comp (A.decompositionSubgroup (F D)).subtype)
    ((continuous_ofGalF D).comp continuous_subtype_val)
    (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
    (fun σ ζ => by
      rw [← Decomposition.reduceMu_smul (F D) A hk hkres n (NeZero.ne n) σ ζ]
      congr 1
      apply Mu.ext
      apply Units.ext
      exact ofGalF_apply D σ.1 _)) h
  convert key using 1
  · induction kummerMap D n u using ContH1.induction_on with
    | h c => rfl
  · induction kummer n (F D) Ω (u : (F D)ˣ) using ContH1.induction_on with
    | h c =>
      simp only [resMu, res, ContH1.map_mk]
      congr 1
      apply Subtype.ext
      funext σ
      simp only [ContH1.cocyclesMap_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, toGalF_ofGalF, MonoidHom.id_apply]

/-- The same for a place `A` centered on `U` (`k ⊆ A`, `t ∈ A`): every `u ∈ Γ(U, 𝒪^×)` is then a
unit at `A`. -/
theorem decomposition_kummerMap_of_isCentered (ht : t ∈ A) (u : units D) (a : kˣ)
    (hua : residue A ⟨_, (units_mem ⟨hk, ht⟩ u.2).1⟩ = algebraMap k (ResidueField A) a) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) =
      ContH1.map (Decomposition.decompositionMap (F D) A hk hkres)
        (Decomposition.continuous_decompositionMap (F D) A hk hkres)
        (MonoidHom.id _) continuous_id (fun _ _ => rfl) (kummer n k (ResidueField A) a) :=
  decomposition_kummerMap D A hk hkres n u a _ (units_mem ⟨hk, ht⟩ u.2).2 hua

end Curve

end KummerTheory
