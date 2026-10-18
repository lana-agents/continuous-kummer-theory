/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Point

/-!
# The section `s_x : Gal(κ(A)/k) → Π_U` of a point of `U`

Mochizuki, *Topics in Absolute Anabelian Geometry III*, Proposition 1.6(ii) (`T3` l.1993) and
Proposition 1.8 (l.2061) use the section `s_x : G_k → Π_U` attached to a point `x ∈ U(k)` (well
defined up to conjugation). In `pi1`'s Galois model, for `U = Spec R` (`H_L = H`) and a place `A`
of `Ω` centered on `U`, the decomposition group `D_A ⊆ Gal(Ω/F)` maps to `Π_U`, and the inertia
`ker(D_A → Gal(κ(A)/k))` dies there (`ker_decompositionMap_le_ker_decompToPi`). So, **if**
`D_A → Gal(κ(A)/k)` is surjective (true for rational points; not yet formalised, see
`Plans/MR5Plan.md`, R2b), `D_A → Π_U` descends to a continuous homomorphism
`Curve.sectionMap : Gal(κ(A)/k) → Π_U` (`D_A` is compact: `isClosed_decompositionSubgroup`).

* `Curve.sectionMap_kummerMap`: **`κ_U(u)|_x = κ_k(u(x))`** ([AbsTopIII] Prop. 1.8(ii)) for `s_x`;
* `Curve.forall_sectionMap_kummerMap_eq_one_iff`: for `k` Kummer-faithful for `𝔾_m`, `κ_U(u)|_x`
  is trivial at every level iff `u(x) = 1` (Prop. 1.8(i), "`η†|x₁ = 0`").
-/

universe u

open AffOrbicurve IsLocalRing Pointwise

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] (A : ValuationSubring Ω)

omit [IsGalois (K₀ k t) Ω] in
/-- `x ∈ σ • A ↔ σ⁻¹ x ∈ A`. -/
theorem mem_smul_valuationSubring_iff (σ : Ω ≃ₐ[F D] Ω) (x : Ω) : x ∈ σ • A ↔ σ⁻¹ x ∈ A := by
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [AlgEquiv.smul_def] using hs
  · intro h
    exact ⟨σ⁻¹ x, h, by simp [AlgEquiv.smul_def]⟩

/-- **The decomposition group `D_A` is closed** in `Gal(Ω/F)`: if `σ • A ≠ A`, pick `x` in the
symmetric difference; `{τ | τ⁻¹ x = σ⁻¹ x}` is an open neighbourhood of `σ` missing `D_A`. -/
theorem isClosed_decompositionSubgroup :
    IsClosed ((A.decompositionSubgroup (F D) : Subgroup (Ω ≃ₐ[F D] Ω)) : Set (Ω ≃ₐ[F D] Ω)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  have hne : σ • A ≠ A := hσ
  obtain ⟨x, hx⟩ : ∃ x, ¬(x ∈ σ • A ↔ x ∈ A) := by
    by_contra h
    exact hne (SetLike.ext fun x => not_not.mp fun hx => h ⟨x, hx⟩)
  set y := σ⁻¹ x
  -- `{ρ | ρ x = y}` is open
  have hopen : IsOpen {ρ : Ω ≃ₐ[F D] Ω | ρ x = y} := by
    rw [isOpen_iff_forall_mem_open]
    intro ρ₀ hρ₀
    have hint : IsIntegral (F D) x := Algebra.IsIntegral.isIntegral x
    haveI : FiniteDimensional (F D) (IntermediateField.adjoin (F D) {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    refine ⟨(fun g => ρ₀ * g) '' ((IntermediateField.adjoin (F D) {x}).fixingSubgroup :
      Set (Ω ≃ₐ[F D] Ω)), ?_, (Homeomorph.mulLeft ρ₀).isOpenMap _
      (IntermediateField.fixingSubgroup_isOpen _), ⟨1, one_mem _, mul_one ρ₀⟩⟩
    rintro _ ⟨g, hg, rfl⟩
    have hgx : g x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x
      (IntermediateField.mem_adjoin_simple_self (F D) x)
    change (ρ₀ * g) x = y
    rw [AlgEquiv.mul_apply, hgx]
    exact hρ₀
  refine ⟨Inv.inv ⁻¹' {ρ : Ω ≃ₐ[F D] Ω | ρ x = y}, ?_, continuous_inv.isOpen_preimage _ hopen,
    rfl⟩
  intro τ hτ hτD
  have hτA : τ • A = A := hτD
  apply hx
  have h1 : x ∈ σ • A ↔ y ∈ A := mem_smul_valuationSubring_iff D A σ x
  have h2 : x ∈ τ • A ↔ τ⁻¹ x ∈ A := mem_smul_valuationSubring_iff D A τ x
  rw [hτA] at h2
  have h3 : τ⁻¹ x = y := hτ
  rw [h1, ← h3, ← h2]

instance compactSpace_decompositionSubgroup : CompactSpace (A.decompositionSubgroup (F D)) :=
  isCompact_iff_compactSpace.mp (isClosed_decompositionSubgroup D A).isCompact

variable [CharZero k] [IsSepClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  [Algebra.IsIntegral k (ResidueField A)]
  (hHL : D.HL = D.H) (ht : t ∈ A)
  (hsurj : Function.Surjective (Decomposition.decompositionMap (F D) A hk hkres))

/-- **The section `s_x : Gal(κ(A)/k) → Π_U` of a point** (for `U = Spec R`, `A` centered on `U`,
`D_A → Gal(κ(A)/k)` surjective): the descent of `D_A → Π_U`. -/
noncomputable def sectionMap : (ResidueField A ≃ₐ[k] ResidueField A) →* Pi D :=
  (Decomposition.decompositionMap (F D) A hk hkres).liftOfSurjective hsurj
    ⟨decompToPi D A, ker_decompositionMap_le_ker_decompToPi D A hk hkres hHL ht⟩

omit [CharZero k] [IsSepClosed Ω] [Algebra.IsIntegral k (ResidueField A)] in
theorem sectionMap_decompositionMap (σ : A.decompositionSubgroup (F D)) :
    sectionMap D A hk hkres hHL ht hsurj (Decomposition.decompositionMap (F D) A hk hkres σ) =
      decompToPi D A σ :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ σ

omit [CharZero k] [IsSepClosed Ω] in
theorem continuous_sectionMap : Continuous (sectionMap D A hk hkres hHL ht hsurj) := by
  have hc := Decomposition.continuous_decompositionMap (F D) A hk hkres
  have hq := IsClosedMap.isQuotientMap hc.isClosedMap hc hsurj
  rw [hq.continuous_iff]
  have : (sectionMap D A hk hkres hHL ht hsurj) ∘ (Decomposition.decompositionMap (F D) A hk hkres)
      = decompToPi D A := funext (sectionMap_decompositionMap D A hk hkres hHL ht hsurj)
  rw [this]
  exact continuous_decompToPi D A

variable (n : ℕ) [NeZero n]

omit [IsSepClosed Ω] [Algebra.IsIntegral k (ResidueField A)] in
/-- `s_x` is compatible with the reduction `μ_n(Ω) → μ_n(κ(A))`. -/
theorem reduceMu_sectionMap_smul (g : ResidueField A ≃ₐ[k] ResidueField A) (ζ : Mu n Ω) :
    Decomposition.reduceMu A n (NeZero.ne n) (sectionMap D A hk hkres hHL ht hsurj g • ζ) =
      g • Decomposition.reduceMu A n (NeZero.ne n) ζ := by
  letI := Decomposition.muAction (F D) A hk hkres n
  obtain ⟨σ, rfl⟩ := hsurj g
  rw [sectionMap_decompositionMap]
  exact reduceMu_decompToPi_smul D A hk hkres n σ ζ

variable [HasKummerRoots n k (ResidueField A)]

/-- **`κ_U(u)|_x = κ_k(u(x))`** ([AbsTopIII] Prop. 1.8(ii), with the section `s_x` of a point of
`U`): pulling `κ_U(u)` back along `s_x : Gal(κ(A)/k) → Π_U` (coefficients reduced modulo `𝔪_A`)
gives the Kummer class of the value `u(x) = a`. -/
theorem sectionMap_kummerMap (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    ContH1.map (sectionMap D A hk hkres hHL ht hsurj)
        (continuous_sectionMap D A hk hkres hHL ht hsurj)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_sectionMap_smul D A hk hkres hHL ht hsurj n) (kummerMap D n u) =
      kummer n k (ResidueField A) a := by
  letI := Decomposition.muAction (F D) A hk hkres n
  apply ContH1.map_id_injective_of_surjective (Decomposition.decompositionMap (F D) A hk hkres)
    (Decomposition.continuous_decompositionMap (F D) A hk hkres) hsurj
    (M := Mu n (ResidueField A)) (fun _ _ => rfl)
  rw [← decomposition_kummerMap D A hk hkres n u a hu hu' hua, ContH1.map_map]
  induction kummerMap D n u using ContH1.induction_on with
  | h c =>
    rw [ContH1.map_mk, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp [sectionMap_decompositionMap]

omit [NeZero n] [HasKummerRoots n k (ResidueField A)] in
/-- **Kummer-faithfulness detects `f(x) = 1` along `s_x`** ([AbsTopIII] Prop. 1.8(i)). -/
theorem forall_sectionMap_kummerMap_eq_one_iff [IsGalois k (ResidueField A)]
    (hroots : ∀ (n : ℕ) [NeZero n], HasKummerRoots n k (ResidueField A))
    (hkf : IsKummerFaithfulGm k) (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    (∀ (n : ℕ) [NeZero n],
      ContH1.map (sectionMap D A hk hkres hHL ht hsurj)
          (continuous_sectionMap D A hk hkres hHL ht hsurj)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_sectionMap_smul D A hk hkres hHL ht hsurj n) (kummerMap D n u) = 1) ↔
      a = 1 := by
  constructor
  · intro h
    refine hkf a fun n hn => ?_
    haveI : NeZero n := ⟨hn.ne'⟩
    haveI := hroots n
    have h1 := h n
    rw [sectionMap_kummerMap D A hk hkres hHL ht hsurj n u a hu hu' hua] at h1
    have hker : a ∈ (kummer n k (ResidueField A)).ker := h1
    rw [ker_kummer] at hker
    exact hker
  · rintro rfl n _
    haveI := hroots n
    rw [sectionMap_kummerMap D A hk hkres hHL ht hsurj n u 1 hu hu' hua, map_one]

end Curve

end KummerTheory
