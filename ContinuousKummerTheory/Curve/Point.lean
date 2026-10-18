/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Decomposition
import ContinuousKummerTheory.Curve.Etale

/-!
# Restriction of Kummer classes to the section of a point

Mochizuki, *Topics in Absolute Anabelian Geometry III*, Proposition 1.8 (`T3` l.2061–2106) uses,
for a point `x ∈ U(k)` with section `s_x : G_k → Π_U`, the classes
`η|_x := s_x^*(η) ∈ H¹(G_k, M_X)` and the identity `κ_U(f)|_x = κ_k(f(x))` (Prop 1.8(ii)), and
reads off whether `f(x) = 1` from `η|_x`: this is where Kummer-faithfulness of `k` enters
("`η†|x₁ = 0`" in Prop 1.8(i)).

In `pi1`'s Galois model a point is a place `A ⊆ Ω` containing `k`; its decomposition group
`D_A ⊆ Gal(Ω/F)` maps to `Π_U` (`Curve.decompToPi`) and onto (a subgroup of)
`Gal(κ(A)/k)` (`Decomposition.decompositionMap`). Here the section `s : Gal(κ(A)/k) → D_A` of
`decompositionMap` is an **argument** (a continuous group-theoretic section; its existence for
rational points is the surjectivity of `D_A → Gal(κ(A)/k)` plus a profinite section, see
`Plans/MR5Plan.md`, step R2). We prove:

* `Curve.section_kummerMap`: `s^* (κ_U(u)|_{D_A}) = κ_k(u(x))` in `H¹(Gal(κ(A)/k), μ_n)`;
* `Curve.section_kummerMap_eq_one_iff`: this class is trivial iff `u(x)` is an `n`-th power in
  `k`;
* `Curve.forall_section_kummerMap_eq_one_iff`: if `k` is Kummer-faithful for `𝔾_m`, the class
  is trivial at every level `n` iff `u(x) = 1`;
* `Curve.decomposition_kummerMap_eq_one_iff`, `Curve.forall_decomposition_kummerMap_eq_one_iff`:
  the same for the restriction of `κ_U(u)` to `D_A` itself, when `D_A → Gal(κ(A)/k)` is
  surjective (no section needed: inflation along a surjection is injective);
* `Curve.ker_decompositionMap_le_ker_decompToPi`: for `U = Spec R` (`H_L = H`) and a place
  `A` centered on `U` (`t ∈ A`), `D_A → Π_U` kills the inertia `ker(D_A → Gal(κ(A)/k))`, so it
  factors through the image of `D_A` in `Gal(κ(A)/k)` (the section `s_x` of [AbsTopIII]
  Prop. 1.6(ii) once `D_A → Gal(κ(A)/k)` is known to be surjective).
-/

universe u

open AffOrbicurve IsLocalRing

namespace KummerTheory

namespace Curve

section Section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]
  (A : ValuationSubring Ω) [CharZero k] [IsSepClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  (s : (ResidueField A ≃ₐ[k] ResidueField A) →* A.decompositionSubgroup (F D))
  (hs : Continuous s)
  (hsec : ∀ g, Decomposition.decompositionMap (F D) A hk hkres (s g) = g)

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω] in
include hsec in
/-- The compatibility of the section `s` with the actions on `μ_n(κ(A))`. -/
theorem section_smul (n : ℕ) [NeZero n] (g : ResidueField A ≃ₐ[k] ResidueField A)
    (ζ : Mu n (ResidueField A)) :
    letI := Decomposition.muAction (F D) A hk hkres n
    (MonoidHom.id _) (s g • ζ) = g • ζ := by
  letI := Decomposition.muAction (F D) A hk hkres n
  change Decomposition.decompositionMap (F D) A hk hkres (s g) • ζ = g • ζ
  rw [hsec]

variable (n : ℕ) [NeZero n] [Algebra.IsIntegral k (ResidueField A)]
  [HasKummerRoots n k (ResidueField A)]

/-- **`κ_U(f)|_x = κ_k(f(x))`** ([AbsTopIII] Prop. 1.8(ii)): for a place `A ⊇ k` with a continuous
section `s` of `D_A → Gal(κ(A)/k)` and a unit `u` of `U` at `A` with residue `a ∈ kˣ`, the
pull-back of `κ_U(u)` along `Gal(κ(A)/k) → D_A → Π_U` is the Kummer class `κ_k(a)`. -/
theorem section_kummerMap (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map s hs (MonoidHom.id _) continuous_id (section_smul D A hk hkres s hsec n)
        (ContH1.map (decompToPi D A) (continuous_decompToPi D A)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u)) =
      kummer n k (ResidueField A) a := by
  letI := Decomposition.muAction (F D) A hk hkres n
  rw [decomposition_kummerMap D A hk hkres n u a hu hu' hua, ContH1.map_map]
  induction kummer n k (ResidueField A) a using ContH1.induction_on with
  | h c =>
    rw [ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext g
    simp [hsec]

/-- **`η|_x` detects `n`-th powers**: the restriction of `κ_U(u)` to the section of `x` is trivial
iff `u(x)` is an `n`-th power in `k`. -/
theorem section_kummerMap_eq_one_iff [IsGalois k (ResidueField A)] (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map s hs (MonoidHom.id _) continuous_id (section_smul D A hk hkres s hsec n)
        (ContH1.map (decompToPi D A) (continuous_decompToPi D A)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u)) = 1 ↔
      ∃ b : kˣ, b ^ n = a := by
  rw [section_kummerMap D A hk hkres s hs hsec n u a hu hu' hua, ← MonoidHom.mem_ker,
    ker_kummer, MonoidHom.mem_range]
  rfl

omit [NeZero n] [HasKummerRoots n k (ResidueField A)] in
/-- **Kummer-faithfulness detects `f(x) = 1`** ([AbsTopIII] Def. 1.5 as used in Prop. 1.8(i):
"`η†|x₁ = 0`"): if `k` is Kummer-faithful for `𝔾_m` and `κ(A)` contains all roots of elements of
`k`, the restrictions of `κ_U(u)` to the section of `x` are trivial at every level `n ≥ 1` iff
`u(x) = 1`. -/
theorem forall_section_kummerMap_eq_one_iff [IsGalois k (ResidueField A)]
    (hroots : ∀ (n : ℕ) [NeZero n], HasKummerRoots n k (ResidueField A))
    (hkf : IsKummerFaithfulGm k) (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    (∀ (n : ℕ) [NeZero n],
      letI := Decomposition.muAction (F D) A hk hkres n
      letI := hroots n
      ContH1.map s hs (MonoidHom.id _) continuous_id (section_smul D A hk hkres s hsec n)
          (ContH1.map (decompToPi D A) (continuous_decompToPi D A)
            (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
            (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u)) = 1) ↔ a = 1 := by
  constructor
  · intro h
    refine hkf a fun n hn => ?_
    haveI : NeZero n := ⟨hn.ne'⟩
    haveI := hroots n
    exact (section_kummerMap_eq_one_iff D A hk hkres s hs hsec n u a hu hu' hua).mp (h n)
  · rintro rfl n _
    haveI := hroots n
    exact (section_kummerMap_eq_one_iff D A hk hkres s hs hsec n u 1 hu hu' hua).mpr
      ⟨1, one_pow n⟩

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω] [Algebra.IsIntegral k (ResidueField A)]
  [NeZero n] [HasKummerRoots n k (ResidueField A)] in
include hsec in
/-- Under the section `s`, the reduction `D_A → Gal(κ(A)/k)` is surjective. -/
theorem decompositionMap_surjective_of_section :
    Function.Surjective (Decomposition.decompositionMap (F D) A hk hkres) :=
  fun g => ⟨s g, hsec g⟩

end Section

section Restriction

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω]
  (A : ValuationSubring Ω) [CharZero k] [IsSepClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)
  (hsurj : Function.Surjective (Decomposition.decompositionMap (F D) A hk hkres))
  (n : ℕ) [NeZero n] [Algebra.IsIntegral k (ResidueField A)]
  [HasKummerRoots n k (ResidueField A)]

include hsurj in
/-- **`κ_U(u)|_{D_A}` detects `n`-th powers**: if `D_A → Gal(κ(A)/k)` is surjective (e.g. for a
`k`-rational point), the restriction of `κ_U(u)` to the decomposition group of `A` is trivial iff
the value `u(x)` is an `n`-th power in `k`. -/
theorem decomposition_kummerMap_eq_one_iff [IsGalois k (ResidueField A)] (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) = 1 ↔
      ∃ b : kˣ, b ^ n = a := by
  letI := Decomposition.muAction (F D) A hk hkres n
  rw [decomposition_kummerMap D A hk hkres n u a hu hu' hua]
  have hinj := ContH1.map_id_injective_of_surjective
    (Decomposition.decompositionMap (F D) A hk hkres)
    (Decomposition.continuous_decompositionMap (F D) A hk hkres) hsurj
    (M := Mu n (ResidueField A)) (fun _ _ => rfl)
  constructor
  · intro h
    have h1 : kummer n k (ResidueField A) a = 1 := hinj (h.trans (map_one _).symm)
    have hker : a ∈ (kummer n k (ResidueField A)).ker := h1
    rw [ker_kummer] at hker
    exact hker
  · rintro ⟨b, rfl⟩
    have hker : b ^ n ∈ (kummer n k (ResidueField A)).ker := by
      rw [ker_kummer]
      exact ⟨b, rfl⟩
    rw [MonoidHom.mem_ker.mp hker, map_one]

omit [NeZero n] [HasKummerRoots n k (ResidueField A)] in
include hsurj in
/-- **Kummer-faithfulness detects `f(x) = 1` on decomposition groups** ([AbsTopIII] Prop. 1.8(i),
"`η†|x₁ = 0`"): if `k` is Kummer-faithful for `𝔾_m` and `D_A → Gal(κ(A)/k)` is surjective, the
restrictions of `κ_U(u)` to `D_A` are trivial at every level iff `u(x) = 1`. -/
theorem forall_decomposition_kummerMap_eq_one_iff [IsGalois k (ResidueField A)]
    (hroots : ∀ (n : ℕ) [NeZero n], HasKummerRoots n k (ResidueField A))
    (hkf : IsKummerFaithfulGm k) (u : units D) (a : kˣ)
    (hu : (((u : (F D)ˣ) : F D) : Ω) ∈ A) (hu' : ((((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) : Ω) ∈ A)
    (hua : residue A ⟨_, hu⟩ = algebraMap k (ResidueField A) a) :
    (∀ (n : ℕ) [NeZero n],
      letI := Decomposition.muAction (F D) A hk hkres n
      ContH1.map (decompToPi D A) (continuous_decompToPi D A)
          (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
          (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) = 1) ↔ a = 1 := by
  constructor
  · intro h
    refine hkf a fun n hn => ?_
    haveI : NeZero n := ⟨hn.ne'⟩
    haveI := hroots n
    exact (decomposition_kummerMap_eq_one_iff D A hk hkres hsurj n u a hu hu' hua).mp (h n)
  · rintro rfl n _
    haveI := hroots n
    exact (decomposition_kummerMap_eq_one_iff D A hk hkres hsurj n u 1 hu hu' hua).mpr
      ⟨1, one_pow n⟩

omit [CharZero k] [IsSepClosed Ω] [Algebra.IsIntegral k (ResidueField A)] [NeZero n]
  [HasKummerRoots n k (ResidueField A)] in
/-- **Inertia at a point of `U` dies in `Π_U`** ([AbsTopIII] Prop. 1.4(i): the inertia groups of
points of `U` are trivial in `Π_U`). For `U = Spec R` (`H_L = H`) and a place `A ⊇ k` centered on
`U` (`t ∈ A`), every `σ ∈ D_A` acting trivially on `κ(A)` maps to `1` in `Π_U`: it lies in the
inertia group of `A`, hence in `S`. -/
theorem ker_decompositionMap_le_ker_decompToPi (hHL : D.HL = D.H) (ht : t ∈ A) :
    (Decomposition.decompositionMap (F D) A hk hkres).ker ≤ (decompToPi D A).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  have hin : ((ofGalF D σ.1 : D.H) : Ω ≃ₐ[K₀ k t] Ω) ∈ D.S := by
    refine ⟨by rw [hHL]; exact (ofGalF D σ.1).2, A, hk, ht, fun a ha => ?_⟩
    have h1 := Decomposition.decompositionMap_residue (F D) A hk hkres σ ⟨a, ha⟩
    rw [hσ, AlgEquiv.one_apply] at h1
    have hm : (σ • (⟨a, ha⟩ : A) : A) - ⟨a, ha⟩ ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, map_sub, ← h1, sub_self]
    have hv := (A.valuation_lt_one_iff _).mp hm
    rw [ofGalF_apply]
    convert hv using 2
    rw [AddSubgroupClass.coe_sub]
    rfl
  rw [MonoidHom.mem_ker]
  refine (QuotientGroup.eq_one_iff (ofGalF D σ.1)).mpr ?_
  rw [GaloisPi1.kernel, Subgroup.mem_subgroupOf]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_closure ⟨1, D.H.one_mem, _, hin, by simp⟩)

end Restriction

end Curve


end KummerTheory
