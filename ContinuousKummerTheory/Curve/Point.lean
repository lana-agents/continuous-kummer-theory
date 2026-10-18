/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Decomposition

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
  is trivial at every level `n` iff `u(x) = 1`.
-/

universe u

open AffOrbicurve IsLocalRing

namespace KummerTheory

namespace Curve

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

end Curve

end KummerTheory
