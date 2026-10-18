/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Decomposition
import ContinuousKummerTheory.Kummer.ClosedPoint

/-!
# `κ_U(f)|_x` at closed points over finite extensions `k_x`

[AbsTopIII] Prop. 1.8 (`T3` l.2061–2098) restricts classes `η ∈ H¹(Π_U, M_X)` to NF-points
`x ∈ U(k_x)`, `k_x / k` finite: `η|_x = s_x^*(η) ∈ H¹(G_{k_x}, M_X)`. In `pi1`'s Galois model a
closed point of `U = Spec R` (`H_L = H`) is a place `A ⊇ k` of `Ω` with `t ∈ A`; its residue field
is `k_x = Decomposition.pointField (F D) A`, and `D_A → Π_U` factors through
`D_A ↠ Gal(κ(A)/k_x) = G_{k_x}` (`Decomposition.range_decompositionMap`; the inertia dies in
`Π_U`, `ker_decompositionMap_le_ker_decompToPi`). As inflation is injective on `H¹`, `η|_x`
vanishes iff the restriction of `η` along `decompToPi : D_A → Π_U` does; we work with the latter.

* `KummerTheory.Curve.decompToPi_kummerMap`: the restriction of `κ_U(u)` along `D_A → Π_U` is
  the restriction of `κ_F(u)` to `D_A ⊆ Gal(Ω/F)`;
* `KummerTheory.Curve.decompToPi_kummerMap_eq_one_iff`: it vanishes at level `n` iff `u(x)` is an
  `n`-th power in `k_x` (no rationality assumption on `x`);
* `KummerTheory.Curve.forall_decompToPi_kummerMap_eq_one_iff`: for `k` torally Kummer-faithful
  and `[k_x : k] < ∞`, it vanishes at all levels iff `u(x) = 1` ([AbsTopIII] Prop. 1.8(i),
  `η†|x = 0`).
-/

universe u

open IsLocalRing AffOrbicurve

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [IsGalois (K₀ k t) Ω] (A : ValuationSubring Ω)
  [CharZero k] [IsSepClosed Ω] (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

section Level

variable (n : ℕ) [NeZero n]

/-- **The restriction of `κ_U(u)` along `D_A → Π_U` is the restriction of `κ_F(u)` to `D_A`**
(coefficients reduced modulo `𝔪_A`). -/
theorem decompToPi_kummerMap (u : units D) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) =
      ContH1.map (A.decompositionSubgroup (F D)).subtype continuous_subtype_val
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (Decomposition.reduceMu_smul (F D) A hk hkres n (NeZero.ne n))
        (kummer n (F D) Ω (u : (F D)ˣ)) := by
  letI := Decomposition.muAction (F D) A hk hkres n
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

omit [IsGalois (K₀ k t) Ω] [CharZero k] [IsSepClosed Ω] [Algebra k (ResidueField A)] in
include hk in
/-- Units of `U` are units at places centred on `U`. -/
theorem units_val_mem (u : units D) (ht : t ∈ A) :
    algebraMap (F D) Ω ((u : (F D)ˣ) : F D) ∈ A ∧
      algebraMap (F D) Ω (((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) ∈ A :=
  units_mem ⟨hk, ht⟩ u.2

/-- **`κ_U(u)|_x` at a closed point vanishes at level `n` iff `u(x) ∈ (k_xˣ)ⁿ`**: for a place
`A ⊇ k` of `Ω` and a unit `u` of `U` at `A`, the restriction of `κ_U(u)` along `D_A → Π_U` is
trivial iff `u(x) = ū` is the `n`-th power of an element of `κ(A)` fixed by `D_A` (an element
of `k_x`, `Decomposition.mem_pointField_iff`). -/
theorem decompToPi_kummerMap_eq_one_iff (u : units D)
    (hu : algebraMap (F D) Ω ((u : (F D)ˣ) : F D) ∈ A)
    (hu' : algebraMap (F D) Ω (((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) ∈ A) :
    letI := Decomposition.muAction (F D) A hk hkres n
    ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) = 1 ↔
      ∃ b : ResidueField A, (∀ σ, Decomposition.decompositionMap (F D) A hk hkres σ b = b) ∧
        b ^ n = residue A ⟨_, hu⟩ := by
  rw [decompToPi_kummerMap]
  exact Decomposition.decomposition_kummer_eq_one_iff (F D) A hk hkres n (NeZero.ne n) _ hu hu'

end Level

/-- **[AbsTopIII] Prop. 1.8(i), `η†|x = 0`, at a closed point over a finite extension `k_x`**:
for `k` torally Kummer-faithful, `Ω` algebraically closed and a place `A ⊇ k` with `κ(A)`
algebraic over `k` and `[k_x : k] < ∞`, the restrictions of `κ_U(u)` along `D_A → Π_U` vanish at
every level iff `u(x) = 1`. -/
theorem forall_decompToPi_kummerMap_eq_one_iff [IsAlgClosed Ω]
    [Algebra.IsIntegral k (ResidueField A)] [IsGalois k (ResidueField A)]
    (htf : IsTorallyKummerFaithful k)
    [FiniteDimensional k (Decomposition.pointField (F D) A hk hkres)] (u : units D)
    (hu : algebraMap (F D) Ω ((u : (F D)ˣ) : F D) ∈ A)
    (hu' : algebraMap (F D) Ω (((u : (F D)ˣ)⁻¹ : (F D)ˣ) : F D) ∈ A) :
    (∀ (n : ℕ) [NeZero n],
      letI := Decomposition.muAction (F D) A hk hkres n
      ContH1.map (decompToPi D A) (continuous_decompToPi D A)
        (Decomposition.reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_decompToPi_smul D A hk hkres n) (kummerMap D n u) = 1) ↔
      residue A ⟨_, hu⟩ = 1 := by
  have key := Decomposition.forall_decomposition_kummer_eq_one_iff (F D) A hk hkres
    (fun n _ => inferInstance) (Decomposition.pointField (F D) A hk hkres)
    (fun y hy => (Decomposition.mem_pointField_iff (F D) A hk hkres y).2 hy)
    (Decomposition.isKummerFaithfulGm_pointField (F := F D) A hk hkres htf) (u : (F D)ˣ) hu hu'
  rw [← key]
  refine forall_congr' fun n => ?_
  refine forall_congr' fun _ => ?_
  rw [decompToPi_kummerMap]

end Curve

end KummerTheory
