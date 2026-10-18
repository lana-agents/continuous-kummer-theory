/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.ConstantsZHat
import ContinuousKummerTheory.Curve.Residue
import ContinuousKummerTheory.Curve.TameChar

/-!
# The first two maps of [AbsTopIII] Proposition 1.6(iii) form a complex

Mochizuki, *Topics in Absolute Anabelian Geometry III*, Proposition 1.6(iii) (`T3` l.2001–2018):
for `U = X \ S`, restricting classes to the inertia groups `I_x` (`x ∈ S`) gives a sequence
`1 → (kˣ)^∧ → H¹(Π_U, M_X) → ⊕_{x ∈ S} Ẑ`, and `κ_U(f)` maps to the divisor of `f`.

In `pi1`'s Galois model (`Curve/Kummer.lean`) a cusp is a place `W ⊇ k` of `Ω` (cusps of `U`
are the places not centered on `U`), the inertia group is `I_W ∩ H`, and restriction to it is
evaluation at its elements (`ContH1.evalTriv`, `Curve/Residue.lean`). We prove:

* `Curve.piToGk_of_mem_inertia`: inertia elements map to `1` under `Π_U ↠ G_k`;
* `Curve.evalTriv_constMapZHat`: the classes of `(kˣ)^∧` (`constMapZHat`) vanish on every
  inertia group — the composite of the first two maps is trivial;
* `Curve.evalTriv_kummerMap_constUnit`: the same for `κ_U(c)`, `c ∈ kˣ`, at level `n`;
* `Curve.exists_inertia_evalTriv_kummerMap_eq`: for a uniformiser `π` of `W ∩ F` and any
  `ζ ∈ μ_n`, there is `σ ∈ I_W ∩ H` with `κ_U(u)(σ) = ζ^m` for every `u` with `u π^{-m}` a unit at
  `W` (the restriction of `κ_U(u)` to `I_W` "is" `ord_W(u)`);
* `Curve.eq_zero_of_kummerMapZHat_eq_constMapZHat`: if `κ_U(u)` lies in the image of `(kˣ)^∧`,
  then `ord_W(u) = 0` at every place `W ⊇ k`, cusps included.
-/

universe u

open AffOrbicurve IntermediateField

namespace ContH1

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- A class evaluates to `1` at `g = 1`. -/
theorem evalTriv_of_eq_one {g : G} (hg : ∀ m : M, g • m = m) (h1 : g = 1) (x : ContH1 G M) :
    evalTriv g hg x = 1 := by
  induction x using induction_on with
  | h c =>
    rw [evalTriv_mk, h1]
    have h := isMulCocycle₁ c 1 1
    rw [one_mul, one_smul] at h
    exact (mul_eq_left.mp h.symm)

end ContH1

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
  {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W)

include hk hσ in
/-- **Inertia lies in the geometric fundamental group**: an element of `I_W ∩ H` (for a place
`W ⊇ k`) maps to `1` under `Π_U ↠ G_k`, since it fixes the algebraic closure `k̄` of `k`. -/
theorem piToGk_of_mem_inertia : piToGk D (σ : Pi D) = 1 := by
  ext x
  change algebraMap (kbar k Ω) Ω (piToGk D (σ : Pi D) x) = (x : Ω)
  rw [piToGk_mk, algebraMap_hToGk_apply]
  exact inertia_fix_algebraic hk hσ (mem_algebraicClosure_iff.mp x.2)

include hk hσ in
/-- **[AbsTopIII] Prop. 1.6(iii): the classes of `(kˣ)^∧` vanish on the inertia groups.** -/
theorem evalTriv_constMapZHat (x : KummerCompletion k) :
    ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_zHatOne hk hσ (F D)) (constMapZHat D x) = 1 := by
  rw [constMapZHat_apply, ContH1.evalTriv_map _ _ _ _ _ (σ : Pi D) _
    (fun m => by rw [piToGk_of_mem_inertia hk hσ, one_smul]),
    ContH1.evalTriv_of_eq_one _ (piToGk_of_mem_inertia hk hσ), map_one]

include hk hσ in
/-- The level-`n` form for `κ_U(c)`, `c ∈ kˣ`: constants are units at every place `W ⊇ k`. -/
theorem evalTriv_kummerMap_constUnit (n : ℕ) [NeZero n] (c : kˣ) :
    ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_mu hk hσ n) (kummerMap D n (constUnit D c)) =
      1 := by
  have hc : (((constUnit D c : (F D)ˣ) : F D) : Ω) = algebraMap k Ω c := rfl
  have h := evalTriv_kummerMap hk hσ n (constUnit D c) 1 0 (by simpa [hc] using hk c)
    (by simpa [hc] using hk (c⁻¹ : kˣ))
  rw [h, zpow_zero]

include hk in
/-- **Cusp inertia records orders** ([AbsTopIII] Prop. 1.4(i), 1.6(iii) at level `n`): for a
uniformiser `π` of `W ∩ F` and `ζ ∈ μ_n` there is `σ ∈ I_W ∩ H` such that `κ_U(u)(σ) = ζ^m` for
every `u ∈ Γ(U, 𝒪^×)` and `m` with `u π^{-m}` a unit at `W` (i.e. `m = ord_W(u)`). -/
theorem exists_inertia_evalTriv_kummerMap_eq (π : (F D)ˣ)
    (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω))
    (n : ℕ) [NeZero n] (ζ : Mu n Ω) :
    ∃ σ : D.H, ∃ hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W,
      ∀ (v : units D) (m : ℤ),
        ((((v : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) : Ω) ∈ W →
        (((((v : (F D)ˣ) * π ^ (-m))⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W →
        ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_mu hk hσ n) (kummerMap D n v) = ζ ^ m := by
  obtain ⟨σ, hσ, hζ⟩ := evalTriv_kummer_surjective (D := D) hk π hπW hπ n ζ
  exact ⟨σ, hσ, fun v m hv hv' => by rw [evalTriv_kummerMap hk hσ n v π m hv hv', hζ]⟩

omit [IsAlgClosed Ω] in
include hk hσ in
/-- The `μ_n`-component of the evaluation of a `Ẑ(1)`-class at an inertia element. -/
theorem proj_evalTriv_zHat (n : ℕ) [NeZero n] (X : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    ZHatOne.proj (⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩ : KummerIndex (F D))
        (ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_zHatOne hk hσ (F D)) X) =
      ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_mu hk hσ n)
        (ContH1.map (MonoidHom.id (Pi D)) continuous_id
          (ZHatOne.proj (⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩ : KummerIndex (F D)))
          (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x) X) :=
  (ContH1.evalTriv_map (MonoidHom.id (Pi D)) continuous_id
    (ZHatOne.proj (⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩ : KummerIndex (F D)))
    (ZHatOne.continuous_proj _) (fun g x => proj_pi_smul _ g x) (σ : Pi D)
    (pi_inertia_smul_mu hk hσ n) (pi_inertia_smul_zHatOne hk hσ (F D)) X).symm

include hk in
/-- **[AbsTopIII] Prop. 1.6(iii): a function whose Kummer class is constant has order `0` at
every place.** If `κ_U(u)` lies in the image of `(kˣ)^∧ → H¹(Π_U, Ẑ(1))`, then for every place
`W ⊇ k` of `Ω` (in particular every cusp) with uniformiser `π` of `W ∩ F`, and every `m` with
`u π^{-m}` a unit at `W`, we have `m = 0`. -/
theorem eq_zero_of_kummerMapZHat_eq_constMapZHat (u : units D) (x : KummerCompletion k)
    (hux : kummerMapZHat D u = constMapZHat D x) (π : (F D)ˣ)
    (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω)) (m : ℤ)
    (hv : ((((u : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) : Ω) ∈ W)
    (hv' : (((((u : (F D)ˣ) * π ^ (-m))⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) : m = 0 := by
  -- `(n : ℤ) ∣ m` for every `n ≥ 1`
  have hdvd : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ m := by
    intro n hn
    haveI : NeZero n := ⟨hn.ne'⟩
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
    obtain ⟨σ, hσ, hev⟩ := exists_inertia_evalTriv_kummerMap_eq hk π hπW hπ n
      (hζ.toRootsOfUnity : Mu n Ω)
    have h1 := hev u m hv hv'
    set i : KummerIndex (F D) := ⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
    have h2 := proj_evalTriv_zHat hk hσ n (kummerMapZHat D u)
    rw [map_proj_kummerMapZHat i u, h1, hux, evalTriv_constMapZHat hk hσ, map_one] at h2
    have hord : orderOf (hζ.toRootsOfUnity : rootsOfUnity n Ω) = n := by
      rw [← Subgroup.orderOf_coe, ← orderOf_units, hζ.val_toRootsOfUnity_coe, ← hζ.eq_orderOf]
    have h2' : (hζ.toRootsOfUnity : rootsOfUnity n Ω) ^ m = 1 := h2.symm
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2'
  have h := Int.natAbs_dvd_natAbs.mpr (hdvd (m.natAbs + 1) (Nat.succ_pos _))
  rw [Int.natAbs_natCast] at h
  by_contra hm0
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) h
  omega

end Curve

end KummerTheory
