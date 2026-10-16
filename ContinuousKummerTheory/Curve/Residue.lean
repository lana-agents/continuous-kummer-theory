/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Kummer

/-!
# Restriction of Kummer classes to inertia groups at cusps

[AbsTopIII] Proposition 1.6(iii): for `U = X ∖ S`, restricting cohomology classes of `Π_U` to the
inertia groups `I_x` (`x ∈ S`) gives a map `H¹(Π_U, M_X) → ∏_{x ∈ S} Hom(I_x, M_X)`, and on Kummer
classes of functions this map records the divisor of the function. We prove the local statement
behind this: the inertia group of any place `W ⊇ k` of `Ω` acts trivially on roots of unity, so a
class can be evaluated at its elements (`ContH1.evalTriv`), and

  `κ_U(u)(σ) = θ_π(σ) ^ m`   for `σ ∈ I_W ∩ H`, whenever `u π^{-m}` is a unit at `W`,

where `θ_π(σ) = κ_F(π)(σ)` is the Kummer character of `π ∈ Fˣ` on `I_W` (the tame character, for
`π` a uniformiser at `W ∩ F`; then `m = ord_W(u)`). Units at `W` have trivial Kummer characters on
`I_W` (the Kummer extensions they generate are unramified at `W`).

## Main results

* `ContH1.evalTriv g hg : H¹_cont(G, M) →* M`: evaluation at an element `g` acting trivially on `M`
  (well defined, coboundaries vanish at `g`).
* `Curve.evalTriv_res_kummer_of_unit`, `Curve.evalTriv_res_kummer_eq_zpow`: the function-field
  statements, for any place `W ⊇ k`.
* `Curve.evalTriv_kummerMap`, `Curve.evalTriv_kummerMapZHat`: the statements for
  `κ_U : Γ(U, 𝒪^×) → H¹(Π_U, μ_n)` and `H¹(Π_U, Ẑ(1))`, evaluated at the image of `σ` in `Π_U`.
-/

universe u

open groupCohomology AffOrbicurve IntermediateField

namespace ContH1

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- **Evaluation at an element acting trivially**: for `g ∈ G` fixing `M` pointwise, `c ↦ c g` is
well defined on `H¹_cont(G, M)` (principal cocycles vanish at `g`), and a homomorphism. -/
def evalTriv (g : G) (hg : ∀ m : M, g • m = m) : ContH1 G M →* M :=
  QuotientGroup.lift _ ((Pi.evalMonoidHom (fun _ : G => M) g).comp (cocycles G M).subtype)
    (by
      rintro c ⟨m, hm⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, Pi.evalMonoidHom_apply,
        ← hm g, hg, div_self'])

@[simp]
theorem evalTriv_mk (g : G) (hg : ∀ m : M, g • m = m) (c : cocycles G M) :
    evalTriv g hg (mk c) = c g := rfl

theorem evalTriv_map {H N : Type*} [Group H] [TopologicalSpace H] [CommGroup N]
    [TopologicalSpace N] [IsTopologicalGroup N] [MulDistribMulAction H N]
    (φ : H →* G) (hφ : Continuous φ) (f : M →* N) (hf : Continuous f)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) (h : H) (hh : ∀ n : N, h • n = n)
    (hφh : ∀ m : M, φ h • m = m) (x : ContH1 G M) :
    evalTriv h hh (map φ hφ f hf hcomp x) = f (evalTriv (φ h) hφh x) := by
  induction x using induction_on with
  | h c => rfl

end ContH1

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]
  {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)

omit [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] in
include hk in
/-- Elements of the inertia group of a place `W ⊇ k` fix all roots of unity. -/
theorem inertia_fix_root_of_unity {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) {ζ : Ω}
    {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have hζW : ζ ∈ W := mem_of_pow_mem hn (by rw [hζ]; exact W.one_mem)
  have hζW' : ζ⁻¹ ∈ W := mem_of_pow_mem hn (by rw [inv_pow, hζ, inv_one]; exact W.one_mem)
  have hpow : (σ ζ / ζ) ^ n = 1 := by rw [div_pow, ← map_pow, hζ, map_one, one_div_one]
  refine eq_of_mem_inertia (k := k) hk hσ hζW (valuation_eq_one_of_mem hζW hζW' hζ0) hn hpow ?_
  field_simp

omit [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] in
include hk in
theorem inertia_smul_mu {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (n : ℕ)
    [NeZero n] (ζ : Mu n Ω) : σ • ζ = ζ := by
  apply Mu.ext
  apply Units.ext
  exact inertia_fix_root_of_unity hk hσ (Nat.pos_of_ne_zero (NeZero.ne n))
    (by rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one])

omit [IsGalois (K₀ k t) Ω] [IsSepClosed Ω] in
include hk in
theorem inertia_smul_zHatOne {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W)
    (K : Type*) [Field K] (x : ZHatOne K Ω) : σ • x = x :=
  Subtype.ext (funext fun i => inertia_smul_mu hk hσ i.n _)

omit [IsSepClosed Ω] in
include hk in
theorem pi_inertia_smul_mu {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (n : ℕ)
    [NeZero n] (ζ : Mu n Ω) : (σ : Pi D) • ζ = ζ :=
  inertia_smul_mu hk hσ n ζ

omit [IsSepClosed Ω] in
include hk in
theorem pi_inertia_smul_zHatOne {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W)
    (K : Type*) [Field K] (x : ZHatOne K Ω) : (σ : Pi D) • x = x :=
  inertia_smul_zHatOne hk hσ K x

variable {σ : D.H} (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W) (n : ℕ) [NeZero n]

include hk in
/-- **Units at `W` have trivial Kummer characters on the inertia group of `W`.** -/
theorem evalTriv_res_kummer_of_unit (ε : (F D)ˣ) (hε : ((ε : F D) : Ω) ∈ W)
    (hε' : (((ε⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) :
    ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω ε)) = 1 := by
  set α := kummerRoot n (F D) Ω ε
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hα : ((α : Ω)) ^ n = ((ε : F D) : Ω) := by
    have := congrArg (fun x : Ωˣ => (x : Ω)) (kummerRoot_pow n (F D) Ω ε)
    simpa using this
  have hαW : (α : Ω) ∈ W := mem_of_pow_mem hn (hα ▸ hε)
  have hαW' : (α : Ω)⁻¹ ∈ W := by
    refine mem_of_pow_mem hn ?_
    rw [inv_pow, hα]
    convert hε' using 1
    simp
  have hpow : ((σ : Ω ≃ₐ[K₀ k t] Ω) α / α) ^ n = 1 := by
    rw [div_pow, ← map_pow, hα, fixes_of_mem_F σ.2, div_self]
    exact fun h => ε.ne_zero (Subtype.ext (by simp at h))
  have hfix : (σ : Ω ≃ₐ[K₀ k t] Ω) α = α :=
    eq_of_mem_inertia (k := k) hk hσ hαW (valuation_eq_one_of_mem hαW hαW' α.ne_zero) hn hpow
      (by field_simp)
  change kummerFun α (smul_pow_of_pow_eq (kummerRoot_pow n (F D) Ω ε)) (toGalF D σ) = 1
  apply Mu.ext
  apply Units.ext
  simp only [val_kummerFun, Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe, toGalF_apply]
  simp [hfix, α.ne_zero]

include hk in
/-- **Kummer characters on inertia record valuations** ([AbsTopIII] Prop. 1.6(iii), restriction
to `I_x`): if `u π^{-m}` is a unit at `W`, the Kummer character of `u` on `I_W` is the `m`-th power
of that of `π`. -/
theorem evalTriv_res_kummer_eq_zpow (v π : (F D)ˣ) (m : ℤ)
    (hv : (((v * π ^ (-m) : (F D)ˣ) : F D) : Ω) ∈ W)
    (hv' : ((((v * π ^ (-m))⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) :
    ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω v)) =
      ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π)) ^ m := by
  have h1 := evalTriv_res_kummer_of_unit hk hσ n _ hv hv'
  have hdecomp : v = (v * π ^ (-m)) * π ^ m := by
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  conv_lhs => rw [hdecomp]
  rw [map_mul, map_zpow, map_mul, map_zpow, map_mul, map_zpow, h1, one_mul]

include hk in
/-- The inertia statement for `κ_U(u) ∈ H¹(Π_U, μ_n)`, evaluated at the image of `σ` in `Π_U`. -/
theorem evalTriv_kummerMap (v : units D) (π : (F D)ˣ) (m : ℤ)
    (hv : ((((v : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) : Ω) ∈ W)
    (hv' : (((((v : (F D)ˣ) * π ^ (-m))⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) :
    ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_mu hk hσ n) (kummerMap D n v) =
      ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π)) ^ m := by
  rw [← evalTriv_res_kummer_eq_zpow hk hσ n _ π m hv hv', ← inflation_kummerMap n v]
  exact (ContH1.evalTriv_map (QuotientGroup.mk' _) QuotientGroup.continuous_mk (MonoidHom.id _)
    continuous_id (fun _ _ => rfl) σ (inertia_smul_mu hk hσ n) (pi_inertia_smul_mu hk hσ n)
    (kummerMap D n v)).symm

omit [NeZero n] in
include hk in
/-- The `Ẑ(1)`-valued inertia statement for the Kummer classes of the function field. -/
theorem evalTriv_resZHat_kummerZHat_eq_zpow (v π : (F D)ˣ) (m : ℤ)
    (hv : (((v * π ^ (-m) : (F D)ˣ) : F D) : Ω) ∈ W)
    (hv' : ((((v * π ^ (-m))⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) :
    ContH1.evalTriv σ (inertia_smul_zHatOne hk hσ (F D))
        (resZHat D (F D) (kummerZHat (F D) Ω v)) =
      ContH1.evalTriv σ (inertia_smul_zHatOne hk hσ (F D))
        (resZHat D (F D) (kummerZHat (F D) Ω π)) ^ m := by
  apply Subtype.ext
  funext i
  have hproj : ∀ w : (F D)ˣ, ((ContH1.evalTriv σ (inertia_smul_zHatOne hk hσ (F D))
      (resZHat D (F D) (kummerZHat (F D) Ω w)) : ZHatOne (F D) Ω) : ∀ i, Mu i.n Ω) i =
      ContH1.evalTriv σ (inertia_smul_mu hk hσ i.n) (resMu D i.n (kummer i.n (F D) Ω w)) := by
    intro w
    rw [← map_proj_res_kummerZHat i w, ContH1.evalTriv_map]
    rfl
  have hpow : ∀ (x : ZHatOne (F D) Ω) (m : ℤ), ((x ^ m : ZHatOne (F D) Ω) : ∀ i, Mu i.n Ω) i =
      ((x : ∀ i, Mu i.n Ω) i) ^ m := fun x m => rfl
  rw [hpow, hproj, hproj]
  exact evalTriv_res_kummer_eq_zpow hk hσ i.n v π m hv hv'

omit [NeZero n] in
include hk in
/-- The inertia statement for `κ_U(u) ∈ H¹(Π_U, Ẑ(1))`. -/
theorem evalTriv_kummerMapZHat (v : units D) (π : (F D)ˣ) (m : ℤ)
    (hv : ((((v : (F D)ˣ) * π ^ (-m) : (F D)ˣ) : F D) : Ω) ∈ W)
    (hv' : (((((v : (F D)ˣ) * π ^ (-m))⁻¹ : (F D)ˣ) : F D) : Ω) ∈ W) :
    ContH1.evalTriv (σ : Pi D) (pi_inertia_smul_zHatOne hk hσ (F D)) (kummerMapZHat D v) =
      ContH1.evalTriv σ (inertia_smul_zHatOne hk hσ (F D))
        (resZHat D (F D) (kummerZHat (F D) Ω π)) ^ m := by
  rw [← evalTriv_resZHat_kummerZHat_eq_zpow hk hσ _ π m hv hv', ← inflation_kummerMapZHat v]
  exact (ContH1.evalTriv_map (QuotientGroup.mk' _) QuotientGroup.continuous_mk (MonoidHom.id _)
    continuous_id (fun _ _ => rfl) σ (inertia_smul_zHatOne hk hσ (F D))
    (pi_inertia_smul_zHatOne hk hσ (F D)) (kummerMapZHat D v)).symm

end Curve

end KummerTheory
