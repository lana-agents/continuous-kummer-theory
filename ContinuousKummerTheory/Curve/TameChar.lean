/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Residue
import Pi1.Orbicurve.SubfieldGalois

/-!
# The tame character of a uniformiser generates

[AbsTopIII] Proposition 1.4(i): the inertia group `I_x` of a cusp `x` is naturally isomorphic to
`Ẑ(1)`. At level `n` this is the statement that the Kummer character of a uniformiser `π` at `x`,
`σ ↦ σ(π^{1/n}) / π^{1/n}`, maps the inertia group of a place `W` of `Ω` above `x` onto `μ_n`.

* `Curve.le_ramificationIdx_of_eq_pow`: if a uniformiser `p` of `u_W(L)` is an `n`-th power in the
  coordinate ring of `M ⊇ L`, then `e(u_W(M) | u_W(L)) ≥ n`.
* `Curve.exists_mem_inertia_eq_mul` (and `..._of_uniformizer`): for `W` centered on the `t`-line,
  every `ζ ∈ μ_n` is `σ(α)/α` for some `σ ∈ I_W` fixing `L`. Proof: in the Galois closure `N` of
  `L(α)`, `|I(N/L)| = e(N/L) = e(L(α)/L) · |I(N/L(α))| ≥ n · |I(N/L(α))|` (`pi1`'s
  `ramificationIdx_mul_card`), the Kummer character `I(N/L) → μ_n(N)` has kernel inside
  `I(N/L(α))`, hence it is onto `μ_n`; then lift along `pi1`'s surjectivity of inertia.
* `Curve.exists_inertia_tameChar`, `Curve.evalTriv_kummer_surjective`: for every place `W ⊇ k` of
  `Ω` (cusps included: there `W` is centered on the `t⁻¹`-line), and `π ∈ F` a uniformiser of
  `W ∩ F`, the tame character `κ_F(π)|_{I_W ∩ H}` maps onto `μ_n`.
-/

universe u

open groupCohomology AffOrbicurve IntermediateField IntermediateField.algebraAdjoinAdjoin Ideal

namespace KummerTheory

namespace Curve

section Ramification

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
  (ht : Transcendental k t) {W : ValuationSubring Ω} (hW : IsCentered k t W)

set_option maxHeartbeats 1000000 in
-- instance search on coordinate rings of nested intermediate fields is slow
include ht in
/-- **A uniformiser that is an `n`-th power upstairs forces ramification `≥ n`**: if `p` is a
uniformiser of the center `u_W(L)` (`p ∈ u_W(L) ∖ u_W(L)²`) and `p = aⁿ` in the coordinate ring of
`M ⊇ L` with `a ∈ u_W(M)`, then `e(u_W(M) | u_W(L)) ≥ n`. -/
theorem le_ramificationIdx_of_eq_pow {L M : IntermediateField (K₀ k t) Ω} (hLM : L ≤ M)
    [FiniteDimensional (K₀ k t) M] (p : coordRing k t L) (hp : p ∈ centerIdeal hW L)
    (hp2 : p ∉ centerIdeal hW L ^ 2) (a : coordRing k t M) (ha : a ∈ centerIdeal hW M) (n : ℕ)
    (hpa : ringMap t hLM p = a ^ n) :
    n ≤ (letI := algRing t hLM; (centerIdeal hW M).ramificationIdx (coordRing k t L)) := by
  letI iR := algRing t hLM
  letI : SMul (coordRing k t L) (coordRing k t M) := iR.toSMul
  letI : Module (coordRing k t L) (coordRing k t M) := iR.toModule
  haveI : FiniteDimensional (K₀ k t) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLM).toLinearMap
      (IntermediateField.inclusion hLM).injective
  haveI := isDedekindDomain_ring t ht L
  haveI := isDedekindDomain_ring t ht M
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hp2 (Ideal.zero_mem _)
  have hq0 : centerIdeal hW L ≠ ⊥ := fun h => hp0 (by simpa [h] using hp)
  have hP0 : centerIdeal hW M ≠ ⊥ := centerIdeal_ne_bot_of_le hW hLM hq0
  haveI hPmax := isMaximal_centerIdeal ht hW M hP0
  haveI hqmax := isMaximal_centerIdeal ht hW L hq0
  haveI : (centerIdeal hW M).LiesOver (centerIdeal hW L) :=
    ⟨(comap_centerIdeal hW hLM).symm⟩
  haveI : FaithfulSMul (coordRing k t L) (coordRing k t M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ringMap_injective t hLM)
  haveI : Module.IsTorsionFree (coordRing k t L) (coordRing k t M) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (ringMap_injective t hLM)
  rw [← ramificationIdx'_eq_ramificationIdx (centerIdeal hW L) (centerIdeal hW M) hq0]
  have hirrq : Irreducible (centerIdeal hW L) :=
    (Ideal.prime_of_isPrime hq0 hqmax.isPrime).irreducible
  have hirrP : Irreducible (centerIdeal hW M) :=
    (Ideal.prime_of_isPrime hP0 hPmax.isPrime).irreducible
  have hspan0 : Ideal.span {p} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hmult := IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hspan0 hirrq hirrP hP0
  have hq1 : emultiplicity (centerIdeal hW L) (Ideal.span {p}) = 1 := by
    rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, emultiplicity_eq_coe]
    refine ⟨?_, ?_⟩
    · rw [pow_one, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hp
    · rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hp2
  have hPn : centerIdeal hW M ^ n ∣ (Ideal.span {p}).map (algebraMap _ _) := by
    rw [Ideal.map_span, Set.image_singleton]
    change _ ∣ Ideal.span {ringMap t hLM p}
    rw [hpa, ← Ideal.span_singleton_pow]
    apply pow_dvd_pow_of_dvd
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact ha
  have hle := le_emultiplicity_of_pow_dvd hPn
  rw [hmult, hq1, mul_one] at hle
  exact_mod_cast hle

end Ramification

section Core

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
  (ht : Transcendental k t) {W : ValuationSubring Ω} (hW : IsCentered k t W)
  [IsGalois (K₀ k t) Ω]

include hW in
/-- Elements of the inertia group of `u_W(N)` in `Gal(N / L)` fix the roots of unity of `N`
(they lift to elements of the inertia group of `W`). -/
theorem fix_root_of_unity_of_mem_inertia_fixSub (ht : Transcendental k t)
    {L N : IntermediateField (K₀ k t) Ω} (hLN : L ≤ N) [FiniteDimensional (K₀ k t) N]
    [IsGalois (K₀ k t) N] (hN : centerIdeal hW N ≠ ⊥) {ρ : N ≃ₐ[K₀ k t] N}
    (hρ : ρ ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N L) {ζ : N} {n : ℕ}
    (hn : 0 < n) (hζ : ζ ^ n = 1) : ρ ζ = ζ := by
  obtain ⟨σ, hσ, -, rfl⟩ := exists_mem_inertia_fixingSubgroup_restrictNormal_eq ht hW hLN hN ρ hρ
  apply Subtype.val_injective
  rw [coe_restrictNormal_apply]
  exact inertia_fix_root_of_unity (t := t) hW.1 hσ hn (by
    rw [← IntermediateField.coe_pow, hζ]; rfl)

set_option maxHeartbeats 2000000 in
-- instance search on coordinate rings of nested intermediate fields is slow
include ht in
/-- **The tame character of a uniformiser maps inertia onto `μ_n`** (centered model): let `W` be a
place of `Ω` centered on the `t`-line, `L` finite over `k(t)`, `p` a uniformiser of the center
`u_W(L)` of `W` on the coordinate ring of `L` (`p ∈ u_W(L) ∖ u_W(L)²`), and `α` an `n`-th root of
`p`. Then every `n`-th root of unity `ζ` is `σ(α) / α` for some `σ` in the inertia group of `W`
fixing `L`. -/
theorem exists_mem_inertia_eq_mul (L : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) L] (p : coordRing k t L) (hp : p ∈ centerIdeal hW L)
    (hp2 : p ∉ centerIdeal hW L ^ 2) {n : ℕ} (hn : 0 < n) {α : Ω}
    (hα : α ^ n = toΩ t L p) {ζ : Ω} (hζ : ζ ^ n = 1) :
    ∃ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, σ ∈ L.fixingSubgroup ∧ σ α = ζ * α := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hp2 (Ideal.zero_mem _)
  have hpΩ : toΩ t L p ≠ 0 := fun h => hp0 (toΩ_injective L (by rw [h, map_zero]))
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact hpΩ hα.symm
  have hαint : IsIntegral (K₀ k t) α := Algebra.IsIntegral.isIntegral α
  -- the fields `M = L(α)` and `N` (its Galois closure)
  set M : IntermediateField (K₀ k t) Ω := L ⊔ IntermediateField.adjoin (K₀ k t) {α}
  haveI : FiniteDimensional (K₀ k t) (IntermediateField.adjoin (K₀ k t) {α}) :=
    IntermediateField.adjoin.finiteDimensional hαint
  haveI : FiniteDimensional (K₀ k t) M := IntermediateField.finiteDimensional_sup _ _
  set N : IntermediateField (K₀ k t) Ω := normalClosure (K₀ k t) M Ω
  haveI : FiniteDimensional (K₀ k t) N := normalClosure.is_finiteDimensional _ _ _
  haveI : IsGalois (K₀ k t) N := ⟨⟩
  have hLM : L ≤ M := le_sup_left
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  have hLN : L ≤ N := hLM.trans hMN
  have hαM : α ∈ M := (le_sup_right : IntermediateField.adjoin (K₀ k t) {α} ≤ M)
    (IntermediateField.mem_adjoin_simple_self (K₀ k t) α)
  have hαN : α ∈ N := hMN hαM
  -- `α` in the coordinate ring of `M`, in the center
  have hαintA : IsIntegral (A₀ k t) (⟨α, hαM⟩ : M) := by
    refine IsIntegral.of_pow hn ?_
    have : (⟨α, hαM⟩ : M) ^ n = (IntermediateField.inclusion hLM) (p : L) := by
      apply Subtype.ext; simp [hα]
    rw [this]
    exact (p.2 : IsIntegral (A₀ k t) (p : L)).map
      ((IntermediateField.inclusion hLM).restrictScalars (A₀ k t))
  set aM : coordRing k t M := ⟨⟨α, hαM⟩, hαintA⟩
  have hpa : ringMap t hLM p = aM ^ n := by
    apply Subtype.ext; apply Subtype.ext
    change ((p : L) : Ω) = α ^ n
    rw [hα]; rfl
  have hvp : W.valuation (toΩ t L p) < 1 := (mem_centerIdeal hW).mp hp
  have hva : aM ∈ centerIdeal hW M := by
    rw [mem_centerIdeal]
    change W.valuation α < 1
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ W.valuation α ^ n := one_le_pow₀ h
    rw [← map_pow, hα] at this
    exact absurd hvp (not_lt.mpr this)
  have he := le_ramificationIdx_of_eq_pow ht hW hLM p hp hp2 aM hva n hpa
  -- the inertia groups
  have hq0 : centerIdeal hW L ≠ ⊥ := fun h => hp0 (by simpa [h] using hp)
  have hN0 : centerIdeal hW N ≠ ⊥ := centerIdeal_ne_bot_of_le hW hLN hq0
  haveI hNmax := isMaximal_centerIdeal ht hW N hN0
  set IL := (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N L
  set IM := (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N M
  have hcount := ramificationIdx_mul_card t ht hLM hMN (centerIdeal hW N)
  rw [comap_centerIdeal hW hMN] at hcount
  -- `n · |G_M| ≤ |G_L|`
  have hineq : n * Nat.card IM ≤ Nat.card IL := by
    rw [← hcount]
    exact Nat.mul_le_mul_right _ he
  -- the Kummer character `χ : G_L → μ_n(N)`
  set αN : N := ⟨α, hαN⟩
  have hαN0 : αN ≠ 0 := fun h => hα0 (congrArg Subtype.val h)
  have hfixp : ∀ ρ ∈ IL, ρ (αN ^ n) = αN ^ n := by
    intro ρ hρ
    have hpL : (αN ^ n : N) = ⟨toΩ t L p, hLN (p : L).2⟩ := Subtype.ext (by
      change α ^ n = _; exact hα)
    rw [hpL]
    exact (mem_fixSub t).mp hρ.2 _ (p : L).2
  have hχpow : ∀ ρ ∈ IL, (ρ αN / αN) ^ n = 1 := by
    intro ρ hρ
    rw [div_pow, ← map_pow, hfixp ρ hρ, div_self (pow_ne_zero _ hαN0)]
  let χfun : IL → rootsOfUnity n N := fun ρ =>
    ⟨Units.mk0 (ρ.1 αN / αN) (div_ne_zero ((map_ne_zero _).mpr hαN0) hαN0), by
      rw [mem_rootsOfUnity]; ext; simp [hχpow ρ.1 ρ.2]⟩
  have hχval : ∀ ρ : IL, ((χfun ρ : Nˣ) : N) = ρ.1 αN / αN := fun _ => rfl
  let χ : IL →* rootsOfUnity n N :=
    { toFun := χfun
      map_one' := by
        apply Subtype.ext; apply Units.ext
        rw [hχval]
        simp [div_self hαN0]
      map_mul' := fun ρ τ => by
        apply Subtype.ext; apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [hχval, hχval, hχval]
        have hfix := fix_root_of_unity_of_mem_inertia_fixSub hW ht hLN hN0 ρ.2 hn
          (hχpow τ.1 τ.2)
        have h1 : τ.1 αN = (τ.1 αN / αN) * αN := by field_simp
        change ρ.1 (τ.1 αN) / αN = _
        rw [h1, map_mul, hfix]
        field_simp }
  -- the kernel of `χ` lies in `G_M`
  have hker : ∀ ρ : IL, χ ρ = 1 → ρ.1 ∈ IM := by
    intro ρ hρ
    have hρα : ρ.1 αN = αN := by
      have := congrArg (fun z : rootsOfUnity n N => ((z : Nˣ) : N)) hρ
      simp only [OneMemClass.coe_one, Units.val_one] at this
      change ρ.1 αN / αN = 1 at this
      rwa [div_eq_one_iff_eq hαN0] at this
    obtain ⟨σ, -, hσL, hσρ⟩ := exists_mem_inertia_fixingSubgroup_restrictNormal_eq ht hW hLN hN0
      ρ.1 ρ.2
    have hσα : σ α = α := by
      have := congrArg (fun z : N => (z : Ω)) hρα
      rw [← hσρ, coe_restrictNormal_apply] at this
      exact this
    have hσM : σ ∈ M.fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      refine ⟨hσL, ?_⟩
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) α :=
        Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hσα)
      have hle : IntermediateField.adjoin (K₀ k t) {α} ≤
          IntermediateField.fixedField (Subgroup.zpowers σ) := by
        rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
        intro g hg
        have := hstab hg
        rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
      exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) σ (Subgroup.mem_zpowers σ)
    refine ⟨ρ.2.1, (mem_fixSub t).mpr fun x hx => ?_⟩
    apply Subtype.val_injective
    rw [← hσρ, coe_restrictNormal_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσM _ hx
  -- counting
  have hkercard : Nat.card χ.ker ≤ Nat.card IM := by
    refine Nat.card_le_card_of_injective (fun ρ => ⟨ρ.1.1, hker ρ.1 ρ.2⟩) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : IM => (z : N ≃ₐ[K₀ k t] N)) h))
  have hGL : Nat.card IL = Nat.card χ.range * Nat.card χ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
  have hGMpos : 0 < Nat.card IM := Nat.card_pos
  have hmuN : Nat.card (rootsOfUnity n N) ≤ n := card_rootsOfUnity N n
  have hrange_le : Nat.card χ.range ≤ Nat.card (rootsOfUnity n N) :=
    Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have hn_le : n ≤ Nat.card χ.range := by
    by_contra hlt
    rw [not_le] at hlt
    have : Nat.card IL < n * Nat.card IM := by
      rw [hGL]
      calc Nat.card χ.range * Nat.card χ.ker ≤ Nat.card χ.range * Nat.card IM :=
            Nat.mul_le_mul_left _ hkercard
        _ < n * Nat.card IM := Nat.mul_lt_mul_of_pos_right hlt hGMpos
    exact absurd hineq (not_le.mpr this)
  have hrange_top : χ.range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm hrange_le (hmuN.trans hn_le))
  have hcardN : Nat.card (rootsOfUnity n N) = n := le_antisymm hmuN (hn_le.trans hrange_le)
  -- `ζ` comes from `μ_n(N)`
  let f : rootsOfUnity n N → rootsOfUnity n Ω := fun η =>
    ⟨Units.map (N.val : N →* Ω) η, by
      rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity n _).mp η.2, map_one]⟩
  have hfinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext; apply Units.ext; apply Subtype.val_injective
    exact congrArg (fun z : rootsOfUnity n Ω => ((z : Ωˣ) : Ω)) h
  have hfsurj : Function.Surjective f :=
    (hfinj.bijective_of_nat_card_le (by rw [hcardN]; exact card_rootsOfUnity Ω n)).2
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨η, hη⟩ := hfsurj ⟨Units.mk0 ζ hζ0, by
    rw [mem_rootsOfUnity]; ext; simp [hζ]⟩
  have hηζ : (((η : Nˣ) : N) : Ω) = ζ := congrArg (fun z : rootsOfUnity n Ω => ((z : Ωˣ) : Ω)) hη
  obtain ⟨ρ, hρ⟩ : η ∈ χ.range := hrange_top ▸ Subgroup.mem_top η
  obtain ⟨σ, hσ, hσL, hσρ⟩ := exists_mem_inertia_fixingSubgroup_restrictNormal_eq ht hW hLN hN0
    ρ.1 ρ.2
  refine ⟨σ, hσ, hσL, ?_⟩
  have h1 : ρ.1 αN = ((η : Nˣ) : N) * αN := by
    have := congrArg (fun z : rootsOfUnity n N => ((z : Nˣ) : N)) hρ
    change ρ.1 αN / αN = _ at this
    rw [← this]
    field_simp
  have h2 := congrArg (fun z : N => (z : Ω)) h1
  rw [← hσρ, coe_restrictNormal_apply] at h2
  simp only [IntermediateField.coe_mul] at h2
  rw [hηζ] at h2
  exact h2

omit [CharZero k] [IsGalois (K₀ k t) Ω] in
include hW in
/-- Values of elements of the square of the center are at most `v(π)²`, if `v(π)` bounds the values
`< 1` on `L`. -/
theorem valuation_le_sq_of_mem_sq (L : IntermediateField (K₀ k t) Ω) {π : Ω}
    (hπ : ∀ f ∈ L, W.valuation f < 1 → W.valuation f ≤ W.valuation π) {b : coordRing k t L}
    (hb : b ∈ centerIdeal hW L ^ 2) : W.valuation (toΩ t L b) ≤ W.valuation π ^ 2 := by
  rw [pow_two] at hb
  refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [map_mul, map_mul, pow_two]
    exact mul_le_mul' (hπ _ (x : L).2 ((mem_centerIdeal hW).mp hx))
      (hπ _ (y : L).2 ((mem_centerIdeal hW).mp hy))
  · rw [(toΩ t L).map_add]
    exact (W.valuation.map_add _ _).trans (max_le hx hy)

set_option maxHeartbeats 2000000 in
-- instance search on coordinate rings of nested intermediate fields is slow
include ht hW in
/-- **The tame character of an arbitrary uniformiser maps inertia onto `μ_n`** (centered model):
`π ∈ L` with `0 < v(π) < 1` and `v(f) ≤ v(π)` for all `f ∈ L` with `v(f) < 1` (a uniformiser of
the discrete valuation ring `W ∩ L`). -/
theorem exists_mem_inertia_eq_mul_of_uniformizer (L : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) L] [IsSepClosed Ω] {π : Ω} (hπL : π ∈ L) (hπ0 : π ≠ 0)
    (hπW : W.valuation π < 1)
    (hπ : ∀ f ∈ L, W.valuation f < 1 → W.valuation f ≤ W.valuation π) {n : ℕ} (hn : 0 < n)
    {α : Ω} (hα : α ^ n = π) {ζ : Ω} (hζ : ζ ^ n = 1) :
    ∃ σ ∈ GaloisPi1.inertia (P := K₀ k t) W, σ ∈ L.fixingSubgroup ∧ σ α = ζ * α := by
  haveI : Algebra.IsSeparable (K₀ k t) L := Algebra.IsSeparable.of_integral _ _
  haveI := isFractionRing_coordRing t L
  have hπWm : π ∈ W := (W.valuation_le_one_iff _).mp hπW.le
  -- the center is nonzero
  have hu0 : centerIdeal hW L ≠ ⊥ := by
    obtain ⟨b₀, s₀, hs₀, hx⟩ := IsFractionRing.div_surjective (coordRing k t L) (⟨π, hπL⟩ : L)
    have hs₀' : (s₀ : coordRing k t L) ≠ 0 := nonZeroDivisors.ne_zero hs₀
    have hb : toΩ t L b₀ = π * toΩ t L s₀ := by
      have := congrArg (fun z : L => (z : Ω)) hx
      simp only [IntermediateField.coe_div] at this
      have hs0Ω : toΩ t L s₀ ≠ 0 := fun h => hs₀' (toΩ_injective L (by rw [h, map_zero]))
      change toΩ t L b₀ / toΩ t L s₀ = π at this
      rw [← this, div_mul_cancel₀ _ hs0Ω]
    intro h
    have hb0 : b₀ ∈ centerIdeal hW L := by
      rw [mem_centerIdeal, hb, map_mul]
      calc W.valuation π * W.valuation (toΩ t L s₀) ≤ W.valuation π * 1 :=
            mul_le_mul_right (valuation_le_one hW s₀) _
        _ < 1 := by rwa [mul_one]
    rw [h, Ideal.mem_bot] at hb0
    apply hπ0
    have hs0Ω : toΩ t L s₀ ≠ 0 := fun h' => hs₀' (toΩ_injective L (by rw [h', map_zero]))
    have := hb
    rw [hb0, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hs0Ω
  -- write `π = b / c` with `c` a unit at `W`
  obtain ⟨b, c, hc, hπbc⟩ := exists_eq_div ht hW L hu0 hπL hπWm
  have hvc : W.valuation (toΩ t L c) = 1 := valuation_eq_one_of_notMem hW hc
  have hc0 : toΩ t L c ≠ 0 := by
    intro h; rw [h, map_zero] at hvc; exact zero_ne_one hvc
  have hbπ : toΩ t L b = π * toΩ t L c := by rw [hπbc, div_mul_cancel₀ _ hc0]
  have hvb : W.valuation (toΩ t L b) = W.valuation π := by rw [hbπ, map_mul, hvc, mul_one]
  have hbu : b ∈ centerIdeal hW L := by rw [mem_centerIdeal, hvb]; exact hπW
  have hbu2 : b ∉ centerIdeal hW L ^ 2 := by
    intro h
    have hle := valuation_le_sq_of_mem_sq hW L hπ h
    rw [hvb, pow_two] at hle
    have hvπ0 : W.valuation π ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ0
    have : W.valuation π * W.valuation π < W.valuation π * 1 :=
      mul_lt_mul_of_pos_left hπW (zero_lt_iff.mpr hvπ0)
    rw [mul_one] at this
    exact absurd hle (not_le.mpr this)
  -- an `n`-th root `γ` of `c`; `β = α γ` is an `n`-th root of `b`
  haveI : NeZero (n : Ω) := ⟨by
    rw [← map_natCast (algebraMap k Ω)]; exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hn.ne')⟩
  obtain ⟨γ, hγ⟩ := IsSepClosed.exists_pow_nat_eq (toΩ t L c) n
  have hγ0 : γ ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hγ; exact hc0 hγ.symm
  have hβ : (α * γ) ^ n = toΩ t L b := by rw [mul_pow, hα, hγ, hbπ]
  obtain ⟨σ, hσ, hσL, hσβ⟩ := exists_mem_inertia_eq_mul ht hW L b hbu hbu2 hn hβ hζ
  refine ⟨σ, hσ, hσL, ?_⟩
  -- `σ` fixes `γ`
  have hcW : toΩ t L c ∈ W := toΩ_mem hW L c
  have hcW' : (toΩ t L c)⁻¹ ∈ W := by
    rw [← (W.valuation_le_one_iff _), map_inv₀, hvc, inv_one]
  have hγW : γ ∈ W := mem_of_pow_mem hn (hγ ▸ hcW)
  have hγW' : γ⁻¹ ∈ W := mem_of_pow_mem hn (by rw [inv_pow, hγ]; exact hcW')
  have hσc : σ (toΩ t L c) = toΩ t L c :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσL _ (c : L).2
  have hσγ : σ γ = γ := by
    refine eq_of_mem_inertia (k := k) hW.1 hσ hγW (valuation_eq_one_of_mem hγW hγW' hγ0) hn
      (ζ := σ γ / γ) ?_ (by field_simp)
    rw [div_pow, ← map_pow, hγ, hσc, div_self hc0]
  rw [map_mul, hσγ] at hσβ
  exact mul_right_cancel₀ hγ0 (by rw [hσβ, mul_assoc])

end Core

section Global

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k]

omit [CharZero k] in
theorem isGalois_of_eq {P Q : IntermediateField k Ω} (h : P = Q) [IsGalois P Ω] :
    IsGalois Q Ω := by
  subst h; assumption

omit [CharZero k] in
theorem finiteDimensional_extendScalars_of_eq {P Q E : IntermediateField k Ω} (h : P = Q)
    (hP : P ≤ E) (hQ : Q ≤ E) [FiniteDimensional P (IntermediateField.extendScalars hP)] :
    FiniteDimensional Q (IntermediateField.extendScalars hQ) := by
  subst h; assumption

omit [CharZero k] in
theorem K₀_inv_eq (t : Ω) : K₀ k t⁻¹ = K₀ k t := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    rwa [inv_inv] at h

omit [CharZero k] in
theorem transcendental_inv {t : Ω} (ht : Transcendental k t) : Transcendental k t⁻¹ := by
  intro h
  apply ht
  rw [← inv_inv t]
  exact h.inv

/-- The model-independent form: `E ⊇ k(s)` finite, `W` centered on the `s`-line. -/
theorem exists_mem_inertia_eq_mul_of_subfield [IsSepClosed Ω] {s : Ω} (hs : Transcendental k s)
    {W : ValuationSubring Ω} (hW : IsCentered k s W) [IsGalois (K₀ k s) Ω]
    (E : IntermediateField k Ω) (hsE : K₀ k s ≤ E)
    [FiniteDimensional (K₀ k s) (IntermediateField.extendScalars hsE)] {π : Ω} (hπE : π ∈ E)
    (hπ0 : π ≠ 0) (hπW : W.valuation π < 1)
    (hπ : ∀ f ∈ E, W.valuation f < 1 → W.valuation f ≤ W.valuation π) {n : ℕ} (hn : 0 < n)
    {α : Ω} (hα : α ^ n = π) {ζ : Ω} (hζ : ζ ^ n = 1) :
    ∃ σ : Ω ≃ₐ[K₀ k s] Ω, σ ∈ GaloisPi1.inertia W ∧ (∀ x ∈ E, σ x = x) ∧ σ α = ζ * α := by
  obtain ⟨σ, hσ, hσL, hσα⟩ := exists_mem_inertia_eq_mul_of_uniformizer hs hW
    (IntermediateField.extendScalars hsE) hπE hπ0 hπW hπ hn hα hζ
  exact ⟨σ, hσ, fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσL x hx, hσα⟩

variable {t : Ω} {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]

/-- **[AbsTopIII] Prop. 1.4(i) at level `n`: the tame character of a uniformiser generates.** Let
`W` be any place of `Ω` containing `k` (in particular a place above a cusp of `U`), `π ∈ F` a
uniformiser of `W ∩ F` (`0 < v_W(π) < 1`, and `v_W(f) ≤ v_W(π)` whenever `f ∈ F`, `v_W(f) < 1`),
and `α` an `n`-th root of `π`. Then every `n`-th root of unity `ζ` equals `σ(α) / α` for some `σ`
in the inertia group `I_W ∩ H`: the Kummer character `σ ↦ σ(α)/α` maps `I_W ∩ H` onto `μ_n`. -/
theorem exists_inertia_tameChar {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    {π : Ω} (hπF : π ∈ F D) (hπ0 : π ≠ 0) (hπW : W.valuation π < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation π) {n : ℕ} (hn : 0 < n)
    {α : Ω} (hα : α ^ n = π) {ζ : Ω} (hζ : ζ ^ n = 1) :
    ∃ σ : D.H, (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W ∧
      (σ : Ω ≃ₐ[K₀ k t] Ω) α = ζ * α := by
  set E : IntermediateField k Ω := (F D).restrictScalars k
  have hK₀E : K₀ k t ≤ E := fun x hx => (F D).algebraMap_mem (⟨x, hx⟩ : K₀ k t)
  have hEF : IntermediateField.extendScalars hK₀E = F D := by ext; rfl
  haveI : FiniteDimensional (K₀ k t) (IntermediateField.extendScalars hK₀E) := by
    rw [hEF]; infer_instance
  have e : (fixedField D.H).fixingSubgroup = D.H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨D.H, D.isClosed_H⟩
  -- an automorphism fixing `E ⊇ k(t)` is an element of `H`
  have toH : ∀ τ : Ω ≃ₐ[K₀ k t] Ω, (∀ x ∈ E, τ x = x) → τ ∈ D.H := by
    intro τ hτ
    rw [← e]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => hτ x hx
  by_cases htW : t ∈ W
  · obtain ⟨σ, hσ, hσE, hσα⟩ := exists_mem_inertia_eq_mul_of_subfield D.transcendental
      ⟨hk, htW⟩ E hK₀E hπF hπ0 hπW hπ hn hα hζ
    exact ⟨⟨σ, toH σ hσE⟩, hσ, hσα⟩
  · have htW' : t⁻¹ ∈ W := (W.mem_or_inv_mem t).resolve_left htW
    have hK := K₀_inv_eq (k := k) t
    haveI : IsGalois (K₀ k t⁻¹) Ω := isGalois_of_eq hK.symm
    have hsE : K₀ k t⁻¹ ≤ E := hK ▸ hK₀E
    haveI : FiniteDimensional (K₀ k t⁻¹) (IntermediateField.extendScalars hsE) :=
      finiteDimensional_extendScalars_of_eq hK.symm hK₀E hsE
    obtain ⟨σ', hσ', hσ'E, hσ'α⟩ := exists_mem_inertia_eq_mul_of_subfield
      (transcendental_inv D.transcendental) ⟨hk, htW'⟩ E hsE hπF hπ0 hπW hπ hn hα hζ
    let σ : Ω ≃ₐ[K₀ k t] Ω := AlgEquiv.ofRingEquiv (f := σ'.toRingEquiv)
      fun x => hσ'E _ (hK₀E x.2)
    exact ⟨⟨σ, toH σ fun x hx => hσ'E x hx⟩, hσ', hσ'α⟩

/-- **The tame character `θ_π = κ_F(π)|_{I_W}` maps `I_W ∩ H` onto `μ_n`** (cohomological form of
`exists_inertia_tameChar`, with `ContH1.evalTriv` as in `Curve/Residue.lean`). -/
theorem evalTriv_kummer_surjective {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)
    (π : (F D)ˣ) (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω))
    (n : ℕ) [NeZero n] (ζ : Mu n Ω) :
    ∃ σ : D.H, ∃ hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W,
      ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π)) = ζ := by
  set α := kummerRoot n (F D) Ω π
  have hα : ((α : Ω)) ^ n = ((π : F D) : Ω) := by
    have := congrArg (fun x : Ωˣ => (x : Ω)) (kummerRoot_pow n (F D) Ω π)
    simpa using this
  have hπ0 : ((π : F D) : Ω) ≠ 0 := fun h => π.ne_zero (Subtype.ext h)
  have hζ : ((Mu.val ζ : Ωˣ) : Ω) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]
  obtain ⟨σ, hσ, hσα⟩ := exists_inertia_tameChar (D := D) hk (π := ((π : F D) : Ω)) (π : F D).2
    hπ0 hπW hπ (Nat.pos_of_ne_zero (NeZero.ne n)) hα hζ
  refine ⟨σ, hσ, ?_⟩
  change kummerFun α (smul_pow_of_pow_eq (kummerRoot_pow n (F D) Ω π)) (toGalF D σ) = ζ
  apply Mu.ext
  apply Units.ext
  simp only [val_kummerFun, Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe, toGalF_apply]
  rw [hσα, mul_div_assoc, div_self α.ne_zero, mul_one]

end Global

end Curve

end KummerTheory
