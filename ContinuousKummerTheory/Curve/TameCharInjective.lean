/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.TameChar
import Pi1.Orbicurve.Pullback

/-!
# The tame character is injective on inertia

[AbsTopIII] Proposition 1.4(i) (`T3` l.1764): "the inertia group `I_x` of `x` in `Δ_U` is naturally
isomorphic to `Ẑ(1)`". The isomorphism is the tame character `θ_π : I_W → Ẑ(1)`,
`σ ↦ (σ(π^{1/n}) / π^{1/n})_n`, for a uniformiser `π` at `x`. Its surjectivity at every level
is `Curve.evalTriv_kummer_surjective` (`Curve/TameChar.lean`). Here we prove that it is
**injective**: an element of the inertia group of `W` that fixes `F` and an `n`-th root of `π`
for every `n` is the identity.

Proof (characteristic `0`, so all inertia groups are cyclic): given `x ∈ Ω`, let `N` be a finite
Galois extension of `k(t)` containing `F(x)`, `e = e(N | F)`, `α` an `e`-th root of `π` fixed by
`σ` and `M = F(α)`. In the Galois closure `N''` of `N M`, the Kummer character of `α` embeds
`I(N''/F) / I(N''/M)` into `μ_e`, so `e(M | F) ≤ e`, while `e(M | F) ≥ e` because `π` is an
`e`-th power in `M` (`le_ramificationIdx_of_eq_pow`). Since the inertia group is cyclic, the
ramification index of the compositum `N M` divides `lcm(e(N|F), e(M|F)) = e`
(`pi1`'s `ramificationIdx_sup_dvd`), so `I(N''/N M) = I(N''/M)` by counting. The restriction
of `σ` lies in `I(N''/M)`, hence fixes `N ∋ x`.

* `Curve.fixes_of_mem_inertia_of_fixes_roots` (centered model, uniformiser in the coordinate
  ring);
* `Curve.eq_one_of_mem_inertia_of_fixes_roots`: for a place `W ⊇ k` of `Ω` (cusps included), a
  uniformiser `π ∈ F` of `W ∩ F` and `σ ∈ I_W ∩ H` fixing an `n`-th root of `π` for all `n`,
  `σ = 1`;
* `Curve.eq_one_of_forall_evalTriv_kummer_eq_one`: the cohomological form — `σ ∈ I_W ∩ H` with
  `θ_π(σ) = 1` at every level is trivial (`⋂_n ker θ_{π,n} = 1`).
-/

universe u

open groupCohomology AffOrbicurve IntermediateField IntermediateField.algebraAdjoinAdjoin Ideal

namespace KummerTheory

namespace Curve

section Core

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
  (ht : Transcendental k t) {W : ValuationSubring Ω} (hW : IsCentered k t W)
  [IsGalois (K₀ k t) Ω]

omit [CharZero k] [IsGalois (K₀ k t) Ω] in
/-- An automorphism fixing `L` and `α` fixes `L(α)`. -/
theorem mem_fixingSubgroup_sup_adjoin {L : IntermediateField (K₀ k t) Ω} {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσL : σ ∈ L.fixingSubgroup) {α : Ω} (hσα : σ α = α) :
    σ ∈ (L ⊔ IntermediateField.adjoin (K₀ k t) {α}).fixingSubgroup := by
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

set_option synthInstance.maxHeartbeats 400000 in
-- `MulAction Gal(N/k(t)) (coordRing k t N)` for nested intermediate fields is slow to synthesise
set_option maxHeartbeats 4000000 in
-- instance search on coordinate rings of nested intermediate fields is slow
include ht in
/-- **Injectivity of the tame character** (centered model): let `W` be centered on the `t`-line,
`L` finite over `k(t)`, `p` a uniformiser of the center `u_W(L)`, and `σ` in the inertia group of
`W`, fixing `L` and, for every `n > 0`, some `n`-th root of `p`. Then `σ` fixes every `x ∈ Ω`. -/
theorem fixes_of_mem_inertia_of_fixes_roots (L : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) L] (p : coordRing k t L) (hp : p ∈ centerIdeal hW L)
    (hp2 : p ∉ centerIdeal hW L ^ 2) {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ GaloisPi1.inertia (P := K₀ k t) W) (hσL : σ ∈ L.fixingSubgroup)
    (hfix : ∀ n : ℕ, 0 < n → ∃ α : Ω, α ^ n = toΩ t L p ∧ σ α = α) (x : Ω) : σ x = x := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hp2 (Ideal.zero_mem _)
  have hpΩ : toΩ t L p ≠ 0 := fun h => hp0 (toΩ_injective L (by rw [h, map_zero]))
  have hq0 : centerIdeal hW L ≠ ⊥ := fun h => hp0 (by simpa [h] using hp)
  -- a finite Galois extension `N ⊇ L(x)`
  have hxint : IsIntegral (K₀ k t) x := Algebra.IsIntegral.isIntegral x
  set N₀ : IntermediateField (K₀ k t) Ω := L ⊔ IntermediateField.adjoin (K₀ k t) {x}
  haveI : FiniteDimensional (K₀ k t) (IntermediateField.adjoin (K₀ k t) {x}) :=
    IntermediateField.adjoin.finiteDimensional hxint
  haveI : FiniteDimensional (K₀ k t) N₀ := IntermediateField.finiteDimensional_sup _ _
  set N : IntermediateField (K₀ k t) Ω := normalClosure (K₀ k t) N₀ Ω
  haveI : FiniteDimensional (K₀ k t) N := normalClosure.is_finiteDimensional _ _ _
  haveI : IsGalois (K₀ k t) N := ⟨⟩
  have hLN : L ≤ N := le_sup_left.trans (IntermediateField.le_normalClosure N₀)
  have hxN : x ∈ N := IntermediateField.le_normalClosure N₀
    ((le_sup_right : IntermediateField.adjoin (K₀ k t) {x} ≤ N₀)
      (IntermediateField.mem_adjoin_simple_self (K₀ k t) x))
  have hN0 : centerIdeal hW N ≠ ⊥ := centerIdeal_ne_bot_of_le hW hLN hq0
  -- `e = e(N | L) > 0`
  set e : ℕ := (letI := algRing t hLN; (centerIdeal hW N).ramificationIdx (coordRing k t L))
    with he_def
  have he0 : 0 < e := by
    haveI := isMaximal_centerIdeal ht hW N hN0
    have h := ramificationIdx_mul_card t ht hLN le_rfl (centerIdeal hW N)
    rw [comap_centerIdeal hW le_rfl] at h
    change e * _ = _ at h
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, zero_mul] at h
      exact absurd h.symm (Nat.card_pos (α := ((centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ⊓
        fixSub t N L : Subgroup _))).ne'
    · exact h0
  haveI : NeZero e := ⟨he0.ne'⟩
  -- an `e`-th root `α` of `p` fixed by `σ`, and `M = L(α)`
  obtain ⟨α, hα, hσα⟩ := hfix e he0
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow he0.ne'] at hα
    exact hpΩ hα.symm
  have hαint : IsIntegral (K₀ k t) α := Algebra.IsIntegral.isIntegral α
  set M : IntermediateField (K₀ k t) Ω := L ⊔ IntermediateField.adjoin (K₀ k t) {α}
  haveI : FiniteDimensional (K₀ k t) (IntermediateField.adjoin (K₀ k t) {α}) :=
    IntermediateField.adjoin.finiteDimensional hαint
  haveI : FiniteDimensional (K₀ k t) M := IntermediateField.finiteDimensional_sup _ _
  have hLM : L ≤ M := le_sup_left
  have hαM : α ∈ M := (le_sup_right : IntermediateField.adjoin (K₀ k t) {α} ≤ M)
    (IntermediateField.mem_adjoin_simple_self (K₀ k t) α)
  -- the Galois closure `N''` of `N M`
  set NM : IntermediateField (K₀ k t) Ω := N ⊔ M with hNM_def
  haveI : FiniteDimensional (K₀ k t) NM := IntermediateField.finiteDimensional_sup _ _
  set N'' : IntermediateField (K₀ k t) Ω := normalClosure (K₀ k t) NM Ω
  haveI : FiniteDimensional (K₀ k t) N'' := normalClosure.is_finiteDimensional _ _ _
  haveI : IsGalois (K₀ k t) N'' := ⟨⟩
  have hNM'' : N ⊔ M ≤ N'' := IntermediateField.le_normalClosure _
  have hNN'' : N ≤ N'' := le_sup_left.trans hNM''
  have hMN'' : M ≤ N'' := le_sup_right.trans hNM''
  have hLN'' : L ≤ N'' := hLM.trans hMN''
  -- `e ≤ e(M | L)`: `p` is an `e`-th power in `M`
  have hαintA : IsIntegral (A₀ k t) (⟨α, hαM⟩ : M) := by
    refine IsIntegral.of_pow he0 ?_
    have : (⟨α, hαM⟩ : M) ^ e = (IntermediateField.inclusion hLM) (p : L) := by
      apply Subtype.ext; simp [hα]
    rw [this]
    exact (p.2 : IsIntegral (A₀ k t) (p : L)).map
      ((IntermediateField.inclusion hLM).restrictScalars (A₀ k t))
  set aM : coordRing k t M := ⟨⟨α, hαM⟩, hαintA⟩
  have hpa : ringMap t hLM p = aM ^ e := by
    apply Subtype.ext; apply Subtype.ext
    change ((p : L) : Ω) = α ^ e
    rw [hα]; rfl
  have hvp : W.valuation (toΩ t L p) < 1 := (mem_centerIdeal hW).mp hp
  have hva : aM ∈ centerIdeal hW M := by
    rw [mem_centerIdeal]
    change W.valuation α < 1
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ W.valuation α ^ e := one_le_pow₀ h
    rw [← map_pow, hα] at this
    exact absurd hvp (not_lt.mpr this)
  have he_le := le_ramificationIdx_of_eq_pow ht hW hLM p hp hp2 aM hva e hpa
  set eM : ℕ := (letI := algRing t hLM; (centerIdeal hW M).ramificationIdx (coordRing k t L))
    with heM_def
  -- inertia groups in `N''`
  set u := centerIdeal hW N''
  have hu0 : u ≠ ⊥ := centerIdeal_ne_bot_of_le hW hLN'' hq0
  haveI hNmax := isMaximal_centerIdeal ht hW N'' hu0
  set IL := u.inertia (N'' ≃ₐ[K₀ k t] N'') ⊓ fixSub t N'' L
  set IM := u.inertia (N'' ≃ₐ[K₀ k t] N'') ⊓ fixSub t N'' M
  set INM := u.inertia (N'' ≃ₐ[K₀ k t] N'') ⊓ fixSub t N'' (N ⊔ M)
  have hcM := ramificationIdx_mul_card t ht hLM hMN'' u
  rw [comap_centerIdeal hW hMN''] at hcM
  change eM * Nat.card IM = Nat.card IL at hcM
  -- the Kummer character of `α` embeds `IL / IM` into `μ_e`, so `e(M | L) ≤ e`
  set αN : N'' := ⟨α, hMN'' hαM⟩
  have hαN0 : αN ≠ 0 := fun h => hα0 (congrArg Subtype.val h)
  have hfixp : ∀ ρ ∈ IL, ρ (αN ^ e) = αN ^ e := by
    intro ρ hρ
    have hpL : (αN ^ e : N'') = ⟨toΩ t L p, hLN'' (p : L).2⟩ := Subtype.ext (by
      change α ^ e = _; exact hα)
    rw [hpL]
    exact (mem_fixSub t).mp hρ.2 _ (p : L).2
  have hχpow : ∀ ρ ∈ IL, (ρ αN / αN) ^ e = 1 := by
    intro ρ hρ
    rw [div_pow, ← map_pow, hfixp ρ hρ, div_self (pow_ne_zero _ hαN0)]
  let χfun : IL → rootsOfUnity e N'' := fun ρ =>
    ⟨Units.mk0 (ρ.1 αN / αN) (div_ne_zero ((map_ne_zero _).mpr hαN0) hαN0), by
      rw [mem_rootsOfUnity]; ext; simp [hχpow ρ.1 ρ.2]⟩
  have hχval : ∀ ρ : IL, ((χfun ρ : N''ˣ) : N'') = ρ.1 αN / αN := fun _ => rfl
  let χ : IL →* rootsOfUnity e N'' :=
    { toFun := χfun
      map_one' := by
        apply Subtype.ext; apply Units.ext
        rw [hχval]
        simp [div_self hαN0]
      map_mul' := fun ρ τ => by
        apply Subtype.ext; apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [hχval, hχval, hχval]
        have hfix := fix_root_of_unity_of_mem_inertia_fixSub hW ht hLN'' hu0 ρ.2 he0
          (hχpow τ.1 τ.2)
        have h1 : τ.1 αN = (τ.1 αN / αN) * αN := by field_simp
        change ρ.1 (τ.1 αN) / αN = _
        rw [h1, map_mul, hfix]
        field_simp }
  -- the kernel of `χ` lies in `IM`
  have hker : ∀ ρ : IL, χ ρ = 1 → ρ.1 ∈ IM := by
    intro ρ hρ
    have hρα : ρ.1 αN = αN := by
      have := congrArg (fun z : rootsOfUnity e N'' => ((z : N''ˣ) : N'')) hρ
      simp only [OneMemClass.coe_one, Units.val_one] at this
      change ρ.1 αN / αN = 1 at this
      rwa [div_eq_one_iff_eq hαN0] at this
    obtain ⟨τ, -, hτL, hτρ⟩ := exists_mem_inertia_fixingSubgroup_restrictNormal_eq ht hW hLN'' hu0
      ρ.1 ρ.2
    have hτα : τ α = α := by
      have := congrArg (fun z : N'' => (z : Ω)) hρα
      rw [← hτρ, coe_restrictNormal_apply] at this
      exact this
    have hτM := mem_fixingSubgroup_sup_adjoin hτL hτα
    refine ⟨ρ.2.1, (mem_fixSub t).mpr fun y hy => ?_⟩
    apply Subtype.val_injective
    rw [← hτρ, coe_restrictNormal_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτM _ hy
  -- counting: `|IL| ≤ e · |IM|`, hence `e(M | L) = e`
  have hkercard : Nat.card χ.ker ≤ Nat.card IM := by
    refine Nat.card_le_card_of_injective (fun ρ => ⟨ρ.1.1, hker ρ.1 ρ.2⟩) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : IM => (z : N'' ≃ₐ[K₀ k t] N'')) h))
  have hGL : Nat.card IL = Nat.card χ.range * Nat.card χ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
  have hGMpos : 0 < Nat.card IM := Nat.card_pos
  have hrange_le : Nat.card χ.range ≤ e :=
    (Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective).trans
      (card_rootsOfUnity N'' e)
  have hILle : Nat.card IL ≤ e * Nat.card IM := by
    rw [hGL]
    exact Nat.mul_le_mul hrange_le hkercard
  have heM : eM = e := by
    refine le_antisymm ?_ he_le
    rw [← hcM] at hILle
    exact Nat.le_of_mul_le_mul_right hILle hGMpos
  -- the compositum `N M` has ramification index dividing `e` (tame inertia is cyclic)
  have h₁ : (letI := algRing t hLN; (u.comap (ringMap t hNN'')).ramificationIdx
      (coordRing k t L)) ∣ e := by
    rw [comap_centerIdeal hW hNN'']
  have h₂ : (letI := algRing t hLM; (u.comap (ringMap t hMN'')).ramificationIdx
      (coordRing k t L)) ∣ e := by
    rw [comap_centerIdeal hW hMN'']
    change eM ∣ e
    rw [heM]
  have hdvd := ramificationIdx_sup_dvd t ht hLN hLM hNN'' hMN'' u hu0 h₁ h₂
  have hcNM := ramificationIdx_mul_card t ht (hLN.trans (le_sup_left : N ≤ N ⊔ M))
    (sup_le hNN'' hMN'') u
  set eNM := (letI := algRing t (hLN.trans (le_sup_left : N ≤ N ⊔ M));
    (u.comap (ringMap t (sup_le hNN'' hMN''))).ramificationIdx (coordRing k t L))
  change eNM * Nat.card INM = Nat.card IL at hcNM
  have hILpos : 0 < Nat.card IL := Nat.card_pos
  have heNM_pos : 0 < eNM := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hcNM
    exact hILpos.ne' hcNM.symm
  have heNM : eNM ≤ e := Nat.le_of_dvd he0 hdvd
  -- hence `INM = IM`
  have hINM : INM = IM := by
    refine Subgroup.eq_of_le_of_card_ge (inf_le_inf_left _ (fixSub_antitone t le_sup_right)) ?_
    refine Nat.le_of_mul_le_mul_left ?_ heNM_pos
    rw [hcNM, ← hcM, heM]
    exact Nat.mul_le_mul_right _ heNM
  -- the restriction of `σ` lies in `IM = INM`, so it fixes `N ∋ x`
  have hσM := mem_fixingSubgroup_sup_adjoin hσL hσα
  have hρ : σ.restrictNormal N'' ∈ IM := by
    refine ⟨restrictNormal_mem_inertia hW N'' hσ, (mem_fixSub t).mpr fun y hy => ?_⟩
    apply Subtype.val_injective
    rw [coe_restrictNormal_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσM _ hy
  rw [← hINM] at hρ
  have hxNM : x ∈ N ⊔ M := (le_sup_left : N ≤ N ⊔ M) hxN
  have := (mem_fixSub t).mp hρ.2 ⟨x, hNM'' hxNM⟩ hxNM
  have := congrArg (fun z : N'' => (z : Ω)) this
  rwa [coe_restrictNormal_apply] at this

set_option maxHeartbeats 2000000 in
-- instance search on coordinate rings of nested intermediate fields is slow
include ht hW in
/-- **Injectivity of the tame character** (centered model, arbitrary uniformiser `π ∈ L` of the
discrete valuation ring `W ∩ L`). -/
theorem fixes_of_mem_inertia_of_fixes_roots_of_uniformizer (L : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) L] [IsSepClosed Ω] {π : Ω} (hπL : π ∈ L) (hπ0 : π ≠ 0)
    (hπW : W.valuation π < 1)
    (hπ : ∀ f ∈ L, W.valuation f < 1 → W.valuation f ≤ W.valuation π) {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ GaloisPi1.inertia (P := K₀ k t) W) (hσL : σ ∈ L.fixingSubgroup)
    (hfix : ∀ n : ℕ, 0 < n → ∃ α : Ω, α ^ n = π ∧ σ α = α) (x : Ω) : σ x = x := by
  haveI : Algebra.IsSeparable (K₀ k t) L := Algebra.IsSeparable.of_integral _ _
  haveI := isFractionRing_coordRing t L
  have hπWm : π ∈ W := (W.valuation_le_one_iff _).mp hπW.le
  -- the center is nonzero
  have hu0 : centerIdeal hW L ≠ ⊥ := by
    obtain ⟨b₀, s₀, hs₀, hx⟩ := IsFractionRing.div_surjective (coordRing k t L) (⟨π, hπL⟩ : L)
    have hs₀' : (s₀ : coordRing k t L) ≠ 0 := nonZeroDivisors.ne_zero hs₀
    have hs0Ω : toΩ t L s₀ ≠ 0 := fun h => hs₀' (toΩ_injective L (by rw [h, map_zero]))
    have hb : toΩ t L b₀ = π * toΩ t L s₀ := by
      have := congrArg (fun z : L => (z : Ω)) hx
      simp only [IntermediateField.coe_div] at this
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
  refine fixes_of_mem_inertia_of_fixes_roots ht hW L b hbu hbu2 hσ hσL (fun n hn => ?_) x
  -- an `n`-th root of `b` fixed by `σ`: `α γ` with `αⁿ = π`, `γⁿ = c`
  obtain ⟨α, hα, hσα⟩ := hfix n hn
  haveI : NeZero (n : Ω) := ⟨by
    rw [← map_natCast (algebraMap k Ω)]; exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hn.ne')⟩
  obtain ⟨γ, hγ⟩ := IsSepClosed.exists_pow_nat_eq (toΩ t L c) n
  have hγ0 : γ ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hγ; exact hc0 hγ.symm
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
  exact ⟨α * γ, by rw [mul_pow, hα, hγ, hbπ], by rw [map_mul, hσα, hσγ]⟩

end Core

section Global

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]

/-- **[AbsTopIII] Prop. 1.4(i): the tame character is injective on `I_W ∩ H`.** Let `W` be a
place of `Ω` containing `k` (in particular a place above a cusp of `U`), `π ∈ F` a uniformiser
of `W ∩ F`, and `σ ∈ H` in the inertia group of `W` fixing, for every `n > 0`, some `n`-th root
of `π`. Then `σ = 1`. -/
theorem eq_one_of_mem_inertia_of_fixes_roots {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) {π : Ω} (hπF : π ∈ F D) (hπ0 : π ≠ 0)
    (hπW : W.valuation π < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation π) {σ : D.H}
    (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W)
    (hfix : ∀ n : ℕ, 0 < n → ∃ α : Ω, α ^ n = π ∧ (σ : Ω ≃ₐ[K₀ k t] Ω) α = α) : σ = 1 := by
  have hσF : ∀ x ∈ F D, (σ : Ω ≃ₐ[K₀ k t] Ω) x = x := fun x hx =>
    fixes_of_mem_F σ.2 ⟨x, hx⟩
  suffices h : ∀ x : Ω, (σ : Ω ≃ₐ[K₀ k t] Ω) x = x by
    exact Subtype.ext (AlgEquiv.ext h)
  set E : IntermediateField k Ω := (F D).restrictScalars k
  have hK₀E : K₀ k t ≤ E := fun x hx => (F D).algebraMap_mem (⟨x, hx⟩ : K₀ k t)
  by_cases htW : t ∈ W
  · exact fixes_of_mem_inertia_of_fixes_roots_of_uniformizer D.transcendental ⟨hk, htW⟩ (F D)
      hπF hπ0 hπW hπ hσ ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσF) hfix
  · have htW' : t⁻¹ ∈ W := (W.mem_or_inv_mem t).resolve_left htW
    have hK := K₀_inv_eq (k := k) t
    haveI : IsGalois (K₀ k t⁻¹) Ω := isGalois_of_eq hK.symm
    have hsE : K₀ k t⁻¹ ≤ E := hK ▸ hK₀E
    have hEF : IntermediateField.extendScalars hK₀E = F D := by ext; rfl
    haveI : FiniteDimensional (K₀ k t) (IntermediateField.extendScalars hK₀E) := by
      rw [hEF]; infer_instance
    haveI : FiniteDimensional (K₀ k t⁻¹) (IntermediateField.extendScalars hsE) :=
      finiteDimensional_extendScalars_of_eq hK.symm hK₀E hsE
    let σ' : Ω ≃ₐ[K₀ k t⁻¹] Ω := AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[K₀ k t] Ω).toRingEquiv)
      fun x => hσF _ (hK₀E (hK ▸ x.2))
    intro x
    exact fixes_of_mem_inertia_of_fixes_roots_of_uniformizer
      (transcendental_inv D.transcendental) ⟨hk, htW'⟩ (IntermediateField.extendScalars hsE)
      (π := π) hπF hπ0 hπW hπ (σ := σ') hσ
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun y hy => hσF y hy) hfix x

/-- **The tame character is injective, cohomological form** ([AbsTopIII] Prop. 1.4(i)): an
element `σ ∈ I_W ∩ H` on which the tame characters `θ_{π,n} = κ_F(π)|_{I_W ∩ H}` are trivial
for all `n` is `1`. -/
theorem eq_one_of_forall_evalTriv_kummer_eq_one {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (π : (F D)ˣ) (hπW : W.valuation ((π : F D) : Ω) < 1)
    (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω)) {σ : D.H}
    (hσ : (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W)
    (h1 : ∀ (n : ℕ) [NeZero n],
      ContH1.evalTriv σ (inertia_smul_mu hk hσ n) (resMu D n (kummer n (F D) Ω π)) = 1) :
    σ = 1 := by
  have hπ0 : ((π : F D) : Ω) ≠ 0 := fun h => π.ne_zero (Subtype.ext h)
  refine eq_one_of_mem_inertia_of_fixes_roots hk (π : F D).2 hπ0 hπW hπ hσ fun n hn => ?_
  haveI : NeZero n := ⟨hn.ne'⟩
  set α := kummerRoot n (F D) Ω π
  refine ⟨α, ?_, ?_⟩
  · have := congrArg (fun x : Ωˣ => (x : Ω)) (kummerRoot_pow n (F D) Ω π)
    simpa using this
  · have h := h1 n
    change kummerFun α (smul_pow_of_pow_eq (kummerRoot_pow n (F D) Ω π)) (toGalF D σ) = 1 at h
    have h' := congrArg (fun z : Mu n Ω => ((Mu.val z : Ωˣ) : Ω)) h
    simp only [val_kummerFun, Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_coe, toGalF_apply, map_one, Units.val_one] at h'
    exact (div_eq_one_iff_eq (Units.ne_zero α)).mp h'

end Global

end Curve

end KummerTheory
