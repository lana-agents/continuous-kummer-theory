/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib
import Pi1.Orbicurve.SubfieldGalois
import Pi1.RingTheory.Transcendence

/-!
# Function fields of curves over Kummer-faithful fields are Kummer-faithful for `𝔾_m`

Mochizuki, *Topics in Absolute Anabelian Geometry III*, Definition 1.5: a field `k` of
characteristic zero is *Kummer-faithful* (resp. *torally Kummer-faithful*) if for every finite
extension `k_H` of `k` and every semi-abelian variety (resp. torus) `A` over `k_H`,

  (a) `⋂_{N ≥ 1} N · A(k_H) = {0}`,

equivalently (b) the Kummer map `A(k_H) → H¹(H, Hom(ℚ/ℤ, A(k̄)))` is injective.

Here we formalise condition (a) for `A = 𝔾_m` over `k` itself (`KummerTheory.IsKummerFaithfulGm`):
`⋂_N (kˣ)^N = {1}`. This is implied by torally Kummer-faithfulness, and it is what the proof of
[AbsTopIII] Prop. 1.6(i) uses ("since `k` is [torally] Kummer-faithful, so is the function field
`K_X`", via Remark 1.5.4(ii)). The equivalence (a) ⇔ (b) for `𝔾_m` is
`KummerTheory.kummerZHat_injective_iff` (in `Curve/Kummer.lean`).

## Main results

* `KummerTheory.not_forall_exists_pow_eq_of_transcendental`: in a field `F` of transcendence
  degree `1` over `k` (characteristic `0`), essentially of finite type, a transcendental element
  `f` is not an `n`-th power for all `n`. Proof: `{f}` is a transcendence basis, so `F` is finite
  over `k(f)`; in the integral closure `R` of `k[f]` in `F` (a Dedekind domain) `f` is a non-unit,
  and if `f = gₙⁿ` for all `n` then `f ∈ ⋂ₙ Pⁿ = 0` for a maximal ideal `P ∋ f` (Krull).
* `KummerTheory.isKummerFaithfulGm_of_trdeg_eq_one`: such an `F`, with `k` algebraically closed in
  `F`, is Kummer-faithful for `𝔾_m` if `k` is ([AbsTopIII] Rem. 1.5.4(ii) for `𝔾_m`, in
  transcendence degree one).
* `KummerTheory.isKummerFaithfulGm_of_finiteDimensional`: the case of a finite extension `L` of
  `k(t)` inside a field `Ω` (the function fields of the curves of `Pi1.Orbicurve`).
-/

universe u

open AffOrbicurve IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace KummerTheory

/-- **Kummer-faithfulness for `𝔾_m`** ([AbsTopIII] Definition 1.5(a) for `A = 𝔾_m`, `k_H = k`):
the only element of `Kˣ` which is an `n`-th power for every `n ≥ 1` is `1`. -/
def IsKummerFaithfulGm (K : Type*) [Field K] : Prop :=
  ∀ x : Kˣ, (∀ n : ℕ, 0 < n → ∃ y : Kˣ, y ^ n = x) → x = 1

section General

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [CharZero k]

omit [CharZero k] in
/-- A transcendental element of a field of transcendence degree one is a transcendence basis,
so the field is algebraic over `k(f)`. -/
theorem isAlgebraic_adjoin_of_trdeg_eq_one (htr : Algebra.trdeg k F = 1) {f : F}
    (hf : Transcendental k f) : Algebra.IsAlgebraic (K₀ k f) F := by
  have hind : AlgebraicIndependent k (fun _ : PUnit.{u + 1} => f) :=
    algebraicIndependent_unique_type_iff.mpr hf
  have hb : IsTranscendenceBasis k (fun _ : PUnit.{u + 1} => f) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite
      (by rw [htr, Cardinal.mk_fintype PUnit.{u + 1}]; simp)
  have := hb.isAlgebraic_field
  rwa [Set.range_const] at this

omit [CharZero k] in
/-- In a function field of one variable, `F` is finite over `k(f)` for transcendental `f`. -/
theorem finiteDimensional_adjoin_of_trdeg_eq_one (htr : Algebra.trdeg k F = 1)
    [Algebra.EssFiniteType k F] {f : F} (hf : Transcendental k f) :
    FiniteDimensional (K₀ k f) F := by
  haveI := isAlgebraic_adjoin_of_trdeg_eq_one htr hf
  haveI : Algebra.EssFiniteType (K₀ k f) F := Algebra.EssFiniteType.of_comp k (K₀ k f) F
  exact Algebra.finite_of_intermediateFieldFG_of_isAlgebraic (K₀ k f) F
    (IntermediateField.fg_top_iff.mpr inferInstance)

omit [CharZero k] in
/-- `f` is not a unit of the integral closure of `k[f]` (in any field extension of `k(f)`),
for `f` transcendental over `k`: otherwise `f⁻¹ ∈ k(f)` would be integral over `k[f]`, hence in
`k[f] ≅ k[X]`, where `X` is not a unit. -/
theorem inv_not_isIntegral {f : F} (hf : Transcendental k f) :
    ¬ IsIntegral (A₀ k f) (AdjoinSimple.gen k f)⁻¹ := by
  intro h
  haveI := isDedekindDomain_A₀ hf
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A₀ k f) (K := K₀ k f)).mp h
  have hfy : (⟨f, Algebra.self_mem_adjoin_singleton k f⟩ : A₀ k f) * y = 1 := by
    apply FaithfulSMul.algebraMap_injective (A₀ k f) (K₀ k f)
    rw [map_mul, hy, algebraMap_eq_gen_self, map_one, mul_inv_cancel₀]
    intro h0
    apply hf
    have : f = 0 := by simpa using congrArg Subtype.val h0
    rw [this]
    exact isAlgebraic_zero
  have hu : IsUnit (⟨f, Algebra.self_mem_adjoin_singleton k f⟩ : A₀ k f) :=
    IsUnit.of_mul_eq_one _ hfy
  have hX : (Polynomial.algEquivOfTranscendental k f hf).symm
      ⟨f, Algebra.self_mem_adjoin_singleton k f⟩ = Polynomial.X := by
    apply (Polynomial.algEquivOfTranscendental k f hf).injective
    rw [AlgEquiv.apply_symm_apply]
    ext
    simp
  exact Polynomial.not_isUnit_X (hX ▸ hu.map (Polynomial.algEquivOfTranscendental k f hf).symm)

/-- **A transcendental element is not infinitely divisible** in a function field of one variable
over a field of characteristic zero. -/
theorem not_forall_exists_pow_eq_of_transcendental (htr : Algebra.trdeg k F = 1)
    [Algebra.EssFiniteType k F] {f : F} (hf : Transcendental k f) :
    ¬ ∀ n : ℕ, 0 < n → ∃ g : F, g ^ n = f := by
  intro hroot
  haveI := finiteDimensional_adjoin_of_trdeg_eq_one htr hf
  set L : IntermediateField (K₀ k f) F := ⊤
  haveI : FiniteDimensional (K₀ k f) L :=
    (IntermediateField.topEquiv (F := K₀ k f) (E := F)).symm.toLinearEquiv.finiteDimensional
  haveI : Algebra.IsSeparable (K₀ k f) L := Algebra.IsSeparable.of_integral _ _
  haveI := isDedekindDomain_ring f hf L
  -- `f` as an element of the coordinate ring `R = coordRing k f L`
  have hfint : IsIntegral (A₀ k f) (⟨f, IntermediateField.mem_top⟩ : L) := by
    have : (⟨f, IntermediateField.mem_top⟩ : L) =
        algebraMap (A₀ k f) L ⟨f, Algebra.self_mem_adjoin_singleton k f⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap
  set fR : coordRing k f L := ⟨_, hfint⟩
  have hfR0 : fR ≠ 0 := by
    intro h
    apply hf
    have : f = 0 := by simpa [fR] using congrArg (fun x : coordRing k f L => ((x : L) : F)) h
    rw [this]
    exact isAlgebraic_zero
  have hfRu : ¬ IsUnit fR := by
    rintro ⟨u, hu⟩
    apply inv_not_isIntegral hf
    have hint : IsIntegral (A₀ k f) (((u⁻¹ : (coordRing k f L)ˣ) : coordRing k f L) : L) :=
      (mem_integralClosure_iff _ _).mp ((u⁻¹ : (coordRing k f L)ˣ) : coordRing k f L).2
    have h1 : algebraMap (K₀ k f) L (AdjoinSimple.gen k f) *
        (((u⁻¹ : (coordRing k f L)ˣ) : coordRing k f L) : L) = 1 := by
      have h2 := congrArg (fun x : coordRing k f L => (x : L)) u.mul_inv
      simp only [hu] at h2
      exact h2
    have hinv : (((u⁻¹ : (coordRing k f L)ˣ) : coordRing k f L) : L) =
        IsScalarTower.toAlgHom (A₀ k f) (K₀ k f) L (AdjoinSimple.gen k f)⁻¹ := by
      rw [IsScalarTower.coe_toAlgHom', map_inv₀]
      exact eq_inv_of_mul_eq_one_right h1
    rw [hinv] at hint
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (A₀ k f) (K₀ k f) L)
      (algebraMap (K₀ k f) L).injective).mp hint
  obtain ⟨P, hPmax, hfP⟩ := Ideal.exists_le_maximal (Ideal.span {fR})
    (Ideal.span_singleton_ne_top hfRu)
  have hmem : ∀ n : ℕ, fR ∈ P ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨g, hg⟩ := hroot n hn
    have hgint : IsIntegral (A₀ k f) (⟨g, IntermediateField.mem_top⟩ : L) := by
      refine IsIntegral.of_pow hn ?_
      have : (⟨g, IntermediateField.mem_top⟩ : L) ^ n = ⟨f, IntermediateField.mem_top⟩ :=
        Subtype.ext hg
      rw [this]
      exact hfint
    set gR : coordRing k f L := ⟨_, hgint⟩
    have hgfR : gR ^ n = fR := Subtype.ext (Subtype.ext hg)
    have hgP : gR ∈ P :=
      hPmax.isPrime.mem_of_pow_mem n (hgfR ▸ hfP (Ideal.mem_span_singleton_self _))
    rw [← hgfR]
    exact Ideal.pow_mem_pow hgP n
  have h0 : fR ∈ ⨅ n : ℕ, P ^ n := Submodule.mem_iInf _ |>.mpr hmem
  rw [Ideal.iInf_pow_eq_bot_of_isDomain P hPmax.ne_top] at h0
  exact hfR0 h0

/-- **[AbsTopIII] Remark 1.5.4(ii) for `𝔾_m` in transcendence degree one**: a function field of one
variable `F` over a field `k` of characteristic zero which is Kummer-faithful for `𝔾_m`, with `k`
algebraically closed in `F`, is Kummer-faithful for `𝔾_m`. -/
theorem isKummerFaithfulGm_of_trdeg_eq_one (htr : Algebra.trdeg k F = 1)
    [Algebra.EssFiniteType k F]
    (hk : ∀ x : F, IsAlgebraic k x → x ∈ Set.range (algebraMap k F))
    (hkf : IsKummerFaithfulGm k) : IsKummerFaithfulGm F := by
  intro x hx
  by_cases halg : IsAlgebraic k (x : F)
  · obtain ⟨c, hc⟩ := hk _ halg
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by simpa using hc.symm)
    have : Units.mk0 c hc0 = 1 := by
      refine hkf _ fun n hn => ?_
      obtain ⟨y, hy⟩ := hx n hn
      have hyalg : IsAlgebraic k (y : F) :=
        IsAlgebraic.of_pow hn (by rw [← Units.val_pow_eq_pow_val, hy]; exact halg)
      obtain ⟨d, hd⟩ := hk _ hyalg
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact y.ne_zero (by simpa using hd.symm)
      refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
      apply (algebraMap k F).injective
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hd, hc]
      rw [← Units.val_pow_eq_pow_val, hy]
    apply Units.ext
    rw [← hc, Units.val_one]
    simpa using congrArg (fun u : kˣ => algebraMap k F u) this
  · refine (not_forall_exists_pow_eq_of_transcendental htr halg fun n hn => ?_).elim
    obtain ⟨y, hy⟩ := hx n hn
    exact ⟨y, by rw [← Units.val_pow_eq_pow_val, hy]⟩

end General

section Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} (ht : Transcendental k t)
  (L : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) L]

include ht in
/-- A finite extension of `k(t)` has transcendence degree one over `k`. -/
theorem trdeg_eq_one : Algebra.trdeg k L = 1 := by
  have h1 : Algebra.trdeg k (A₀ k t) = 1 := by
    rw [← (Polynomial.algEquivOfTranscendental k t ht).trdeg_eq]
    exact Polynomial.trdeg_of_isDomain
  haveI : Algebra.IsAlgebraic (A₀ k t) L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A₀ k t) (K := K₀ k t)).mpr
      (Algebra.IsAlgebraic.of_finite (K₀ k t) L)
  have h2 : Algebra.trdeg (A₀ k t) L = 0 := trdeg_eq_zero
  haveI : FaithfulSMul k (A₀ k t) :=
    (faithfulSMul_iff_algebraMap_injective k _).mpr (algebraMap k (A₀ k t)).injective
  rw [← trdeg_add_eq (A := L) k (A₀ k t), h1, h2, add_zero]

include ht in
/-- A finite extension of `k(t)` (characteristic zero) is essentially of finite type over `k`. -/
theorem essFiniteType [CharZero k] : Algebra.EssFiniteType k L := by
  haveI := isFractionRing_coordRing t L
  haveI := finiteType_ring t ht L
  exact IntermediateField.fg_top_iff.mp (Algebra.FiniteType.FG_top_of_isFractionRing
    (R := k) (S := coordRing k t L) (K := L))

include ht in
/-- **The function field of a curve over a Kummer-faithful field is Kummer-faithful for `𝔾_m`**
([AbsTopIII] Remark 1.5.4(ii), used in the proof of Prop. 1.6(i)): `L` finite over `k(t)`, `k` of
characteristic zero, Kummer-faithful for `𝔾_m` and algebraically closed in `L`. -/
theorem isKummerFaithfulGm_of_finiteDimensional [CharZero k]
    (hk : ∀ x : L, IsAlgebraic k x → x ∈ Set.range (algebraMap k L))
    (hkf : IsKummerFaithfulGm k) : IsKummerFaithfulGm L :=
  haveI := essFiniteType ht L
  isKummerFaithfulGm_of_trdeg_eq_one (trdeg_eq_one ht L) hk hkf

end Curve

end KummerTheory
