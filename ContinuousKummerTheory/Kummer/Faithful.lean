/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib
import ContinuousKummerTheory.Curve.FunctionField
import ContinuousKummerTheory.Kummer.PAdic
import ContinuousKummerTheory.Curve.Etale

/-!
# Torally Kummer-faithful fields

Mochizuki, *Topics in Absolute Anabelian Geometry III* ([AbsTopIII]), Definition 1.5
(`T3` l.1807–1836): a field `k` of characteristic zero is *torally Kummer-faithful* if for every
finite extension `k_H ⊆ k̄` of `k` and every torus `A` over `k_H`,
`⋂_{N ≥ 1} N · A(k_H) = {0}`.

A torus splits over a finite extension, and `T(k_H) ⊆ T(k') ≅ (k'ˣ)^r` for a splitting field
`k'`, so the condition for all tori over all finite extensions is equivalent to the condition for
`𝔾_m` over all finite extensions. Mathlib has no algebraic tori, so we take this `𝔾_m`-form as the
definition: `KummerTheory.IsTorallyKummerFaithful k` says that every finite extension of `k` is
Kummer-faithful for `𝔾_m` (`IsKummerFaithfulGm`, `⋂_N (Lˣ)^N = {1}`). We quantify over all
finite extensions `L` in the universe of `k` rather than over subfields of a fixed `k̄`; this is
equivalent (every finite extension embeds into `k̄`), and closed under finite extensions
(`IsTorallyKummerFaithful.of_finite`).

## Main results

* `KummerTheory.isKummerFaithfulGm_of_isDiscreteValuationRing`: the fraction field of a discrete
  valuation ring with finite residue field is Kummer-faithful for `𝔾_m`. Proof: if `x` has
  `N`-th roots for all `N`, we may assume `x ∈ R` (valuation ring), the roots lie in `R`
  (integrally closed), `x` is a unit (Krull), and with `q = #(R/𝔪)` and `N = (q - 1) q^a` the
  root `s` gives `h = s^(q-1) ≡ 1 mod 𝔪`, whence `x = h^(q^a) ≡ 1 mod 𝔪^(a+1)` for all `a`.
  This is the argument of [AbsTopIII] Remark 1.5.3(i) (l.1868–1886), with the residue
  field in place of the `p`-adic topology.
* `KummerTheory.isKummerFaithfulGm_of_isDedekindDomain`: the same for the fraction field of a
  Dedekind domain with a nonzero maximal ideal of finite residue field (localise).
* `KummerTheory.isTorallyKummerFaithful_of_isDedekindDomain`: such fields (of characteristic
  zero) are torally Kummer-faithful: the integral closure in a finite extension has a maximal
  ideal over the given one, with finite residue field.
* Instances of Remark 1.5.3(i) / Remark 1.5.4(i): `KummerTheory.isTorallyKummerFaithful_rat`,
  `NumberField.isTorallyKummerFaithful` (number fields),
  `KummerTheory.isTorallyKummerFaithful_of_isNonarchimedeanLocalField` (finite extensions of
  `ℚ_p` with their local field structure) and `KummerTheory.isTorallyKummerFaithful_padic`.
* `KummerTheory.IsKummerFaithfulGm.not_forall_exists_isPrimitiveRoot`: Remark 1.5.1 (a field
  Kummer-faithful for `𝔾_m` does not contain all `l`-power roots of unity).
* `KummerTheory.Curve.kummerMapZHat_injective_of_isTorallyKummerFaithful` (and the étale and
  number-field versions): [AbsTopIII] Proposition 1.6(i) for torally Kummer-faithful `k`.
-/

universe u

open IsLocalRing

namespace KummerTheory

/-- **Torally Kummer-faithful fields** ([AbsTopIII] Definition 1.5, in its `𝔾_m`-form, see the
module docstring): every finite extension `L` of `K` is Kummer-faithful for `𝔾_m`, i.e.
`⋂_N (Lˣ)^N = {1}`. -/
def IsTorallyKummerFaithful (K : Type u) [Field K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L], IsKummerFaithfulGm L

namespace IsTorallyKummerFaithful

variable {K : Type u} [Field K]

/-- A torally Kummer-faithful field is Kummer-faithful for `𝔾_m`. -/
theorem isKummerFaithfulGm (h : IsTorallyKummerFaithful K) : IsKummerFaithfulGm K := h K

/-- Finite extensions of torally Kummer-faithful fields are torally Kummer-faithful. -/
theorem of_finite (h : IsTorallyKummerFaithful K) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] : IsTorallyKummerFaithful L := fun M _ _ _ => by
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K M := Module.Finite.trans L M
  exact h M

end IsTorallyKummerFaithful

/-- Kummer-faithfulness for `𝔾_m` is invariant under isomorphisms of fields. -/
theorem IsKummerFaithfulGm.of_ringEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (h : IsKummerFaithfulGm K) : IsKummerFaithfulGm L := by
  intro x hx
  have : Units.map e.symm.toMonoidHom x = 1 := h _ fun n hn => by
    obtain ⟨y, hy⟩ := hx n hn
    exact ⟨Units.map e.symm.toMonoidHom y, by rw [← map_pow, hy]⟩
  have h2 := congrArg (fun u : Kˣ => e (u : K)) this
  apply Units.ext
  simpa using h2

section LocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- If `h ≡ 1 mod 𝔪` and `h ≡ 1 mod 𝔪^j`, then `h^q ≡ 1 mod 𝔪^(j+1)` for `q = #(R/𝔪)`:
`h^q - 1 = (h - 1) · ∑_{i<q} h^i` and `∑_{i<q} h^i ≡ q ≡ 0 mod 𝔪`. -/
theorem pow_card_sub_one_mem_pow_succ [Fintype (ResidueField R)] {h : R}
    (h1 : h - 1 ∈ maximalIdeal R) {j : ℕ} (hj : h - 1 ∈ maximalIdeal R ^ j) :
    h ^ Fintype.card (ResidueField R) - 1 ∈ maximalIdeal R ^ (j + 1) := by
  set q := Fintype.card (ResidueField R)
  have hres : residue R h = 1 := by
    rw [← sub_eq_zero, ← map_one (residue R), ← map_sub, residue_eq_zero_iff]
    exact h1
  have hsum : (∑ i ∈ Finset.range q, h ^ i) ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    simp [q]
  have : h ^ q - 1 = (h - 1) * ∑ i ∈ Finset.range q, h ^ i := by
    rw [mul_comm, geom_sum_mul]
  rw [this, pow_succ]
  exact Ideal.mul_mem_mul hj hsum

/-- If `h ≡ 1 mod 𝔪`, then `h^(q^a) ≡ 1 mod 𝔪^(a+1)` for `q = #(R/𝔪)`. -/
theorem pow_card_pow_sub_one_mem [Fintype (ResidueField R)] {h : R}
    (h1 : h - 1 ∈ maximalIdeal R) (a : ℕ) :
    h ^ Fintype.card (ResidueField R) ^ a - 1 ∈ maximalIdeal R ^ (a + 1) := by
  induction a with
  | zero => simpa using h1
  | succ a ih =>
    rw [pow_succ (Fintype.card (ResidueField R)) a, pow_mul]
    have h1' : h ^ Fintype.card (ResidueField R) ^ a - 1 ∈ maximalIdeal R :=
      Ideal.pow_le_self (Nat.succ_ne_zero a) ih
    exact pow_card_sub_one_mem_pow_succ h1' ih

/-- A unit `s` satisfies `s^(q-1) ≡ 1 mod 𝔪` for `q = #(R/𝔪)`. -/
theorem pow_card_sub_one_sub_one_mem [Fintype (ResidueField R)] {s : R} (hs : IsUnit s) :
    s ^ (Fintype.card (ResidueField R) - 1) - 1 ∈ maximalIdeal R := by
  rw [← residue_eq_zero_iff, map_sub, map_pow, map_one, sub_eq_zero]
  apply FiniteField.pow_card_sub_one_eq_one
  exact (hs.map (residue R)).ne_zero

variable [IsDomain R] [IsNoetherianRing R]

/-- **The core lemma.** In a Noetherian local domain with finite residue field, a nonzero element
which is an `n`-th power for every `n ≥ 1` is `1`. -/
theorem eq_one_of_forall_exists_pow_eq [Finite (ResidueField R)] {r : R} (hr : r ≠ 0)
    (h : ∀ n : ℕ, 0 < n → ∃ s : R, s ^ n = r) : r = 1 := by
  cases nonempty_fintype (ResidueField R)
  set q := Fintype.card (ResidueField R) with hq_def
  have hq : 1 < q := Fintype.one_lt_card
  have hbot : (⨅ n : ℕ, maximalIdeal R ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isDomain _ (maximalIdeal.isMaximal R).ne_top
  -- `r` is a unit: otherwise `r ∈ ⋂ₙ 𝔪ⁿ = 0`.
  have hru : IsUnit r := by
    by_contra hnu
    have hrm : r ∈ maximalIdeal R := hnu
    have hmem : r ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
      refine Submodule.mem_iInf _ |>.mpr fun n => ?_
      rcases n.eq_zero_or_pos with rfl | hn
      · simp
      obtain ⟨s, hs⟩ := h n hn
      have hsm : s ∈ maximalIdeal R :=
        (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem n (hs ▸ hrm)
      rw [← hs]
      exact Ideal.pow_mem_pow hsm n
    rw [hbot] at hmem
    exact hr hmem
  have hmem : ∀ a : ℕ, r - 1 ∈ maximalIdeal R ^ (a + 1) := by
    intro a
    obtain ⟨s, hs⟩ := h ((q - 1) * q ^ a) (Nat.mul_pos (by omega) (pow_pos (by omega) a))
    have hsu : IsUnit s :=
      (isUnit_pow_iff (Nat.mul_pos (by omega) (pow_pos (by omega) a)).ne').1 (hs ▸ hru)
    rw [← hs, pow_mul]
    exact pow_card_pow_sub_one_mem (pow_card_sub_one_sub_one_mem hsu) a
  have h1 : r - 1 ∈ ⨅ n : ℕ, maximalIdeal R ^ n :=
    Submodule.mem_iInf _ |>.mpr fun n => Ideal.pow_le_pow_right (Nat.le_succ n) (hmem n)
  rw [hbot] at h1
  exact sub_eq_zero.mp h1

end LocalRing

section DVR

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]

include R in
/-- **The fraction field of a discrete valuation ring with finite residue field is
Kummer-faithful for `𝔾_m`** (the argument of [AbsTopIII] Remark 1.5.3(i), l.1868–1886). -/
theorem isKummerFaithfulGm_of_isDiscreteValuationRing : IsKummerFaithfulGm K := by
  have key : ∀ x : Kˣ, (∀ n : ℕ, 0 < n → ∃ y : Kˣ, y ^ n = x) →
      IsLocalization.IsInteger R (x : K) → x = 1 := by
    intro x hx ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [← hr, map_zero])
    have : r = 1 := eq_one_of_forall_exists_pow_eq hr0 fun n hn => by
      obtain ⟨y, hy⟩ := hx n hn
      have hint : IsIntegral R ((y : K) ^ n) := by
        rw [← Units.val_pow_eq_pow_val, hy, ← hr]
        exact isIntegral_algebraMap
      obtain ⟨s, hs⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn hint
      refine ⟨s, IsFractionRing.injective R K ?_⟩
      rw [map_pow, hs, ← Units.val_pow_eq_pow_val, hy, hr]
    apply Units.ext
    rw [← hr, this, map_one, Units.val_one]
  intro x hx
  rcases ValuationRing.isInteger_or_isInteger R (x : K) with hint | hint
  · exact key x hx hint
  · have := key x⁻¹ (fun n hn => by
      obtain ⟨y, hy⟩ := hx n hn
      exact ⟨y⁻¹, by rw [inv_pow, hy]⟩) (by rwa [Units.val_inv_eq_inv_val])
    exact inv_eq_one.mp this

end DVR

section Dedekind

/-- **The fraction field of a Dedekind domain with a nonzero maximal ideal of finite residue
field is Kummer-faithful for `𝔾_m`** (localise at the ideal and apply
`isKummerFaithfulGm_of_isDiscreteValuationRing`). -/
theorem isKummerFaithfulGm_of_isDedekindDomain (A L : Type*) [CommRing A] [IsDedekindDomain A]
    [Field L] [Algebra A L] [IsFractionRing A L] (P : Ideal A) [P.IsMaximal] (hP : P ≠ ⊥)
    [Finite (A ⧸ P)] : IsKummerFaithfulGm L := by
  let Aₚ := Localization.AtPrime P
  haveI : IsDiscreteValuationRing Aₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP Aₚ
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h0 => y.2 ?_
    rw [← map_zero (algebraMap A L)] at h0
    rw [IsFractionRing.injective A L h0]
    exact P.zero_mem
  letI : Algebra Aₚ L := (IsLocalization.lift (M := P.primeCompl) (S := Aₚ) hunit).toAlgebra
  haveI : IsScalarTower A Aₚ L := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := P.primeCompl) (S := Aₚ) hunit x).symm
  haveI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Aₚ L
  haveI : Finite (ResidueField Aₚ) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal P Aₚ).toEquiv
  exact isKummerFaithfulGm_of_isDiscreteValuationRing Aₚ L

/-- **Finite separable extensions** of the fraction field `K` of a Dedekind domain `A` with a
nonzero maximal ideal `P` of finite residue field are Kummer-faithful for `𝔾_m`: the integral
closure `S` of `A` in `L` is a Dedekind domain, finite over `A`, with a maximal ideal `Q` over
`P`, and `S ⧸ Q` is finite over `A ⧸ P`. -/
theorem isKummerFaithfulGm_of_finite (A K L : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (P : Ideal A)
    [P.IsMaximal] (hP : P ≠ ⊥) [Finite (A ⧸ P)] : IsKummerFaithfulGm L := by
  let S := integralClosure A L
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain A K L
  haveI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  haveI : Module.Finite A S := IsIntegralClosure.finite A K L S
  have hinj : Function.Injective (algebraMap A S) := by
    intro x y hxy
    have := congrArg (algebraMap S L) hxy
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at this
    exact IsFractionRing.injective A K ((algebraMap K L).injective this)
  have hker : RingHom.ker (algebraMap A S) ≤ P := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
  haveI : Q.LiesOver P := ⟨by rw [Ideal.under_def, hQ]⟩
  haveI : Finite (S ⧸ Q) := Module.finite_of_finite (A ⧸ P)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hP
    rw [← hQ, Ideal.comap_bot_of_injective _ hinj]
  exact isKummerFaithfulGm_of_isDedekindDomain S L Q hQ0

/-- **Fraction fields of Dedekind domains with a nonzero maximal ideal of finite residue field
are torally Kummer-faithful** (in characteristic zero; [AbsTopIII] Remark 1.5.3(i)). -/
theorem isTorallyKummerFaithful_of_isDedekindDomain (A : Type*) (K : Type u) [CommRing A]
    [IsDedekindDomain A] [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K] (P : Ideal A)
    [P.IsMaximal] (hP : P ≠ ⊥) [Finite (A ⧸ P)] : IsTorallyKummerFaithful K := by
  intro L _ _ _
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact isKummerFaithfulGm_of_finite A K L P hP

end Dedekind

section Examples

/-- `ℚ` is torally Kummer-faithful. -/
theorem isTorallyKummerFaithful_rat : IsTorallyKummerFaithful ℚ := by
  haveI : (Ideal.span {((2 : ℕ) : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by norm_num)).mpr
      (Int.prime_iff_natAbs_prime.mpr (by norm_num)) |>.isMaximal (by simp)
  haveI : Finite (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod 2).toEquiv.symm
  exact isTorallyKummerFaithful_of_isDedekindDomain ℤ ℚ (Ideal.span {((2 : ℕ) : ℤ)})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)

/-- **Number fields are torally Kummer-faithful** ([AbsTopIII] Remark 1.5.3(i)). -/
theorem _root_.NumberField.isTorallyKummerFaithful (K : Type u) [Field K] [NumberField K] :
    IsTorallyKummerFaithful K := by
  intro L _ _ _
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : (Ideal.span {((2 : ℕ) : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by norm_num)).mpr
      (Int.prime_iff_natAbs_prime.mpr (by norm_num)) |>.isMaximal (by simp)
  haveI : Finite (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod 2).toEquiv.symm
  exact isKummerFaithfulGm_of_finite ℤ ℚ L (Ideal.span {((2 : ℕ) : ℤ)})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)

open ValuativeRel in
/-- **Non-archimedean local fields of characteristic zero (finite extensions of `ℚ_p`) are
torally Kummer-faithful** ([AbsTopIII] Remark 1.5.4(i) for tori). -/
theorem isTorallyKummerFaithful_of_isNonarchimedeanLocalField (K : Type u) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] :
    IsTorallyKummerFaithful K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : Finite (𝒪[K] ⧸ maximalIdeal 𝒪[K]) := inferInstanceAs (Finite 𝓀[K])
  exact isTorallyKummerFaithful_of_isDedekindDomain 𝒪[K] K (maximalIdeal 𝒪[K])
    (IsDiscreteValuationRing.not_a_field _)

/-- **`ℚ_p` is torally Kummer-faithful.** -/
theorem isTorallyKummerFaithful_padic (p : ℕ) [Fact p.Prime] :
    IsTorallyKummerFaithful ℚ_[p] := by
  haveI : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) := inferInstanceAs (Finite (ResidueField ℤ_[p]))
  exact isTorallyKummerFaithful_of_isDedekindDomain ℤ_[p] ℚ_[p] (maximalIdeal ℤ_[p])
    (IsDiscreteValuationRing.not_a_field _)

end Examples

section Cyclotomic

/-- **[AbsTopIII] Remark 1.5.1** (`T3` l.1837–1855), field-theoretic content: a field which is
Kummer-faithful for `𝔾_m` does not contain all `l`-power roots of unity. (Otherwise a primitive
`l`-th root of unity `ξ ≠ 1` is an `N`-th power for every `N = l^e r`, `l ∤ r`: `ξ` is a power of
`ζ^(l^e)` for a primitive `l^(e+1)`-th root `ζ`, and `ζ` is an `r`-th power since `r` is invertible
modulo `l^(e+1)`.) Applied to all finite extensions of a torally Kummer-faithful field, this says
that `k(μ_{l^∞})/k` is infinite, i.e. the `l`-adic cyclotomic character has infinite, hence open,
image. -/
theorem IsKummerFaithfulGm.not_forall_exists_isPrimitiveRoot {L : Type*} [Field L]
    (h : IsKummerFaithfulGm L) {l : ℕ} (hl : l.Prime) :
    ¬ ∀ m : ℕ, ∃ ζ : L, IsPrimitiveRoot ζ (l ^ m) := by
  intro hall
  obtain ⟨ξ, hξ⟩ := hall 1
  rw [pow_one] at hξ
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hl.ne_zero
  apply hξ.ne_one hl.one_lt
  have key := h (Units.mk0 ξ hξ0) fun N hN => by
    obtain ⟨e, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
    obtain ⟨ζ, hζ⟩ := hall (e + 1)
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ hl.ne_zero)
    -- `ζ^(l^e)` is a primitive `l`-th root of unity, and `ξ` is a power of it
    have hη : IsPrimitiveRoot (ζ ^ l ^ e) l := by
      have := hζ.pow_of_dvd (pow_ne_zero e hl.ne_zero) (pow_dvd_pow l (Nat.le_succ e))
      rwa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hl.pos e)] at this
    haveI : NeZero l := ⟨hl.ne_zero⟩
    obtain ⟨j, -, hj⟩ := hη.eq_pow_of_pow_eq_one hξ.pow_eq_one
    -- `ζ` is an `r`-th power: `r` is invertible modulo `l^(e+1)`
    have hcop : Nat.Coprime r (l ^ (e + 1)) :=
      (Nat.Coprime.pow_left (e + 1) ((Nat.Prime.coprime_iff_not_dvd hl).mpr hr)).symm
    have hg := Nat.gcd_eq_gcd_ab r (l ^ (e + 1))
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hg
    set A := Nat.gcdA r (l ^ (e + 1))
    set B := Nat.gcdB r (l ^ (e + 1))
    have h1 : ζ ^ ((r : ℤ) * A + ((l ^ (e + 1) : ℕ) : ℤ) * B) = ζ := by rw [← hg, zpow_one]
    rw [zpow_add₀ hζ0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hζ.pow_eq_one, one_zpow,
      mul_one] at h1
    have hζr : (ζ ^ A) ^ r = ζ := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact h1
    have hw0 : ζ ^ A ≠ 0 := zpow_ne_zero A hζ0
    refine ⟨Units.mk0 ((ζ ^ A) ^ j) (pow_ne_zero j hw0), Units.ext ?_⟩
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [← hj]
    conv_rhs => rw [← hζr]
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  simpa using congrArg Units.val key

/-- For a torally Kummer-faithful field `k`, no finite extension contains all `l`-power roots of
unity ([AbsTopIII] Remark 1.5.1: the `l`-adic cyclotomic character of `k` has open image). -/
theorem IsTorallyKummerFaithful.not_forall_exists_isPrimitiveRoot {K : Type u} [Field K]
    (h : IsTorallyKummerFaithful K) (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    {l : ℕ} (hl : l.Prime) : ¬ ∀ m : ℕ, ∃ ζ : L, IsPrimitiveRoot ζ (l ^ m) :=
  (h L).not_forall_exists_isPrimitiveRoot hl

end Cyclotomic

namespace Curve

open AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsSepClosed Ω]

/-- **[AbsTopIII] Proposition 1.6(i)** (`T3` l.1969–1988) for a torally Kummer-faithful field
`k` algebraically closed in the function field: `κ_U : Γ(U, 𝒪^×) → H¹(Π_U, Ẑ(1))` is
injective. -/
theorem kummerMapZHat_injective_of_isTorallyKummerFaithful
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (hkf : IsTorallyKummerFaithful k) : Function.Injective (kummerMapZHat D) :=
  kummerMapZHat_injective hk hkf.isKummerFaithfulGm

/-- [AbsTopIII] Proposition 1.6(i) on `π₁ᵉᵗ(U)` for torally Kummer-faithful `k`. -/
theorem kummerMapEtaleZHat_injective_of_isTorallyKummerFaithful
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (hkf : IsTorallyKummerFaithful k) : Function.Injective (kummerMapEtaleZHat D) :=
  kummerMapEtaleZHat_injective D hk hkf.isKummerFaithfulGm

/-- [AbsTopIII] Proposition 1.6(i) over a number field `k`. -/
theorem kummerMapZHat_injective_of_numberField [NumberField k]
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    Function.Injective (kummerMapZHat D) :=
  kummerMapZHat_injective_of_isTorallyKummerFaithful hk (NumberField.isTorallyKummerFaithful k)

end Curve

end KummerTheory
