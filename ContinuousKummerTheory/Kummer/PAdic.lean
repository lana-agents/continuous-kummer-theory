/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.ProfiniteCompletion

/-!
# Finiteness of `Kˣ/(Kˣ)ⁿ` for `p`-adic fields

We prove `FiniteKummerQuotients K` — `Kˣ/(Kˣ)ⁿ` is finite for every `n ≥ 1` — for

* the fraction field `K` of characteristic zero of a complete discrete valuation ring `R` with
  finite residue field (`KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing`);
* every non-archimedean local field of characteristic zero in the sense of Mathlib's
  `IsNonarchimedeanLocalField` (i.e. every finite extension of `ℚ_p`, once given its local field
  structure) — an instance;
* `ℚ_[p]` — an instance.

Hence `KummerTheory.kummerZHatEquivProfiniteCompletion`
(`H¹_cont(G_K, Ẑ(1)) ≃* (Kˣ)^∧`) applies to these fields without further hypotheses.

The proof is self-contained:

* `KummerTheory.exists_fixedPoint_of_adicContraction`: in an `I`-adically complete ring, a map
  `T` with `T y - T y' ∈ I · (y - y')` has a fixed point (a Banach fixed-point theorem for the
  `I`-adic topology).
* `KummerTheory.exists_pow_eq_one_add` (a Hensel/Newton-type lemma for `Xⁿ - u`, valid also when
  `n` is divisible by the residue characteristic): if `d ∈ I` then every element of
  `1 + n² d R` is an `n`-th power. Indeed `(1 + n d y)ⁿ = 1 + n² d (y + Q(y))` where all
  coefficients of `Q` are divisible by `d` (`KummerTheory.one_add_pow_eq`), and `y ↦ w - Q(y)` is
  an `I`-adic contraction. This is the statement `U^{(m)} ⊆ (Kˣ)ⁿ` for `m ≥ v(n² ϖ)`.
* Writing `x ∈ Kˣ` as `u ϖᵏ` with `u ∈ Rˣ`, the classes of `ϖⁱ r` with `0 ≤ i < n` and `r`
  ranging over representatives of the finite ring `R/(n² ϖ)` exhaust `Kˣ/(Kˣ)ⁿ`
  (`KummerTheory.finiteIndex_powRange_of_isDiscreteValuationRing`).
-/

open IsLocalRing

namespace KummerTheory

section Adic

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem mem_pow_smul_top_iff (n : ℕ) (x : R) :
    x ∈ (I ^ n • ⊤ : Submodule R R) ↔ x ∈ I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- **Fixed points of `I`-adic contractions.** In an `I`-adically complete ring, a map `T` with
`T y - T y' ∈ I · (y - y')` has a fixed point. -/
theorem exists_fixedPoint_of_adicContraction [IsAdicComplete I R] (T : R → R)
    (hT : ∀ y y', ∃ r ∈ I, T y - T y' = r * (y - y')) : ∃ y, T y = y := by
  set s : ℕ → R := fun j => T^[j] 0 with hs
  have hsucc : ∀ j, s (j + 1) = T (s j) := fun j => Function.iterate_succ_apply' T j 0
  have hstep : ∀ j, s (j + 1) - s j ∈ I ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨r, hr, h⟩ := hT (s (j + 1)) (s j)
      rw [show s (j + 1 + 1) - s (j + 1) = T (s (j + 1)) - T (s j) by
        rw [hsucc (j + 1), ← hsucc j], h, pow_succ']
      exact Ideal.mul_mem_mul hr ih
  have hcauchy : ∀ m k, s (m + k) - s m ∈ I ^ m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have := Ideal.pow_le_pow_right (Nat.le_add_right m k) (hstep (m + k))
      rw [← add_assoc, show s (m + k + 1) - s m = (s (m + k + 1) - s (m + k)) + (s (m + k) - s m)
        by ring]
      exact add_mem this ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) s (fun {m n} hmn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← neg_sub, neg_mem_iff]
    exact hcauchy m k)
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := I) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_iff]
  have h1 : s n - L ∈ I ^ n := by
    have := hL n
    rwa [SModEq.sub_mem, mem_pow_smul_top_iff] at this
  have h2 : s (n + 1) - L ∈ I ^ n := by
    have := hL (n + 1)
    rw [SModEq.sub_mem, mem_pow_smul_top_iff] at this
    exact Ideal.pow_le_pow_right (Nat.le_succ n) this
  obtain ⟨r, -, h⟩ := hT L (s n)
  rw [show T L - L = T L - T (s n) + (s (n + 1) - L) by rw [hsucc]; ring, h]
  refine add_mem ?_ h2
  rw [← neg_sub, mul_neg]
  exact neg_mem (Ideal.mul_mem_left _ _ h1)

/-- The higher-order part of `(1 + N d y)^N`, divided by `N² d`. -/
noncomputable def powCorr (m : ℕ) (d y : R) : R :=
  ∑ k ∈ Finset.range m, ((m + 1).choose (k + 2) : R) * ((m + 1 : ℕ) : R) ^ k * d ^ (k + 1) *
    y ^ (k + 2)

theorem one_add_pow_eq (m : ℕ) (d y : R) :
    (1 + ((m + 1 : ℕ) : R) * d * y) ^ (m + 1) =
      1 + ((m + 1 : ℕ) : R) ^ 2 * d * (y + powCorr m d y) := by
  rw [add_comm 1, add_pow, Finset.sum_range_succ', Finset.sum_range_succ', powCorr, mul_add,
    Finset.mul_sum]
  have : ∀ k ∈ Finset.range m, (((m + 1 : ℕ) : R) * d * y) ^ (k + 1 + 1) *
      1 ^ (m + 1 - (k + 1 + 1)) * ((m + 1).choose (k + 1 + 1) : R) =
      ((m + 1 : ℕ) : R) ^ 2 * d * (((m + 1).choose (k + 2) : R) * ((m + 1 : ℕ) : R) ^ k *
        d ^ (k + 1) * y ^ (k + 2)) := fun k _ => by ring
  rw [Finset.sum_congr rfl this]
  simp only [zero_add, pow_one, one_pow, mul_one, pow_zero, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one]
  ring

/-- **Hensel-type lemma for `n`-th powers.** In an `I`-adically complete ring, every element of
`1 + n² d R` with `d ∈ I` is an `n`-th power. -/
theorem exists_pow_eq_one_add [IsAdicComplete I R] (n : ℕ) {d : R} (hd : d ∈ I) (w : R) :
    ∃ y : R, y ^ n = 1 + (n : R) ^ 2 * d * w := by
  obtain _ | m := n
  · exact ⟨1, by simp⟩
  obtain ⟨y, hy⟩ := exists_fixedPoint_of_adicContraction I (fun y => w - powCorr m d y)
    (fun y y' => by
      refine ⟨-∑ k ∈ Finset.range m, ((m + 1).choose (k + 2) : R) * ((m + 1 : ℕ) : R) ^ k *
        d ^ (k + 1) * ∑ i ∈ Finset.range (k + 2), y ^ i * y' ^ (k + 2 - 1 - i), ?_, ?_⟩
      · refine neg_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_)
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hd _ k.succ_pos)
      · simp only [powCorr, sub_sub_sub_cancel_left, neg_mul, Finset.sum_mul,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc _ (∑ i ∈ _, _), geom_sum₂_mul]
        ring)
  refine ⟨1 + ((m + 1 : ℕ) : R) * d * y, ?_⟩
  rw [one_add_pow_eq, show y + powCorr m d y = w by linear_combination -hy]

end Adic

section DVR

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]

include R in
/-- For `K` the fraction field of a complete discrete valuation ring `R` with finite residue field,
the subgroup `(Kˣ)ⁿ` has finite index in `Kˣ` whenever `n ≠ 0` in `K`. -/
theorem finiteIndex_powRange_of_isDiscreteValuationRing (n : ℕ) (hn : (n : K) ≠ 0) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hn' : (n : R) ≠ 0 := fun h => hn (by simpa using congrArg (algebraMap R K) h)
  have hnpos : n ≠ 0 := by rintro rfl; simp at hn
  set c : R := (n : R) ^ 2 * ϖ with hc_def
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hn') hϖ.ne_zero
  have hfin : Finite (R ⧸ Ideal.span {c}) := by
    rw [IsLocalRing.finite_quotient_iff]
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {c}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
    exact ⟨k, by rw [hk, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  have hϖK : algebraMap R K ϖ ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne hϖ.ne_zero
  set P := (powMonoidHom n : Kˣ →* Kˣ).range
  let πK : Kˣ := Units.mk0 _ hϖK
  let F : Fin n × (R ⧸ Ideal.span {c}) → Kˣ ⧸ P := fun it =>
    if h : IsUnit it.2.out then
      QuotientGroup.mk (πK ^ (it.1 : ℕ) * Units.map (algebraMap R K : R →* K) h.unit)
    else 1
  have hF : Function.Surjective F := by
    intro x
    induction x using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨k, u, hx⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ x.ne_zero
    set t : R ⧸ Ideal.span {c} := Ideal.Quotient.mk _ (u : R)
    have ht : t.out - u ∈ Ideal.span {c} :=
      Ideal.Quotient.eq.1 (by rw [Ideal.Quotient.mk_out])
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 ht
    have hunit : IsUnit t.out := by
      have h := IsLocalRing.isUnit_or_isUnit_of_isUnit_add
        (show IsUnit (t.out + -(w * c)) by rw [← sub_eq_add_neg, hw]; simp)
      refine h.resolve_right fun h' => hϖ.not_isUnit ?_
      have h2 : IsUnit c := isUnit_of_mul_isUnit_right ((IsUnit.neg_iff _).1 h')
      rw [hc_def] at h2
      exact isUnit_of_mul_isUnit_right h2
    obtain ⟨y, hy⟩ := exists_pow_eq_one_add (maximalIdeal R) n
      ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) (-(w * ↑hunit.unit⁻¹))
    have hu : (u : R) = t.out * y ^ n := by
      rw [hy]
      have : (t.out : R) * ↑hunit.unit⁻¹ = 1 := hunit.mul_val_inv
      linear_combination hw + (w * c) * this
    have hyU : IsUnit y :=
      (isUnit_pow_iff hnpos).1 (isUnit_of_mul_isUnit_right (hu ▸ u.isUnit))
    obtain ⟨yU, rfl⟩ := hyU
    have hn0 : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hnpos
    set i : ℕ := (k % n).toNat with hi_def
    have hik : (i : ℤ) = k % n := Int.toNat_of_nonneg (Int.emod_nonneg _ hn0.ne')
    have hi : i < n := by
      have := Int.emod_lt_of_pos k hn0
      omega
    refine ⟨(⟨i, hi⟩, t), ?_⟩
    simp only [F, dif_pos hunit]
    rw [QuotientGroup.eq]
    refine ⟨πK ^ (k / n) * Units.map (algebraMap R K : R →* K) yU, ?_⟩
    rw [powMonoidHom_apply, eq_inv_mul_iff_mul_eq]
    apply Units.ext
    have hu' := congrArg (algebraMap R K) hu
    simp only [map_mul, map_pow] at hu'
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
      IsUnit.unit_spec, hx, Units.smul_def, Algebra.smul_def, hu', Units.val_zpow_eq_zpow_val,
      πK, Units.val_mk0]
    have hk : algebraMap R K ϖ ^ k = algebraMap R K ϖ ^ i * (algebraMap R K ϖ ^ (k / n)) ^ n := by
      rw [← zpow_natCast (algebraMap R K ϖ) i, ← zpow_natCast (algebraMap R K ϖ ^ (k / n)) n,
        ← zpow_mul, ← zpow_add₀ hϖK, hik, Int.emod_add_ediv_mul]
    rw [hk]
    ring
  have : Finite (Kˣ ⧸ P) := Finite.of_surjective F hF
  exact Subgroup.finiteIndex_of_finite_quotient

include R in
/-- **Finiteness of `Kˣ/(Kˣ)ⁿ`** for the fraction field `K` (of characteristic zero) of a complete
discrete valuation ring `R` with finite residue field. -/
theorem finiteKummerQuotients_of_isDiscreteValuationRing [CharZero K] :
    FiniteKummerQuotients K :=
  ⟨fun n hn => finiteIndex_powRange_of_isDiscreteValuationRing R K n (by exact_mod_cast hn)⟩

end DVR

section LocalField

open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Finiteness of `Kˣ/(Kˣ)ⁿ` for non-archimedean local fields of characteristic zero** (finite
extensions of `ℚ_p`), so that `kummerZHatEquivProfiniteCompletion` applies to them. -/
instance [CharZero K] : FiniteKummerQuotients K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  exact finiteKummerQuotients_of_isDiscreteValuationRing 𝒪[K] K

end LocalField

section Padic

variable (p : ℕ) [Fact p.Prime]

instance : Finite (ResidueField ℤ_[p]) :=
  Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).toEquiv.symm

instance : FiniteKummerQuotients ℚ_[p] :=
  finiteKummerQuotients_of_isDiscreteValuationRing ℤ_[p] ℚ_[p]

end Padic

/-- **Kummer theory for `ℚ_p`**: `H¹_cont(G_{ℚ_p}, Ẑ(1))` is the profinite completion of `ℚ_pˣ`. -/
noncomputable def padicKummerZHatEquiv (p : ℕ) [Fact p.Prime] :
    ContH1 Gal(AlgebraicClosure ℚ_[p]/ℚ_[p]) (ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p])) ≃*
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of ℚ_[p]ˣ) :=
  kummerZHatEquivProfiniteCompletion ℚ_[p] (AlgebraicClosure ℚ_[p])

end KummerTheory
