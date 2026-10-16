/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Decomposition
import ContinuousKummerTheory.Kummer.Restriction

/-!
# The arithmetic quotient `Π_U → G_k` and Kummer classes of constants

Let `k̄ ⊆ Ω` be the algebraic closure of `k` in `Ω` and `G_k = Gal(k̄ / k)`. Restriction to `k̄`
gives `H ≅ Gal(Ω / F) → G_k`; the inertia groups of places `W ⊇ k` fix `k̄` pointwise
(`Curve.inertia_fix_algebraic`: in residue characteristic `0`, distinct conjugates of an
algebraic element stay distinct modulo `𝔪_W`), so it factors through `Π_U`
(`Curve.piToGk : Π_U →* G_k`, the arithmetic quotient of the Galois model of `Π_U`).

The Kummer class of a constant `c ∈ kˣ` (a unit of `U`) is the pull-back along `Π_U → G_k` of the
Kummer class of `c` in `H¹(G_k, μ_n(k̄))` (`Curve.kummerMap_const`): this is the first map
`(kˣ)^∧ → H¹(Π_U, M_X)` of the exact sequence of [AbsTopIII] Prop. 1.6(iii), on Kummer classes.
If `k` is algebraically closed in `F`, `Π_U → G_k` is surjective (`Curve.piToGk_surjective`) and
`kˣ/(kˣ)ⁿ → H¹(Π_U, μ_n)` is injective (`Curve.kummerMap_const_eq_one_iff`).
-/

universe u

open groupCohomology AffOrbicurve IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace KummerTheory

namespace Curve

section Algebraic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} [CharZero k]
  {W : ValuationSubring Ω} (hk : ∀ c : k, algebraMap k Ω c ∈ W)

/-- `k → W`. -/
def toW : k →+* W := (algebraMap k Ω).codRestrict W.toSubring hk

omit [CharZero k] in
include hk in
/-- Elements of `Ω` integral over `k ⊆ W` lie in `W`. -/
theorem mem_of_isIntegral {y : Ω} (hy : IsIntegral k y) : y ∈ W := by
  have hint : IsIntegral W y := by
    refine ⟨(minpoly k y).map (toW hk), (minpoly.monic hy).map _, ?_⟩
    rw [eval₂_map]
    exact minpoly.aeval k y
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hz]
  exact z.2

include hk in
/-- **Inertia fixes algebraic elements** (residue characteristic `0`): if `σ` (fixing `k`) is in
the inertia group of a place `W ⊇ k`, then `σ x = x` for every `x` algebraic over `k`. -/
theorem inertia_fix_algebraic {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) {x : Ω}
    (hx : IsAlgebraic k x) : σ x = x := by
  have hxi : IsIntegral k x := hx.isIntegral
  set f := minpoly k x
  have hsep : f.Separable := (minpoly.irreducible hxi).separable
  set σk : Ω →ₐ[k] Ω := (σ.restrictScalars k).toAlgHom
  have hσx_root : aeval (σ x) f = 0 := by
    have := Polynomial.aeval_algHom_apply σk x f
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hσxi : IsIntegral k (σ x) := ⟨f, minpoly.monic hxi, hσx_root⟩
  by_contra hne
  -- work in `W[X]`
  set xW : W := ⟨x, mem_of_isIntegral hk hxi⟩
  set sW : W := ⟨σ x, mem_of_isIntegral hk hσxi⟩
  set fW : W[X] := f.map (toW hk)
  have hfW : ∀ z : W, (algebraMap W Ω) (fW.eval z) = aeval (z : Ω) f := by
    intro z
    rw [← Polynomial.eval₂_hom, aeval_def, eval₂_map]
    simp only [eval₂_eq_eval_map]
    rfl
  have hroot : fW.IsRoot xW := by
    apply Subtype.val_injective
    have := hfW xW
    rw [minpoly.aeval] at this
    exact this
  set gW := fW /ₘ (X - C xW)
  have hfac : (X - C xW) * gW = fW := (mul_divByMonic_eq_iff_isRoot).mpr hroot
  -- `g(σx) = 0`
  have hsW : fW.eval sW = 0 := by
    apply Subtype.val_injective
    exact (hfW sW).trans hσx_root
  have hgs : gW.eval sW = 0 := by
    have := congrArg (eval sW) hfac
    rw [eval_mul, hsW] at this
    simp only [eval_sub, eval_X, eval_C] at this
    refine (mul_eq_zero.mp this).resolve_left ?_
    intro h
    apply hne
    exact congrArg Subtype.val (sub_eq_zero.mp h)
  -- `g(x) = f'(x) ≠ 0`
  have hgx : gW.eval xW = fW.derivative.eval xW := by
    rw [← hfac, derivative_mul]
    simp [eval_add, eval_mul]
  set d : Ω := aeval x (derivative f)
  have hd : ((Polynomial.eval xW gW : W) : Ω) = d := by
    rw [hgx]
    change (algebraMap W Ω) (eval xW (derivative fW)) = d
    rw [show derivative fW = (derivative f).map (toW hk) from derivative_map _ _,
      ← Polynomial.eval₂_hom, eval₂_map]
    rfl
  have hd0 : d ≠ 0 := hsep.aeval_derivative_ne_zero (minpoly.aeval k x)
  have hdint : IsIntegral k d := by
    have hx' : x ∈ integralClosure k Ω := hxi
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx')
      (Polynomial.aeval_mem_adjoin_singleton k x)
  have hdW' : d⁻¹ ∈ W := mem_of_isIntegral hk hdint.inv
  have hvd : W.valuation d = 1 :=
    valuation_eq_one_of_mem (hd ▸ (gW.eval xW).2) hdW' hd0
  -- `x - σx ∣ g(x) - g(σx) = g(x)` in `W`, and `v(σx - x) < 1`
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub xW sW gW
  rw [hgs, sub_zero] at hc
  have hlt : W.valuation (σ x - x) < 1 :=
    (show ∀ a ∈ W, W.valuation (σ a - a) < 1 from hσ) x xW.2
  have hdeq : d = (c : Ω) * (x - σ x) := by
    rw [← hd, hc, mul_comm]
    rfl
  have hlt' : W.valuation d < 1 := by
    rw [hdeq, map_mul, Valuation.map_sub_swap]
    calc W.valuation (c : Ω) * W.valuation (σ x - x) ≤ 1 * W.valuation (σ x - x) :=
          mul_le_mul_left (W.valuation_le_one c) _
      _ < 1 := by rwa [one_mul]
  rw [hvd] at hlt'
  exact lt_irrefl _ hlt'

end Algebraic

section Global

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- The algebraic closure `k̄` of `k` in `Ω`. -/
abbrev kbar (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] : IntermediateField k Ω :=
  algebraicClosure k Ω

/-- `G_k = Gal(k̄ / k)`. -/
abbrev Gk (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] : Type u :=
  Gal(kbar k Ω / k)

instance isAlgClosed_kbar : IsAlgClosed (kbar k Ω) := IsAlgClosure.isAlgClosed k

variable {D} in
omit [IsAlgClosed Ω] in
/-- **The closed normal subgroup `⟨⟨S⟩⟩` fixes `k̄` pointwise.** -/
theorem eq_of_mem_ambientKernel_of_isAlgebraic {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : σ ∈ GaloisPi1.ambientKernel D.H D.S) {x : Ω} (hx : IsAlgebraic k x) : σ x = x := by
  let St := MulAction.stabilizer (Ω ≃ₐ[K₀ k t] Ω) x
  have hcl : IsClosed (St : Set (Ω ≃ₐ[K₀ k t] Ω)) :=
    Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)
  have hle : GaloisPi1.ambientKernel D.H D.S ≤ St := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hcl
    rw [Subgroup.closure_le]
    rintro _ ⟨h, -, s, hs, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    obtain ⟨-, W, hk, -, hinert⟩ := hs
    have hx' : IsAlgebraic k (h⁻¹ x) :=
      (hx.isIntegral.map ((h⁻¹ : Ω ≃ₐ[K₀ k t] Ω).restrictScalars k).toAlgHom).isAlgebraic
    simp only [AlgEquiv.mul_apply]
    rw [inertia_fix_algebraic hk hinert hx']
    exact h.apply_symm_apply x
  exact hle hσ

/-- `H ≅ Gal(Ω / F) → G_k` (restriction to `k̄`). -/
noncomputable def hToGk : D.H →* Gk k Ω :=
  (galRestrict k (F D) (kbar k Ω) Ω).comp (toGalF D)

theorem continuous_hToGk : Continuous (hToGk D) :=
  (continuous_galRestrict k (F D) (kbar k Ω) Ω).comp continuous_toGalF

omit [IsGalois (K₀ k t) Ω] in
theorem algebraMap_hToGk_apply (h : D.H) (x : kbar k Ω) :
    algebraMap (kbar k Ω) Ω (hToGk D h x) = (h : Ω ≃ₐ[K₀ k t] Ω) x :=
  algebraMap_galRestrict_apply (toGalF D h) x

/-- **The arithmetic quotient `Π_U → G_k`** (restriction to the constants `k̄`). -/
noncomputable def piToGk : Pi D →* Gk k Ω :=
  QuotientGroup.lift _ (hToGk D) fun σ hσ => by
    ext x
    change algebraMap (kbar k Ω) Ω (hToGk D σ x) = (x : Ω)
    rw [algebraMap_hToGk_apply]
    exact eq_of_mem_ambientKernel_of_isAlgebraic hσ (mem_algebraicClosure_iff.mp x.2)

@[simp]
theorem piToGk_mk (h : D.H) : piToGk D (h : Pi D) = hToGk D h := rfl

theorem continuous_piToGk : Continuous (piToGk D) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_hToGk D)

theorem muMap_piToGk_smul (n : ℕ) [NeZero n] (g : Pi D) (ζ : Mu n (kbar k Ω)) :
    muMap n (kbar k Ω) Ω (piToGk D g • ζ) = g • muMap n (kbar k Ω) Ω ζ := by
  induction g using QuotientGroup.induction_on with
  | H h => exact muMap_galRestrict_smul n (toGalF D h) ζ

/-- The constant `c ∈ kˣ` as a unit of `U`. -/
def constUnit (c : kˣ) : units D :=
  ⟨Units.map (algebraMap k (F D) : k →* F D) c, by
    constructor
    · change IsIntegral (A₀ k t) (algebraMap k (F D) c)
      rw [IsScalarTower.algebraMap_apply k (A₀ k t) (F D)]
      exact isIntegral_algebraMap
    · change IsIntegral (A₀ k t) (algebraMap k (F D) ↑c⁻¹)
      rw [IsScalarTower.algebraMap_apply k (A₀ k t) (F D)]
      exact isIntegral_algebraMap⟩

/-- **Kummer classes of constants come from `G_k`**: `κ_U(c)` is the pull-back along
`Π_U → G_k` of the Kummer class `κ_k(c) ∈ H¹(G_k, μ_n(k̄))` (the first map of the exact
sequence of [AbsTopIII] Prop. 1.6(iii), on Kummer classes). -/
theorem kummerMap_const (n : ℕ) [NeZero n] (c : kˣ) :
    kummerMap D n (constUnit D c) =
      ContH1.map (piToGk D) (continuous_piToGk D) (muMap n (kbar k Ω) Ω)
        continuous_of_discreteTopology (muMap_piToGk_smul D n) (kummer n k (kbar k Ω) c) := by
  apply ContH1.inflation_injective (N := GaloisPi1.kernel D.H D.S) (fun _ _ => rfl)
  rw [inflation_kummerMap]
  have h := restriction_kummer (K := k) (L := F D) (ΩK := kbar k Ω) (ΩL := Ω) n c
  change resMu D n (kummer n (F D) Ω (Units.map (algebraMap k (F D) : k →* F D) c)) = _
  rw [← h]
  induction kummer n k (kbar k Ω) c using ContH1.induction_on with
  | h c' => rfl

/-- **`Π_U → G_k` is surjective** (the homotopy exact sequence's `Π_U ↠ G_k`, in the Galois model)
when `k` is algebraically closed in `F` (`U` geometrically connected): the fixed field of the
(closed) image of `Gal(Ω / F)` in `G_k` is `k̄ ∩ F = k`. -/
theorem hToGk_surjective
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    Function.Surjective (hToGk D) := by
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  set I := (hToGk D).range
  have hIcl : IsClosed (I : Set (Gk k Ω)) := by
    have : (I : Set (Gk k Ω)) = Set.range (hToGk D) := MonoidHom.coe_range _
    rw [this]
    exact (isCompact_range (continuous_hToGk D)).isClosed
  have hfix : IntermediateField.fixedField I = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [IntermediateField.mem_fixedField_iff] at hy
    have hyF : (y : Ω) ∈ F D := by
      rw [IntermediateField.mem_fixedField_iff]
      intro h hh
      have := hy (hToGk D ⟨h, hh⟩) ⟨_, rfl⟩
      have h2 := congrArg (algebraMap (kbar k Ω) Ω) this
      rw [algebraMap_hToGk_apply] at h2
      exact h2
    obtain ⟨c, hc⟩ := hk ⟨_, hyF⟩ (by
      have := mem_algebraicClosure_iff.mp y.2
      exact (isAlgebraic_algHom_iff ((F D).val.restrictScalars k)
        Subtype.val_injective).mp this)
    refine IntermediateField.mem_bot.mpr ⟨c, ?_⟩
    apply Subtype.ext
    have := congrArg (fun z : F D => (z : Ω)) hc
    exact this
  have hI : I = ⊤ := by
    have := InfiniteGalois.fixingSubgroup_fixedField ⟨I, hIcl⟩
    change (IntermediateField.fixedField I).fixingSubgroup = I at this
    rw [hfix, IntermediateField.fixingSubgroup_bot] at this
    exact this.symm
  intro g
  have : g ∈ I := hI ▸ Subgroup.mem_top g
  exact this

theorem piToGk_surjective
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    Function.Surjective (piToGk D) := by
  intro g
  obtain ⟨h, rfl⟩ := hToGk_surjective D hk g
  exact ⟨h, rfl⟩

omit [CharZero k] [IsAlgClosed Ω] in
/-- `μ_n(k̄) → μ_n(Ω)` is surjective: roots of unity are algebraic. -/
theorem muMap_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (muMap n (kbar k Ω) Ω) := by
  intro ζ
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hζ : ((Mu.val ζ : Ωˣ) : Ω) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]
  have halg : IsAlgebraic k ((Mu.val ζ : Ωˣ) : Ω) :=
    ⟨X ^ n - 1, X_pow_sub_C_ne_zero hn 1, by simp [hζ]⟩
  set y : kbar k Ω := ⟨_, mem_algebraicClosure_iff.mpr halg⟩
  have hy0 : y ≠ 0 := fun h => (Mu.val ζ).ne_zero (congrArg Subtype.val h)
  have hyn : Units.mk0 y hy0 ^ n = 1 := by
    apply Units.ext
    apply Subtype.ext
    simp [y, hζ]
  refine ⟨Mu.mk _ hyn, Mu.ext (Units.ext ?_)⟩
  rfl

omit [CharZero k] [IsAlgClosed Ω] in
theorem muMap_injective (n : ℕ) : Function.Injective (muMap n (kbar k Ω) Ω) := by
  intro a b h
  apply Mu.ext
  apply Units.ext
  apply Subtype.ext
  have := congrArg (fun z : Mu n Ω => ((Mu.val z : Ωˣ) : Ω)) h
  exact this

/-- **[AbsTopIII] Prop. 1.6(iii), first map, at level `n`**: for `k` algebraically closed in `F`,
the Kummer class in `H¹(Π_U, μ_n)` of a constant `c ∈ kˣ` is trivial iff `c ∈ (kˣ)ⁿ`; i.e.
`kˣ / (kˣ)ⁿ → H¹(Π_U, μ_n)` is injective. -/
theorem kummerMap_const_eq_one_iff
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (n : ℕ) [NeZero n] (c : kˣ) :
    kummerMap D n (constUnit D c) = 1 ↔ c ∈ (powMonoidHom n : kˣ →* kˣ).range := by
  rw [kummerMap_const, ← ker_kummer n k (kbar k Ω), MonoidHom.mem_ker]
  constructor
  · intro h
    induction hx : kummer n k (kbar k Ω) c using ContH1.induction_on with
    | h c' =>
      rw [hx, ContH1.map_mk, ContH1.mk_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      obtain ⟨m', rfl⟩ := muMap_surjective (k := k) (Ω := Ω) n m
      rw [ContH1.mk_eq_one_iff]
      refine ⟨m', fun g => ?_⟩
      obtain ⟨p, rfl⟩ := piToGk_surjective D hk g
      apply muMap_injective (k := k) (Ω := Ω) n
      rw [_root_.map_div, muMap_piToGk_smul]
      exact hm p
  · intro h
    rw [h, map_one]

end Global

end Curve

end KummerTheory
