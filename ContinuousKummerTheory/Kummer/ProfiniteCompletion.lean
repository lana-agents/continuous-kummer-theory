/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.ZHat

/-!
# The Kummer completion is the profinite completion (finite `Kˣ/(Kˣ)ⁿ`, characteristic zero)

If `char K = 0` and every `Kˣ/(Kˣ)ⁿ` (`n ≥ 1`) is finite — e.g. `K` a finite extension of `ℚ_p` —
then the subgroups `(Kˣ)ⁿ` are cofinal among the finite-index subgroups of `Kˣ` (a subgroup of
index `d` contains `(Kˣ)ᵈ`), so the Kummer completion `lim_n Kˣ/(Kˣ)ⁿ` is the profinite completion
of `Kˣ`. We prove this as a group isomorphism with Mathlib's
`ProfiniteGrp.ProfiniteCompletion.completion`, and deduce

`KummerTheory.kummerZHatEquivProfiniteCompletion :`
`  H¹_cont(G_K, Ẑ(1)) ≃* ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ)`.
-/

open CategoryTheory ProfiniteGrp ProfiniteCompletion

namespace KummerTheory

variable (K : Type*) [Field K]

/-- The hypothesis that `Kˣ/(Kˣ)ⁿ` is finite for every `n ≥ 1`. -/
class FiniteKummerQuotients : Prop where
  finiteIndex : ∀ n : ℕ, n ≠ 0 → (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex

variable {K}

/-- The quotient map `Kˣ/A → Kˣ/B` for `A ≤ B`. -/
abbrev qmap {A B : Subgroup Kˣ} (h : A ≤ B) : Kˣ ⧸ A →* Kˣ ⧸ B :=
  QuotientGroup.map A B (MonoidHom.id _) h

theorem qmap_qmap {A B C : Subgroup Kˣ} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : Kˣ ⧸ A) :
    qmap h₂ (qmap h₁ x) = qmap (h₁.trans h₂) x := by
  induction x using QuotientGroup.induction_on with
  | H a => rfl

theorem powRange_le {m n : ℕ} (h : m ∣ n) :
    (powMonoidHom n : Kˣ →* Kˣ).range ≤ (powMonoidHom m : Kˣ →* Kˣ).range := by
  rintro _ ⟨b, rfl⟩
  exact ⟨b ^ (n / m), by simp [← pow_mul, Nat.div_mul_cancel h]⟩

theorem quotTransition_eq_qmap {m n : ℕ} (h : m ∣ n)
    (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :
    quotTransition K h x = qmap (powRange_le h) x := rfl

variable [CharZero K] [FiniteKummerQuotients K]

/-- The finite-index normal subgroup `(Kˣ)ⁿ`. -/
noncomputable def powSubgroup (i : KummerIndex K) : FiniteIndexNormalSubgroup (GrpCat.of Kˣ) :=
  haveI := FiniteKummerQuotients.finiteIndex (K := K) i.n i.n_ne_zero
  haveI : ((powMonoidHom i.n : Kˣ →* Kˣ).range).Normal := Subgroup.normal_of_isMulCommutative _
  FiniteIndexNormalSubgroup.ofSubgroup (powMonoidHom i.n : Kˣ →* Kˣ).range

/-- The index of a finite-index subgroup, as an element of `KummerIndex K`. -/
noncomputable def indexIdx (H : FiniteIndexNormalSubgroup (GrpCat.of Kˣ)) : KummerIndex K :=
  ⟨H.toSubgroup.index, Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero⟩

omit [FiniteKummerQuotients K] in
theorem powRange_index_le (H : FiniteIndexNormalSubgroup (GrpCat.of Kˣ)) :
    (powMonoidHom (indexIdx H).n : Kˣ →* Kˣ).range ≤ H.toSubgroup := by
  rintro _ ⟨b, rfl⟩
  exact Subgroup.pow_index_mem H.toSubgroup b

variable (K) in
/-- For `char K = 0` and all `Kˣ/(Kˣ)ⁿ` finite, the Kummer completion `lim_n Kˣ/(Kˣ)ⁿ` is the
profinite completion of `Kˣ`. -/
noncomputable def kummerCompletionEquivProfiniteCompletion :
    KummerCompletion K ≃* completion (GrpCat.of Kˣ) where
  toFun x := ⟨fun H => qmap (powRange_index_le H) (x.1 (indexIdx H)), fun H H' π => by
    change qmap (leOfHom π) (qmap (powRange_index_le H) (x.1 (indexIdx H))) =
      qmap (powRange_index_le H') (x.1 (indexIdx H'))
    have hdvd : (indexIdx H').n ∣ (indexIdx H).n := Subgroup.index_dvd_of_le (leOfHom π)
    rw [← x.2 (indexIdx H') (indexIdx H) hdvd, quotTransition_eq_qmap, qmap_qmap, qmap_qmap]⟩
  invFun y := ⟨fun i => y.1 (powSubgroup i), fun i j h => by
    change qmap (powRange_le h) (y.1 (powSubgroup j)) = y.1 (powSubgroup i)
    exact y.2 (homOfLE (show powSubgroup j ≤ powSubgroup i from powRange_le h))⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    change qmap (powRange_index_le (powSubgroup i)) (x.1 (indexIdx (powSubgroup i))) = x.1 i
    set d := indexIdx (powSubgroup i)
    let e : KummerIndex K := ⟨i.n * d.n, by push_cast; exact mul_ne_zero i.ne_zero d.ne_zero⟩
    have hd : d ≤ e := dvd_mul_left d.n i.n
    have hi : i ≤ e := dvd_mul_right i.n d.n
    rw [← x.2 d e hd, ← x.2 i e hi, quotTransition_eq_qmap, quotTransition_eq_qmap, qmap_qmap]
    rfl
  right_inv y := by
    apply Subtype.ext
    funext H
    change qmap (powRange_index_le H) (y.1 (powSubgroup (indexIdx H))) = y.1 H
    exact y.2 (homOfLE (show powSubgroup (indexIdx H) ≤ H from powRange_index_le H))
  map_mul' x y := by
    apply Subtype.ext
    funext H
    exact map_mul (qmap (powRange_index_le H)) (x.1 (indexIdx H)) (y.1 (indexIdx H))

variable (K) in
/-- **Kummer theory, profinite form**: for `K` of characteristic zero with all `Kˣ/(Kˣ)ⁿ` finite
(e.g. a `p`-adic field) and `Ω` a separable closure of `K`,
`H¹_cont(G_K, Ẑ(1)) ≃ (Kˣ)^∧`, the profinite completion of `Kˣ`. -/
noncomputable def kummerZHatEquivProfiniteCompletion (Ω : Type*) [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω] :
    ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃* completion (GrpCat.of Kˣ) :=
  (kummerZHatEquiv K Ω).trans (kummerCompletionEquivProfiniteCompletion K)

end KummerTheory
