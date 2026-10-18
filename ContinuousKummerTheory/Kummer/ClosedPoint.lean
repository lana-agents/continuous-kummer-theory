/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.DecompositionSurjective
import ContinuousKummerTheory.Kummer.Faithful

/-!
# Kummer classes on the decomposition group of a closed point

Let `Ω / F` be an algebraic extension, `k ⊆ F`, and `A ⊆ Ω` a valuation subring containing `k`
(a place of `Ω` above a closed point `x` of a curve with function field `F`). The point need not
be rational: its residue field is `k_x = κ(A ∩ F)`, which we realise inside `κ(A)` as the set
of residues of the elements of `A ∩ F` (`KummerTheory.Decomposition.pointField`).

[AbsTopIII] Prop. 1.8 (`T3` l.2061–2098) restricts Kummer classes `η` to points `x ∈ U(k_x)`
over finite extensions `k_x / k`, `η|_x = s_x^*(η) ∈ H¹(G_{k_x}, M_X)`. Since `D_A → Π_U` factors
through `D_A ↠ G_{k_x}` and inflation is injective in degree one, `η|_x = 0` iff the restriction
of `η` to `D_A` vanishes. Here we treat the restriction to `D_A` of the Kummer class `κ_F(f)` of
a function `f` which is a unit at `A`, with coefficients reduced modulo `𝔪_A`:

* `KummerTheory.Decomposition.decomposition_kummer_eq_one_iff`: the restriction of `κ_F(f)` to
  `D_A` at level `n` vanishes iff `f(x) = f̄` is an `n`-th power of an element of `κ(A)` fixed by
  `D_A`;
* `KummerTheory.Decomposition.mem_pointField_iff`: for `Ω` algebraically closed and `Ω / F`
  Galois, the elements of `κ(A)` fixed by `D_A` are exactly `k_x` (`G_{k_x}` is the image of
  `D_A`, `exists_decompositionMap_eq_of_fixes`, plus infinite Galois theory);
* `KummerTheory.Decomposition.forall_decomposition_kummer_eq_one_iff`: if `k_x` is
  Kummer-faithful for `𝔾_m` (e.g. `k` torally Kummer-faithful and `[k_x : k] < ∞`,
  `KummerTheory.Decomposition.isKummerFaithfulGm_pointField`), the restrictions vanish at all
  levels iff `f(x) = 1`.
-/

universe u

open IsLocalRing groupCohomology

namespace KummerTheory

namespace Decomposition

variable {k : Type*} (F : Type*) {Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra k F]
  [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω] (A : ValuationSubring Ω)
  (hk : ∀ c : k, algebraMap k Ω c ∈ A) [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

section PointField

include hkres in
theorem algebraMap_mem_pointField (c : k) :
    ∃ (a : F) (ha : algebraMap F Ω a ∈ A), residue A ⟨_, ha⟩ = algebraMap k (ResidueField A) c :=
  ⟨algebraMap k F c, by rw [← IsScalarTower.algebraMap_apply]; exact hk c, by
    rw [← hkres]
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply k F Ω c).symm⟩

/-- **The residue field `k_x = κ(A ∩ F)` of the closed point below `A`**, as the subfield of
`κ(A)` consisting of the residues of the elements of `A ∩ F`. -/
def pointField : IntermediateField k (ResidueField A) where
  carrier := {y | ∃ (a : F) (ha : algebraMap F Ω a ∈ A), residue A ⟨_, ha⟩ = y}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    have hab : algebraMap F Ω (a * b) ∈ A := by rw [map_mul]; exact A.mul_mem _ _ ha hb
    refine ⟨a * b, hab, ?_⟩
    have e : (⟨_, hab⟩ : A) = ⟨_, ha⟩ * ⟨_, hb⟩ := Subtype.ext (map_mul _ a b)
    rw [e, map_mul]
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    have hab : algebraMap F Ω (a + b) ∈ A := by rw [map_add]; exact A.add_mem _ _ ha hb
    refine ⟨a + b, hab, ?_⟩
    have e : (⟨_, hab⟩ : A) = ⟨_, ha⟩ + ⟨_, hb⟩ := Subtype.ext (map_add _ a b)
    rw [e, map_add]
  algebraMap_mem' c := algebraMap_mem_pointField F A hk hkres c
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    by_cases h0 : residue A ⟨_, ha⟩ = 0
    · have h00 : algebraMap F Ω 0 ∈ A := by rw [map_zero]; exact A.zero_mem
      refine ⟨0, h00, ?_⟩
      have e : (⟨_, h00⟩ : A) = 0 := Subtype.ext (map_zero _)
      rw [h0, inv_zero, e, map_zero]
    · have hunit : IsUnit (⟨_, ha⟩ : A) := by
        by_contra hu
        exact h0 ((residue_eq_zero_iff _).2 hu)
      have ha0 : algebraMap F Ω a ≠ 0 := fun h => h0 (by
        have : (⟨_, ha⟩ : A) = 0 := Subtype.ext h
        rw [this, map_zero])
      have hinv : algebraMap F Ω a⁻¹ ∈ A := by
        rw [map_inv₀]
        obtain ⟨u, hu⟩ := hunit
        have : ((u⁻¹ : Aˣ) : A) * ⟨_, ha⟩ = 1 := by rw [← hu, Units.inv_mul]
        have h' : (((u⁻¹ : Aˣ) : A) : Ω) = (algebraMap F Ω a)⁻¹ :=
          eq_inv_of_mul_eq_one_left (congrArg Subtype.val this)
        rw [← h']
        exact ((u⁻¹ : Aˣ) : A).2
      refine ⟨a⁻¹, hinv, eq_inv_of_mul_eq_one_left ?_⟩
      have : (⟨_, hinv⟩ : A) * ⟨_, ha⟩ = 1 := by
        apply Subtype.ext
        change algebraMap F Ω a⁻¹ * algebraMap F Ω a = 1
        rw [← map_mul, inv_mul_cancel₀ (fun h => ha0 (by rw [h, map_zero])), map_one]
      rw [← map_mul, this, map_one]

variable {F A hk hkres} in
theorem mem_pointField {y : ResidueField A} :
    y ∈ pointField F A hk hkres ↔ ∃ (a : F) (ha : algebraMap F Ω a ∈ A), residue A ⟨_, ha⟩ = y :=
  Iff.rfl

theorem residue_mem_pointField (a : F) (ha : algebraMap F Ω a ∈ A) :
    residue A ⟨_, ha⟩ ∈ pointField F A hk hkres :=
  ⟨a, ha, rfl⟩

/-- The decomposition group acts trivially on `k_x`. -/
theorem decompositionMap_apply_of_mem_pointField (σ : A.decompositionSubgroup F)
    {y : ResidueField A} (hy : y ∈ pointField F A hk hkres) :
    decompositionMap F A hk hkres σ y = y := by
  obtain ⟨a, ha, rfl⟩ := hy
  rw [decompositionMap_residue]
  congr 1
  apply Subtype.ext
  change (σ : Ω ≃ₐ[F] Ω) (algebraMap F Ω a) = algebraMap F Ω a
  exact AlgEquiv.commutes _ a

/-- **`G_{k_x}` is the image of `D_A`**: the image of `D_A → Gal(κ(A)/k)` is the subgroup fixing
`k_x` ([AbsTopIII] Prop. 1.8: the decomposition group of a closed point `x` surjects onto
`G_{k_x}`). -/
theorem range_decompositionMap [IsAlgClosed Ω] [IsGalois F Ω]
    [Algebra.IsIntegral k (ResidueField A)] :
    (decompositionMap F A hk hkres).range = (pointField F A hk hkres).fixingSubgroup := by
  ext τ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨σ, rfl⟩ y hy
    exact decompositionMap_apply_of_mem_pointField F A hk hkres σ hy
  · intro h
    exact exists_decompositionMap_eq_of_fixes (F := F) A hk hkres τ fun a ha =>
      h _ (residue_mem_pointField F A hk hkres a ha)

/-- **The elements of `κ(A)` fixed by `D_A` are exactly those of `k_x`.** -/
theorem mem_pointField_iff [IsAlgClosed Ω] [IsGalois F Ω] [Algebra.IsIntegral k (ResidueField A)]
    [IsGalois k (ResidueField A)] (y : ResidueField A) :
    y ∈ pointField F A hk hkres ↔ ∀ σ, decompositionMap F A hk hkres σ y = y := by
  constructor
  · intro hy σ
    exact decompositionMap_apply_of_mem_pointField F A hk hkres σ hy
  · intro h
    rw [← InfiniteGalois.fixedField_fixingSubgroup (pointField F A hk hkres),
      ← range_decompositionMap F A hk hkres, IntermediateField.mem_fixedField_iff]
    rintro _ ⟨σ, rfl⟩
    exact h σ

end PointField

section Faithful

variable {k F Ω : Type u} [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A)
  [Algebra k (ResidueField A)]
  (hkres : ∀ c : k, residue A ⟨algebraMap k Ω c, hk c⟩ = algebraMap k (ResidueField A) c)

/-- If `k` is torally Kummer-faithful and `k_x / k` is finite, `k_x` is Kummer-faithful for
`𝔾_m` ([AbsTopIII] Rem. 1.5.4, Def. 1.5 for finite extensions). -/
theorem isKummerFaithfulGm_pointField (htf : IsTorallyKummerFaithful k)
    [FiniteDimensional k (pointField F A hk hkres)] :
    IsKummerFaithfulGm (pointField F A hk hkres) :=
  htf _

end Faithful

section Kummer

variable (n : ℕ) (hn : n ≠ 0)

/-- The residue of a unit `β` of `Ω` with `β, β⁻¹ ∈ A`. -/
theorem residue_mul_residue_inv (β : Ωˣ) (hβ : (β : Ω) ∈ A) (hβ' : ((β⁻¹ : Ωˣ) : Ω) ∈ A) :
    residue A ⟨_, hβ⟩ * residue A ⟨_, hβ'⟩ = 1 := by
  rw [← map_mul, ← map_one (residue A)]
  congr 1
  exact Subtype.ext (by simp)

include hn in
/-- The reduction of `σ α / α` is `σ̄(ᾱ) / ᾱ`. -/
theorem val_reduceMu_div (σ : A.decompositionSubgroup F) (α : Ωˣ) (hα : (α : Ω) ∈ A)
    (hα' : ((α⁻¹ : Ωˣ) : Ω) ∈ A) (h : ((σ : Ω ≃ₐ[F] Ω) • α / α) ^ n = 1) :
    ((Mu.val (reduceMu A n hn (Mu.mk _ h)) : (ResidueField A)ˣ) : ResidueField A) =
      decompositionMap F A hk hkres σ (residue A ⟨_, hα⟩) * residue A ⟨_, hα'⟩ := by
  rw [reduceMu, coe_val_specMu, decompositionMap_residue, ← map_mul]
  congr 1

variable [Algebra.IsIntegral F Ω] [HasKummerRoots n F Ω]

include hn in
/-- **The restriction of a Kummer class to the decomposition group of a closed point**
([AbsTopIII] Prop. 1.8, `η|_x`): for `f ∈ Fˣ` a unit at `A`, the restriction of `κ_F(f)` to
`D_A`, with coefficients reduced modulo `𝔪_A`, is trivial iff the value `f̄ = f(x)` is an `n`-th
power of an element of `κ(A)` fixed by `D_A` (i.e. of `k_x`, `mem_pointField_iff`). -/
theorem decomposition_kummer_eq_one_iff (f : Fˣ) (hf : algebraMap F Ω f ∈ A)
    (hf' : algebraMap F Ω ↑f⁻¹ ∈ A) :
    letI := muAction F A hk hkres n
    ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val (reduceMu A n hn)
        continuous_of_discreteTopology (reduceMu_smul F A hk hkres n hn) (kummer n F Ω f) = 1 ↔
      ∃ b : ResidueField A, (∀ σ, decompositionMap F A hk hkres σ b = b) ∧
        b ^ n = residue A ⟨_, hf⟩ := by
  letI := muAction F A hk hkres n
  obtain ⟨α, hα⟩ := HasKummerRoots.exists_pow_eq (n := n) (K := F) (Ω := Ω) f
  have hαn : (α : Ω) ^ n = algebraMap F Ω f := by
    rw [← Units.val_pow_eq_pow_val, hα]
    rfl
  have hαn' : ((α⁻¹ : Ωˣ) : Ω) ^ n = algebraMap F Ω ↑f⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hα]
    rfl
  have hαA : (α : Ω) ∈ A := mem_of_pow_mem_toSubring A n hn _ (by rw [hαn]; exact hf)
  have hαA' : ((α⁻¹ : Ωˣ) : Ω) ∈ A := mem_of_pow_mem_toSubring A n hn _ (by rw [hαn']; exact hf')
  set a := residue A ⟨_, hαA⟩ with ha_def
  set a' := residue A ⟨_, hαA'⟩ with ha'_def
  have haa' : a * a' = 1 := residue_mul_residue_inv A α hαA hαA'
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one haa'
  have ha' : a' = a⁻¹ := (eq_inv_of_mul_eq_one_right haa')
  have hfa : residue A ⟨_, hf⟩ = a ^ n := by
    rw [ha_def, ← map_pow]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact hαn.symm
  have hred : ∀ σ : A.decompositionSubgroup F,
      ((Mu.val (reduceMu A n hn (kummerFun α (smul_pow_of_pow_eq hα) σ.1)) :
        (ResidueField A)ˣ) : ResidueField A) = decompositionMap F A hk hkres σ a / a := by
    intro σ
    rw [div_eq_mul_inv, ← ha']
    exact val_reduceMu_div F A hk hkres n hn σ α hαA hαA' _
  rw [kummer_eq f α hα, ContH1.map_mk, ContH1.mk_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨a / ((Mu.val m : (ResidueField A)ˣ) : ResidueField A), fun σ => ?_, ?_⟩
    · have h := congrArg (fun ζ : Mu n (ResidueField A) =>
        ((Mu.val ζ : (ResidueField A)ˣ) : ResidueField A)) (hm σ)
      change ((Mu.val (σ • m / m) : (ResidueField A)ˣ) : ResidueField A) =
        ((Mu.val (reduceMu A n hn (kummerFun α (smul_pow_of_pow_eq hα) σ.1)) :
          (ResidueField A)ˣ) : ResidueField A) at h
      rw [hred, map_div, Units.val_div_eq_div_val] at h
      change decompositionMap F A hk hkres σ ((Mu.val m : (ResidueField A)ˣ) : ResidueField A) /
        ((Mu.val m : (ResidueField A)ˣ) : ResidueField A) = _ at h
      have hm0 : ((Mu.val m : (ResidueField A)ˣ) : ResidueField A) ≠ 0 := Units.ne_zero _
      rw [map_div₀]
      rw [div_eq_div_iff hm0 ha0] at h
      rw [div_eq_div_iff ((map_ne_zero _).2 hm0) hm0]
      linear_combination -h
    · rw [div_pow, ← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one, div_one, hfa]
  · rintro ⟨b, hb, hbn⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [hfa, zero_pow hn] at hbn
      exact pow_ne_zero n ha0 hbn.symm
    let u : (ResidueField A)ˣ := Units.mk0 (a / b) (div_ne_zero ha0 hb0)
    have hu : u ^ n = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, div_pow, hbn, hfa, div_self (pow_ne_zero n ha0),
        Units.val_one]
    refine ⟨Mu.mk u hu, fun σ => ?_⟩
    apply Mu.ext
    apply Units.ext
    change ((Mu.val (decompositionMap F A hk hkres σ • Mu.mk u hu / Mu.mk u hu) :
      (ResidueField A)ˣ) : ResidueField A) = _
    rw [ContH1.cocyclesMap_apply]
    change _ = ((Mu.val (reduceMu A n hn (kummerFun α (smul_pow_of_pow_eq hα) σ.1)) :
      (ResidueField A)ˣ) : ResidueField A)
    rw [hred, map_div, Units.val_div_eq_div_val, Mu.val_smul, Mu.val_mk]
    change decompositionMap F A hk hkres σ (a / b) / (a / b) = _
    rw [map_div₀, hb σ, div_div_div_cancel_right₀ hb0]

end Kummer

section Faithful

variable [Algebra.IsIntegral F Ω] (hroots : ∀ (n : ℕ) [NeZero n], HasKummerRoots n F Ω)

include hroots in
/-- **Kummer-faithfulness at a closed point detects `f(x) = 1`** ([AbsTopIII] Prop. 1.8(i),
"`η†|x₁ = 0`", for points over finite extensions `k_x`): let `K ⊆ κ(A)` be a subfield containing
every element fixed by `D_A` (e.g. `K = k_x`, `mem_pointField_iff`) which is Kummer-faithful for
`𝔾_m`. Then the restrictions of `κ_F(f)` to `D_A` vanish at every level `n ≥ 1` iff
`f(x) = 1`. -/
theorem forall_decomposition_kummer_eq_one_iff (K : IntermediateField k (ResidueField A))
    (hK : ∀ y : ResidueField A, (∀ σ, decompositionMap F A hk hkres σ y = y) → y ∈ K)
    (hKf : IsKummerFaithfulGm K) (f : Fˣ)
    (hf : algebraMap F Ω f ∈ A) (hf' : algebraMap F Ω ↑f⁻¹ ∈ A) :
    (∀ (n : ℕ) [NeZero n],
      letI := muAction F A hk hkres n
      haveI := hroots n
      ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
        (reduceMu A n (NeZero.ne n)) continuous_of_discreteTopology
        (reduceMu_smul F A hk hkres n (NeZero.ne n)) (kummer n F Ω f) = 1) ↔
      residue A ⟨_, hf⟩ = 1 := by
  have hfix : ∀ σ, decompositionMap F A hk hkres σ (residue A ⟨_, hf⟩) = residue A ⟨_, hf⟩ :=
    fun σ => decompositionMap_apply_of_mem_pointField F A hk hkres σ
      (residue_mem_pointField F A hk hkres _ hf)
  have hy0 : residue A ⟨_, hf⟩ ≠ 0 := by
    intro h
    have := residue_mul_residue_inv A (Units.map (algebraMap F Ω : F →* Ω) f) hf
      (by simpa using hf')
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    rw [h, zero_mul] at this
    exact zero_ne_one this
  constructor
  · intro h
    have hyK := hK _ hfix
    let yK : Kˣ := Units.mk0 ⟨_, hyK⟩ (fun h0 => hy0 (congrArg Subtype.val h0))
    have : yK = 1 := hKf yK fun N hN => by
      haveI : NeZero N := ⟨hN.ne'⟩
      haveI := hroots N
      obtain ⟨b, hb, hbN⟩ :=
        (decomposition_kummer_eq_one_iff F A hk hkres N (NeZero.ne N) f hf hf').1 (h N)
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [zero_pow (NeZero.ne N)] at hbN
        exact hy0 hbN.symm
      have hbK := hK b hb
      refine ⟨Units.mk0 ⟨b, hbK⟩ (fun h0 => hb0 (congrArg Subtype.val h0)), ?_⟩
      apply Units.ext
      apply Subtype.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow, yK]
      exact hbN
    exact congrArg (fun z : Kˣ => ((z : K) : ResidueField A)) this
  · intro h n _
    haveI := hroots n
    rw [decomposition_kummer_eq_one_iff F A hk hkres n (NeZero.ne n) f hf hf']
    exact ⟨1, fun σ => map_one _, by rw [one_pow, h]⟩

end Faithful

end Decomposition

end KummerTheory
