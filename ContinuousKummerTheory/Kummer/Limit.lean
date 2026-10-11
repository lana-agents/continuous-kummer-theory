/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Equiv

/-!
# The inverse-limit form of Kummer theory: `H¹_cont(G_K, Ẑ(1)) ≃ (Kˣ)^∧`

Let `K` be a field with separable closure `Ω`. We index by the set `KummerTheory.KummerIndex K`
of natural numbers `n` invertible in `K`, ordered by divisibility (a directed set).

* `KummerTheory.ZHatOne K Ω = lim_n μ_n(Ω)` is the Tate twist `Ẑ(1)` (the prime-to-`p` part if
  `char K = p > 0`), with the inverse-limit (profinite) topology and the Galois action.
* `KummerTheory.KummerCompletion K = lim_n Kˣ/(Kˣ)ⁿ` is the Kummer completion `(Kˣ)^∧` of `Kˣ`.
* `KummerTheory.H1Limit K Ω = lim_n H¹_cont(G_K, μ_n)`.

## Main results

* `KummerTheory.h1Transition_kummer` : the Kummer maps are compatible with the transition maps
  `μ_n → μ_m`, `ζ ↦ ζ^{n/m}` and `Kˣ/(Kˣ)ⁿ → Kˣ/(Kˣ)ᵐ` for `m ∣ n`.
* `KummerTheory.kummerLimitEquiv : KummerCompletion K ≃* H1Limit K Ω`.
* `KummerTheory.h1ZHatOneEquiv : ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃* H1Limit K Ω`: continuous
  cohomology commutes with the inverse limit `Ẑ(1) = lim μ_n`. This uses only that the `μ_n` are
  finite (a compactness / König argument, `KummerTheory.exists_compatible_family`), so that the
  relevant `lim¹` terms vanish.
* `KummerTheory.kummerZHatEquiv : ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃* KummerCompletion K`, the
  inverse-limit form of Kummer theory `H¹_cont(G_K, Ẑ(1)) ≃ (Kˣ)^∧`.

These hold for every field `K`: no finiteness of `Kˣ/(Kˣ)ⁿ` is needed. When all `Kˣ/(Kˣ)ⁿ` are
finite and `char K = 0` (e.g. `K` a `p`-adic field), `(Kˣ)^∧` is the profinite completion of `Kˣ`;
that comparison is in `ContinuousKummerTheory.Kummer.ProfiniteCompletion` (with the finiteness for
`p`-adic fields in `ContinuousKummerTheory.Kummer.PAdic`).
-/

open CategoryTheory groupCohomology

/-- A König-type lemma: an inverse system of finite nonempty sets indexed by a directed preorder
has a compatible family of elements. -/
theorem KummerTheory.exists_compatible_family {J : Type*} [Preorder J] [IsDirectedOrder J]
    (T : J → Type*) [∀ j, Finite (T j)] [∀ j, Nonempty (T j)] (f : ∀ i j, i ≤ j → T j → T i)
    (hid : ∀ i x, f i i le_rfl x = x)
    (hcomp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x) :
    ∃ s : ∀ j, T j, ∀ i j (h : i ≤ j), f i j h (s j) = s i := by
  let F : Jᵒᵖ ⥤ Type _ :=
    { obj := fun i => T i.unop
      map := fun {i j} h => TypeCat.ofHom (f j.unop i.unop (leOfHom h.unop))
      map_id := fun i => by ext x; exact hid _ x
      map_comp := fun {i j k} g h => by ext x; exact (hcomp _ _ _ _ _ x).symm }
  haveI : ∀ j : Jᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (T j.unop))
  haveI : ∀ j : Jᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (T j.unop))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  exact ⟨fun j => s (Opposite.op j), fun i j h => hs (homOfLE h).op⟩

namespace KummerTheory

section Transition

variable {K Ω : Type*} [Field K] [Field Ω]

/-- The transition map `μ_n → μ_m`, `ζ ↦ ζ^{n/m}`, for `m ∣ n`. -/
def Mu.transition {m n : ℕ} (h : m ∣ n) : Mu n Ω →* Mu m Ω where
  toFun ζ := Mu.mk (Mu.val ζ ^ (n / m)) (by rw [← pow_mul, Nat.div_mul_cancel h, Mu.val_pow_n])
  map_one' := Mu.ext (by simp)
  map_mul' a b := Mu.ext (by simp [mul_pow])

@[simp]
theorem Mu.val_transition {m n : ℕ} (h : m ∣ n) (ζ : Mu n Ω) :
    Mu.val (Mu.transition h ζ) = Mu.val ζ ^ (n / m) := rfl

theorem Mu.transition_self {n : ℕ} (hn : n ≠ 0) (ζ : Mu n Ω) :
    Mu.transition (dvd_refl n) ζ = ζ :=
  Mu.ext (by simp [Nat.div_self (Nat.pos_of_ne_zero hn)])

theorem Mu.transition_transition {l m n : ℕ} (h1 : l ∣ m) (h2 : m ∣ n) (ζ : Mu n Ω) :
    Mu.transition h1 (Mu.transition h2 ζ) = Mu.transition (h1.trans h2) ζ :=
  Mu.ext (by simp [← pow_mul, Nat.div_mul_div h2 h1])

variable [Algebra K Ω]

theorem Mu.transition_smul {m n : ℕ} (h : m ∣ n) (σ : Gal(Ω/K)) (ζ : Mu n Ω) :
    Mu.transition h (σ • ζ) = σ • Mu.transition h ζ :=
  Mu.ext (by simp [smul_pow'])

variable (K Ω) in
/-- The transition map `H¹_cont(G_K, μ_n) → H¹_cont(G_K, μ_m)` for `m ∣ n`. -/
noncomputable def h1Transition {m n : ℕ} (h : m ∣ n) :
    ContH1 Gal(Ω/K) (Mu n Ω) →* ContH1 Gal(Ω/K) (Mu m Ω) :=
  ContH1.map (MonoidHom.id _) continuous_id (Mu.transition h) continuous_of_discreteTopology
    (fun σ ζ => Mu.transition_smul h σ ζ)

variable (K) in
/-- The transition map `Kˣ/(Kˣ)ⁿ → Kˣ/(Kˣ)ᵐ` for `m ∣ n`. -/
def quotTransition {m n : ℕ} (h : m ∣ n) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range →* Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range :=
  QuotientGroup.map _ _ (MonoidHom.id _) <| by
    rintro _ ⟨b, rfl⟩
    exact ⟨b ^ (n / m), by simp [← pow_mul, Nat.div_mul_cancel h]⟩

/-- The Kummer maps for `n` and `m ∣ n` are compatible with the transition maps. -/
theorem h1Transition_kummer [Algebra.IsIntegral K Ω] {m n : ℕ} (h : m ∣ n)
    [HasKummerRoots n K Ω] [HasKummerRoots m K Ω] (a : Kˣ) :
    h1Transition K Ω h (kummer n K Ω a) = kummer m K Ω a := by
  set α := kummerRoot n K Ω a
  have hα := kummerRoot_pow n K Ω a
  have hβ : (α ^ (n / m)) ^ m = Units.map (algebraMap K Ω : K →* Ω) a := by
    rw [← pow_mul, Nat.div_mul_cancel h, hα]
  rw [kummer_eq a α hα, kummer_eq a _ hβ, h1Transition, ContH1.map_mk]
  congr 1
  apply Subtype.ext
  funext σ
  apply Mu.ext
  simp [smul_pow', div_pow]

theorem kummerEquiv_quotTransition [IsGalois K Ω] {m n : ℕ} (h : m ∣ n)
    [HasKummerRoots n K Ω] [HasKummerRoots m K Ω]
    (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :
    h1Transition K Ω h (kummerEquiv n K Ω x) = kummerEquiv m K Ω (quotTransition K h x) := by
  induction x using QuotientGroup.induction_on with
  | H a => exact h1Transition_kummer h a

end Transition

section Index

variable (K : Type*) [Field K]

/-- The natural numbers invertible in `K`, ordered by divisibility. -/
structure KummerIndex where
  /-- The underlying natural number. -/
  n : ℕ
  ne_zero : (n : K) ≠ 0

namespace KummerIndex

variable {K}

instance : Preorder (KummerIndex K) where
  le i j := i.n ∣ j.n
  le_refl i := dvd_refl i.n
  le_trans _ _ _ h₁ h₂ := dvd_trans h₁ h₂

theorem le_def {i j : KummerIndex K} : i ≤ j ↔ i.n ∣ j.n := Iff.rfl

instance : IsDirectedOrder (KummerIndex K) :=
  ⟨fun i j => ⟨⟨i.n * j.n, by push_cast; exact mul_ne_zero i.ne_zero j.ne_zero⟩,
    dvd_mul_right i.n j.n, dvd_mul_left j.n i.n⟩⟩

instance : Nonempty (KummerIndex K) := ⟨⟨1, by simp⟩⟩

theorem n_ne_zero (i : KummerIndex K) : i.n ≠ 0 := fun h => i.ne_zero (by simp [h])

instance (i : KummerIndex K) : NeZero (i.n : K) := ⟨i.ne_zero⟩

instance (i : KummerIndex K) : NeZero i.n := ⟨i.n_ne_zero⟩

end KummerIndex

/-- The **Kummer completion** `(Kˣ)^∧ = lim_n Kˣ/(Kˣ)ⁿ` of `Kˣ`, the limit over the `n`
invertible in `K` ordered by divisibility. -/
def KummerCompletion :
    Subgroup (∀ i : KummerIndex K, Kˣ ⧸ (powMonoidHom i.n : Kˣ →* Kˣ).range) where
  carrier := {x | ∀ i j (h : i ≤ j), quotTransition K h (x j) = x i}
  mul_mem' hx hy i j h := by simp [hx i j h, hy i j h]
  one_mem' _ _ h := by simp
  inv_mem' hx i j h := by simp [hx i j h]

/-- The canonical map `Kˣ → (Kˣ)^∧`. -/
def toKummerCompletion : Kˣ →* KummerCompletion K :=
  (MonoidHom.pi fun _ => QuotientGroup.mk' _).codRestrict _ fun _ _ _ _ => rfl

end Index

section ZHat

variable (K Ω : Type*) [Field K] [Field Ω]

/-- The Tate twist `Ẑ(1) = lim_n μ_n(Ω)`, over the `n` invertible in `K` (for `char K = p > 0`
this is the prime-to-`p` part), with the inverse-limit topology. -/
def ZHatOne : Subgroup (∀ i : KummerIndex K, Mu i.n Ω) where
  carrier := {x | ∀ i j (h : i ≤ j), Mu.transition h (x j) = x i}
  mul_mem' hx hy i j h := by simp [hx i j h, hy i j h]
  one_mem' i j h := by simp
  inv_mem' hx i j h := by simp [hx i j h]

namespace ZHatOne

variable {K Ω}

/-- The projection `Ẑ(1) → μ_n`. -/
def proj (i : KummerIndex K) : ZHatOne K Ω →* Mu i.n Ω :=
  (Pi.evalMonoidHom _ i).comp (ZHatOne K Ω).subtype

@[simp]
theorem proj_apply (i : KummerIndex K) (x : ZHatOne K Ω) : proj i x = (x : ∀ i, Mu i.n Ω) i :=
  rfl

theorem continuous_proj (i : KummerIndex K) : Continuous (proj i : ZHatOne K Ω → Mu i.n Ω) :=
  (continuous_apply i).comp continuous_subtype_val

theorem transition_proj {i j : KummerIndex K} (h : i ≤ j) (x : ZHatOne K Ω) :
    Mu.transition h (proj j x) = proj i x := x.2 i j h

variable {F : Type*} [Field F] [Algebra F Ω]

instance : MulDistribMulAction Gal(Ω/F) (ZHatOne K Ω) where
  smul σ x := ⟨fun i => σ • (x : ∀ i, Mu i.n Ω) i, fun i j h => by
    rw [Mu.transition_smul, x.2 i j h]⟩
  one_smul x := Subtype.ext (funext fun i => one_smul _ _)
  mul_smul σ τ x := Subtype.ext (funext fun i => mul_smul σ τ _)
  smul_mul σ x y := Subtype.ext (funext fun i => smul_mul' σ _ _)
  smul_one σ := Subtype.ext (funext fun i => smul_one σ)

@[simp]
theorem coe_smul_apply (σ : Gal(Ω/F)) (x : ZHatOne K Ω) (i : KummerIndex K) :
    (σ • x : ∀ i, Mu i.n Ω) i = σ • (x : ∀ i, Mu i.n Ω) i := rfl

theorem proj_smul (i : KummerIndex K) (σ : Gal(Ω/F)) (x : ZHatOne K Ω) :
    proj i (σ • x) = σ • proj i x := rfl

end ZHatOne

end ZHat

section Limit

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- `lim_n H¹_cont(G_K, μ_n)`. -/
noncomputable def H1Limit :
    Subgroup (∀ i : KummerIndex K, ContH1 Gal(Ω/K) (Mu i.n Ω)) where
  carrier := {x | ∀ i j (h : i ≤ j), h1Transition K Ω h (x j) = x i}
  mul_mem' hx hy i j h := by simp [hx i j h, hy i j h]
  one_mem' i j h := by simp
  inv_mem' hx i j h := by simp [hx i j h]

variable [IsGalois K Ω] [IsSepClosed Ω]

/-- The inverse limit of the Kummer isomorphisms: `(Kˣ)^∧ ≃ lim_n H¹_cont(G_K, μ_n)`. -/
noncomputable def kummerLimitEquiv : KummerCompletion K ≃* H1Limit K Ω where
  toFun x := ⟨fun i => kummerEquiv i.n K Ω (x.1 i), fun i j h => by
    change h1Transition K Ω h (kummerEquiv j.n K Ω (x.1 j)) = kummerEquiv i.n K Ω (x.1 i)
    rw [kummerEquiv_quotTransition, x.2 i j h]⟩
  invFun y := ⟨fun i => (kummerEquiv i.n K Ω).symm (y.1 i), fun i j h => by
    change quotTransition K h ((kummerEquiv j.n K Ω).symm (y.1 j)) =
      (kummerEquiv i.n K Ω).symm (y.1 i)
    apply (kummerEquiv i.n K Ω).injective
    rw [← kummerEquiv_quotTransition, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      y.2 i j h]⟩
  left_inv x := Subtype.ext (funext fun i => (kummerEquiv i.n K Ω).symm_apply_apply (x.1 i))
  right_inv y := Subtype.ext (funext fun i => (kummerEquiv i.n K Ω).apply_symm_apply (y.1 i))
  map_mul' x y := Subtype.ext (funext fun i => map_mul (kummerEquiv i.n K Ω) (x.1 i) (y.1 i))

@[simp]
theorem kummerLimitEquiv_apply (x : KummerCompletion K) (i : KummerIndex K) :
    (kummerLimitEquiv K Ω x).1 i = kummerEquiv i.n K Ω (x.1 i) := rfl

end Limit

end KummerTheory
