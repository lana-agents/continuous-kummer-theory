/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.Constants

/-!
# The map `(kˣ)^∧ → H¹(Π_U, Ẑ(1))`

[AbsTopIII] Proposition 1.6(iii) starts with `1 → (kˣ)^∧ → H¹(Π_U, M_X)`, where `(kˣ)^∧` is the
profinite completion of `kˣ` (for `char k = 0`, ckt's `KummerCompletion k = lim kˣ/(kˣ)ⁿ`). We
construct this map as the composite

  `(kˣ)^∧ ≃ H¹(G_k, Ẑ(1)) → H¹(Π_U, Ẑ(1))`

of the inverse of the Kummer isomorphism `kummerZHatEquiv` for `k̄ / k` and the pull-back along
`Π_U ↠ G_k` (with `Ẑ(1)_{k̄} ≅ Ẑ(1)_Ω`, `Curve.zHatMap`), and prove:

* `Curve.constMapZHat_toKummerCompletion`: on `kˣ` it is the Kummer map of `U` on constants;
* `Curve.constMapZHat_injective`: it is injective when `k` is algebraically closed in `F`.
-/

universe u

open groupCohomology AffOrbicurve IntermediateField

namespace ContH1

variable {G H M N : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M]
  [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N] [MulDistribMulAction H N]

/-- Pull-back along a surjection, with bijective coefficients, is injective in degree one. -/
theorem map_injective_of_surjective_of_bijective (φ : H →* G) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) (f : M →* N) (hf : Continuous f) (hfb : Function.Bijective f)
    (hcomp : ∀ h m, f (φ h • m) = h • f m) : Function.Injective (map φ hφ f hf hcomp) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using induction_on with
  | h c =>
    rw [map_mk, mk_eq_one_iff] at hx
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', rfl⟩ := hfb.2 m
    rw [mk_eq_one_iff]
    refine ⟨m', fun g => ?_⟩
    obtain ⟨h, rfl⟩ := hsurj g
    apply hfb.1
    rw [map_div, hcomp]
    exact hm h

end ContH1

namespace KummerTheory

namespace Curve

section ZHatMap

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k]

/-- The index `n` of `Ẑ(1)_K` viewed in `KummerIndex k` (all `n ≥ 1` in characteristic `0`). -/
def toIndex {K : Type*} [Field K] (i : KummerIndex K) : KummerIndex k :=
  ⟨i.n, Nat.cast_ne_zero.mpr i.n_ne_zero⟩

omit [CharZero k] in
theorem muMap_transition {m n : ℕ} (h : m ∣ n) (ζ : Mu n (kbar k Ω)) :
    muMap m (kbar k Ω) Ω (Mu.transition h ζ) = Mu.transition h (muMap n (kbar k Ω) Ω ζ) := by
  apply Mu.ext
  apply Units.ext
  simp

/-- `Ẑ(1)` of `k̄` → `Ẑ(1)` of `Ω` (reindexed over `KummerIndex K`). -/
def zHatMap (K : Type*) [Field K] : ZHatOne k (kbar k Ω) →* ZHatOne K Ω where
  toFun x := ⟨fun i => (muMap (toIndex (k := k) i).n (kbar k Ω) Ω
      ((x : ∀ j, Mu j.n (kbar k Ω)) (toIndex (k := k) i)) : Mu i.n Ω),
    fun i j h => by
      refine (muMap_transition (k := k) (Ω := Ω) (m := i.n) (n := j.n) h _).symm.trans ?_
      exact congrArg (muMap i.n (kbar k Ω) Ω) (x.2 (toIndex (k := k) i) (toIndex (k := k) j) h)⟩
  map_one' := rfl
  map_mul' a b := by
    apply Subtype.ext
    funext i
    exact map_mul (muMap i.n (kbar k Ω) Ω) _ _

theorem zHatMap_apply (K : Type*) [Field K] (x : ZHatOne k (kbar k Ω)) (i : KummerIndex K) :
    ((zHatMap (k := k) (Ω := Ω) K x : ZHatOne K Ω) : ∀ i, Mu i.n Ω) i =
      muMap i.n (kbar k Ω) Ω ((x : ∀ j, Mu j.n (kbar k Ω)) (toIndex (k := k) i)) := rfl

theorem continuous_zHatMap (K : Type*) [Field K] :
    Continuous (zHatMap (k := k) (Ω := Ω) K) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  exact continuous_of_discreteTopology.comp
    ((continuous_apply (toIndex (k := k) i)).comp continuous_subtype_val)

theorem zHatMap_injective (K : Type*) [Field K] [CharZero K] :
    Function.Injective (zHatMap (k := k) (Ω := Ω) K) := by
  intro x y h
  apply Subtype.ext
  funext j
  let j' : KummerIndex K := ⟨j.n, Nat.cast_ne_zero.mpr j.n_ne_zero⟩
  have := congrArg (fun z : ZHatOne K Ω => (z : ∀ i, Mu i.n Ω) j') h
  exact muMap_injective (k := k) (Ω := Ω) j.n this

theorem zHatMap_surjective (K : Type*) [Field K] [CharZero K] :
    Function.Surjective (zHatMap (k := k) (Ω := Ω) K) := by
  have hpre : ∀ (j : KummerIndex k) (ζ : Mu j.n Ω), ∃ η, muMap j.n (kbar k Ω) Ω η = ζ :=
    fun j ζ => haveI : NeZero j.n := ⟨j.n_ne_zero⟩; muMap_surjective (k := k) j.n ζ
  choose g hg using hpre
  intro x
  let toK : KummerIndex k → KummerIndex K := fun j => ⟨j.n, Nat.cast_ne_zero.mpr j.n_ne_zero⟩
  refine ⟨⟨fun j => g j ((x : ∀ i, Mu i.n Ω) (toK j)), fun i j h => ?_⟩, ?_⟩
  · apply muMap_injective (k := k) (Ω := Ω) i.n
    rw [muMap_transition, hg, hg]
    exact x.2 (toK i) (toK j) h
  · apply Subtype.ext
    funext i
    exact hg (toIndex (k := k) i) _

end ZHatMap

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

instance isGalois_kbar : IsGalois k (kbar k Ω) := ⟨⟩

theorem zHatMap_piToGk_smul (K : Type*) [Field K] (g : Pi D) (x : ZHatOne k (kbar k Ω)) :
    zHatMap K (piToGk D g • x) = g • zHatMap K x := by
  induction g using QuotientGroup.induction_on with
  | H h =>
    apply Subtype.ext
    funext i
    exact muMap_galRestrict_smul i.n (toGalF D h) _

/-- The Kummer map of the constants, on the profinite completion:
`(kˣ)^∧ ≃ H¹(G_k, Ẑ(1)) → H¹(Π_U, Ẑ(1))`. -/
noncomputable def constMapZHat : KummerCompletion k →* ContH1 (Pi D) (ZHatOne (F D) Ω) :=
  (ContH1.map (piToGk D) (continuous_piToGk D) (zHatMap (F D)) (continuous_zHatMap (F D))
    (zHatMap_piToGk_smul D (F D))).comp (kummerZHatEquiv k (kbar k Ω)).symm.toMonoidHom

theorem constMapZHat_apply (x : KummerCompletion k) :
    constMapZHat D x = ContH1.map (piToGk D) (continuous_piToGk D) (zHatMap (F D))
      (continuous_zHatMap (F D)) (zHatMap_piToGk_smul D (F D))
      ((kummerZHatEquiv k (kbar k Ω)).symm x) := rfl

/-- **[AbsTopIII] Prop. 1.6(iii): `(kˣ)^∧ → H¹(Π_U, Ẑ(1))` is injective** (`k` algebraically
closed in `F`). -/
theorem constMapZHat_injective
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D))) :
    Function.Injective (constMapZHat D) :=
  (ContH1.map_injective_of_surjective_of_bijective _ _ (piToGk_surjective D hk) _ _
    ⟨zHatMap_injective (F D), zHatMap_surjective (F D)⟩ _).comp
    (kummerZHatEquiv k (kbar k Ω)).symm.injective

theorem inflZHat_map_piToGk (X : ContH1 (Gk k Ω) (ZHatOne k (kbar k Ω))) :
    inflZHat D (F D) (ContH1.map (piToGk D) (continuous_piToGk D) (zHatMap (F D))
      (continuous_zHatMap (F D)) (zHatMap_piToGk_smul D (F D)) X) =
    resZHat D (F D) (ContH1.map (galRestrict k (F D) (kbar k Ω) Ω)
        (continuous_galRestrict k (F D) (kbar k Ω) Ω) (zHatMap (F D))
        (continuous_zHatMap (F D)) (fun σ x => by
          apply Subtype.ext; funext i; exact muMap_galRestrict_smul i.n σ _) X) := by
  induction X using ContH1.induction_on with
  | h c' => rfl

/-- On `kˣ`, `constMapZHat` is the Kummer map of `U` on constants. -/
theorem constMapZHat_toKummerCompletion (c : kˣ) :
    constMapZHat D (toKummerCompletion k c) = kummerMapZHat D (constUnit D c) := by
  apply ContH1.inflation_injective (N := GaloisPi1.kernel D.H D.S) (fun _ _ => rfl)
  rw [inflation_kummerMapZHat]
  -- reduce to an identity in `H¹(Gal(Ω/F), Ẑ(1))`
  have key : kummerZHat (F D) Ω (constUnit D c : (F D)ˣ) =
      ContH1.map (galRestrict k (F D) (kbar k Ω) Ω)
        (continuous_galRestrict k (F D) (kbar k Ω) Ω) (zHatMap (F D))
        (continuous_zHatMap (F D)) (fun σ x => by
          apply Subtype.ext; funext i; exact muMap_galRestrict_smul i.n σ _)
        (kummerZHat k (kbar k Ω) c) := by
    apply h1ToLimit_injective (F D) Ω
    apply Subtype.ext
    funext i
    haveI : NeZero (i.n : k) := ⟨(toIndex (k := k) i).ne_zero⟩
    change h1Proj (F D) Ω i _ = h1Proj (F D) Ω i _
    rw [h1Proj_kummerZHat]
    have h2 := h1Proj_kummerZHat k (kbar k Ω) (toIndex (k := k) i) c
    have h3 := restriction_kummer (K := k) (L := F D) (ΩK := kbar k Ω) (ΩL := Ω) i.n c
    change kummer i.n (F D) Ω (Units.map (algebraMap k (F D) : k →* F D) c) = _
    rw [← h3]
    rw [show kummer i.n k (kbar k Ω) c = kummer (toIndex (k := k) i).n k (kbar k Ω) c from rfl,
      ← h2]
    induction kummerZHat k (kbar k Ω) c using ContH1.induction_on with
    | h c' => rfl
  refine Eq.trans ?_ (congrArg (resZHat D (F D)) key).symm
  exact inflZHat_map_piToGk D (kummerZHat k (kbar k Ω) c)

end Curve

end KummerTheory
