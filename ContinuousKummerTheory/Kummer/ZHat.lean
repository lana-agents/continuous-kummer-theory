/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Limit

/-!
# `H¹_cont(G_K, Ẑ(1)) ≃ (Kˣ)^∧`

We show that continuous cohomology with coefficients in `Ẑ(1) = lim_n μ_n` is the inverse limit
of the `H¹_cont(G_K, μ_n)` (`KummerTheory.h1ZHatOneEquiv`), and combine this with the Kummer
isomorphisms to obtain `KummerTheory.kummerZHatEquiv : H¹_cont(G_K, Ẑ(1)) ≃* (Kˣ)^∧`.

The comparison map `H¹_cont(G, lim μ_n) → lim H¹_cont(G, μ_n)` is bijective because the sets of
cocycles representing a given class, and of elements of `μ_n` with given coboundary, are finite
and nonempty, so compatible choices exist (`KummerTheory.exists_compatible_family`). No
hypothesis on `K` is needed for this step.
-/

open groupCohomology

namespace KummerTheory

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- The map `H¹_cont(G_K, Ẑ(1)) → H¹_cont(G_K, μ_n)` induced by the projection `Ẑ(1) → μ_n`. -/
noncomputable def h1Proj (i : KummerIndex K) :
    ContH1 Gal(Ω/K) (ZHatOne K Ω) →* ContH1 Gal(Ω/K) (Mu i.n Ω) :=
  ContH1.map (MonoidHom.id _) continuous_id (ZHatOne.proj i) (ZHatOne.continuous_proj i)
    (fun _ _ => rfl)

theorem h1Transition_h1Proj {i j : KummerIndex K} (h : i ≤ j)
    (x : ContH1 Gal(Ω/K) (ZHatOne K Ω)) :
    h1Transition K Ω h (h1Proj K Ω j x) = h1Proj K Ω i x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [h1Proj, h1Transition, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    exact ZHatOne.transition_proj h (c σ)

/-- The comparison map `H¹_cont(G_K, lim μ_n) → lim H¹_cont(G_K, μ_n)`. -/
noncomputable def h1ToLimit : ContH1 Gal(Ω/K) (ZHatOne K Ω) →* H1Limit K Ω :=
  (MonoidHom.pi fun i => h1Proj K Ω i).codRestrict _ fun x _ _ h => h1Transition_h1Proj K Ω h x

@[simp]
theorem h1ToLimit_apply (x : ContH1 Gal(Ω/K) (ZHatOne K Ω)) (i : KummerIndex K) :
    (h1ToLimit K Ω x).1 i = h1Proj K Ω i x := rfl

theorem h1ToLimit_injective : Function.Injective (h1ToLimit K Ω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using ContH1.induction_on with
  | h c =>
  have hi : ∀ i : KummerIndex K,
      IsMulCoboundary₁ (fun σ : Gal(Ω/K) => ZHatOne.proj i (c σ)) := fun i => by
    have := congrArg (fun y : H1Limit K Ω => y.1 i) hx
    exact (ContH1.mk_eq_one_iff _).1 this
  let T : KummerIndex K → Type _ := fun i =>
    {m : Mu i.n Ω // ∀ σ : Gal(Ω/K), σ • m / m = ZHatOne.proj i (c σ)}
  haveI : ∀ i, Nonempty (T i) := fun i => let ⟨m, hm⟩ := hi i; ⟨⟨m, hm⟩⟩
  obtain ⟨s, hs⟩ := exists_compatible_family T
    (fun i j h m => ⟨Mu.transition h m.1, fun σ => by
      rw [← Mu.transition_smul, ← map_div, m.2 σ, ZHatOne.transition_proj]⟩)
    (fun i m => Subtype.ext (Mu.transition_self i.n_ne_zero _))
    (fun i j k _ _ m => Subtype.ext (Mu.transition_transition _ _ _))
  rw [ContH1.mk_eq_one_iff]
  refine ⟨⟨fun i => (s i).1, fun i j h => congrArg Subtype.val (hs i j h)⟩, fun σ => ?_⟩
  apply Subtype.ext
  funext i
  exact (s i).2 σ

theorem h1ToLimit_surjective : Function.Surjective (h1ToLimit K Ω) := by
  intro y
  let S : KummerIndex K → Type _ := fun i =>
    {c : ContH1.cocycles Gal(Ω/K) (Mu i.n Ω) // ContH1.mk c = y.1 i}
  haveI : ∀ i, Nonempty (S i) := fun i =>
    let ⟨c, hc⟩ := ContH1.mk_surjective (y.1 i); ⟨⟨c, hc⟩⟩
  haveI : ∀ i, Finite (S i) := by
    intro i
    obtain ⟨c₀⟩ := (inferInstance : Nonempty (S i))
    refine Finite.of_injective
      (fun c : S i => ((ContH1.mk_eq_mk_iff _ _).1 (c.2.trans c₀.2.symm)).choose) ?_
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    funext σ
    have h1 := ((ContH1.mk_eq_mk_iff _ _).1 (c.2.trans c₀.2.symm)).choose_spec σ
    have h2 := ((ContH1.mk_eq_mk_iff _ _).1 (d.2.trans c₀.2.symm)).choose_spec σ
    simp only at hcd
    rw [hcd] at h1
    exact div_left_injective (h1.symm.trans h2)
  obtain ⟨s, hs⟩ := exists_compatible_family S
    (fun i j h c => ⟨ContH1.cocyclesMap (MonoidHom.id _) continuous_id (Mu.transition h)
      continuous_of_discreteTopology (fun σ ζ => Mu.transition_smul h σ ζ) c.1, by
        change h1Transition K Ω h (ContH1.mk c.1) = y.1 i
        rw [c.2]
        exact y.2 i j h⟩)
    (fun i c => Subtype.ext (Subtype.ext (funext fun σ => Mu.transition_self i.n_ne_zero _)))
    (fun i j k _ _ c => Subtype.ext (Subtype.ext (funext fun σ =>
      Mu.transition_transition _ _ _)))
  let C : Gal(Ω/K) → ZHatOne K Ω := fun σ => ⟨fun i => (s i).1 σ, fun i j h =>
    congrArg (fun c : S i => (c.1 : Gal(Ω/K) → Mu i.n Ω) σ) (hs i j h)⟩
  have hcont : Continuous C :=
    continuous_induced_rng.2 (continuous_pi fun i => ContH1.continuous (s i).1)
  have hcoc : IsMulCocycle₁ C := fun σ τ =>
    Subtype.ext (funext fun i => ContH1.isMulCocycle₁ (s i).1 σ τ)
  refine ⟨ContH1.mk (ContH1.mkCocycle C hcont hcoc), Subtype.ext (funext fun i => ?_)⟩
  change ContH1.mk _ = y.1 i
  rw [← (s i).2]
  rfl

/-- **Continuous cohomology commutes with the inverse limit** `Ẑ(1) = lim_n μ_n`:
`H¹_cont(G_K, Ẑ(1)) ≃ lim_n H¹_cont(G_K, μ_n)`. -/
noncomputable def h1ZHatOneEquiv : ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃* H1Limit K Ω :=
  MulEquiv.ofBijective (h1ToLimit K Ω) ⟨h1ToLimit_injective K Ω, h1ToLimit_surjective K Ω⟩

variable [IsGalois K Ω] [IsSepClosed Ω]

/-- **Kummer theory, inverse-limit form**: for `Ω` a separable closure of `K`,
`H¹_cont(G_K, Ẑ(1)) ≃ (Kˣ)^∧ = lim_n Kˣ/(Kˣ)ⁿ`, the limit over `n` invertible in `K`. -/
noncomputable def kummerZHatEquiv : ContH1 Gal(Ω/K) (ZHatOne K Ω) ≃* KummerCompletion K :=
  (h1ZHatOneEquiv K Ω).trans (kummerLimitEquiv K Ω).symm

/-- The Kummer map `Kˣ → H¹_cont(G_K, Ẑ(1))`. -/
noncomputable def kummerZHat : Kˣ →* ContH1 Gal(Ω/K) (ZHatOne K Ω) :=
  (kummerZHatEquiv K Ω).symm.toMonoidHom.comp (toKummerCompletion K)

/-- The `n`-th component of the `Ẑ(1)`-valued Kummer class of `a` is its `μ_n`-valued Kummer
class. -/
theorem h1Proj_kummerZHat (i : KummerIndex K) (a : Kˣ) :
    h1Proj K Ω i (kummerZHat K Ω a) = kummer i.n K Ω a := by
  have := congrArg (fun y : H1Limit K Ω => y.1 i)
    ((h1ZHatOneEquiv K Ω).apply_symm_apply (kummerLimitEquiv K Ω (toKummerCompletion K a)))
  exact this

theorem kummerZHatEquiv_kummerZHat (a : Kˣ) :
    kummerZHatEquiv K Ω (kummerZHat K Ω a) = toKummerCompletion K a :=
  (kummerZHatEquiv K Ω).apply_symm_apply _

end KummerTheory
