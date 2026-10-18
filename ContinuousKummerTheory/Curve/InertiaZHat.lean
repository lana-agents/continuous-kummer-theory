/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Curve.TameCharInjective

/-!
# The inertia group of a cusp is `Ẑ(1)`

[AbsTopIII] Proposition 1.4(i) (`T3` l.1764): "the inertia group `I_x` of `x` in `Δ_U` is naturally
isomorphic to `Ẑ(1)`". In `pi1`'s Galois model a point (or cusp) `x` is a place `W ⊇ k` of `Ω`,
and its inertia group is `I_W ∩ H`. For a uniformiser `π ∈ F` of `W ∩ F` the isomorphism is the
tame character

  `θ_π : I_W ∩ H → Ẑ(1) = lim_n μ_n`,   `σ ↦ (σ(π^{1/n}) / π^{1/n})_n`,

i.e. the evaluation at `σ` of the restriction to `H` of the `Ẑ(1)`-valued Kummer class of `π`
(`ContH1.evalTriv`; inertia acts trivially on `Ẑ(1)`). It does not depend on the choice of the
roots `π^{1/n}` (`Curve.val_proj_tameChar`) and is compatible with the transition maps by
construction (it takes values in the inverse limit).

## Main results

* `KummerTheory.PlaceInertia.inertiaSubgroup W`: the inertia set `GaloisPi1.inertia W` of a place
  `W` is a closed subgroup of the Galois group (`PlaceInertia.isClosed_inertiaSubgroup`);
* `Curve.inertiaH D W`: the inertia group `I_W ∩ H`, as a closed (`Curve.isClosed_inertiaH`),
  hence compact, subgroup of `H`;
* `Curve.tameChar`: the tame character `θ_π : I_W ∩ H →* Ẑ(1)`, continuous
  (`Curve.continuous_tameChar`), with components the level-`n` tame characters
  (`Curve.proj_tameChar`, `Curve.val_proj_tameChar`);
* `Curve.tameChar_injective`, `Curve.tameChar_surjective`;
* `Curve.inertiaZHatEquiv : I_W ∩ H ≃ₜ* Ẑ(1)`.
-/

universe u

open groupCohomology AffOrbicurve IntermediateField

namespace ContH1

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction G M]

/-- Evaluation at a product of elements acting trivially is multiplicative (cocycle identity). -/
theorem evalTriv_mul {g h : G} (hg : ∀ m : M, g • m = m) (hh : ∀ m : M, h • m = m)
    (hgh : ∀ m : M, (g * h) • m = m) (x : ContH1 G M) :
    evalTriv (g * h) hgh x = evalTriv g hg x * evalTriv h hh x := by
  induction x using induction_on with
  | h c =>
    rw [evalTriv_mk, evalTriv_mk, evalTriv_mk, isMulCocycle₁ c g h, hg, mul_comm]

/-- **Evaluation on a subgroup acting trivially**: for `I ≤ G` acting trivially on `M`, a class
`x ∈ H¹_cont(G, M)` restricts to a homomorphism `I →* M`, `g ↦ x(g)`. -/
def evalTrivHom (I : Subgroup G) (hI : ∀ g ∈ I, ∀ m : M, g • m = m) (x : ContH1 G M) :
    I →* M :=
  MonoidHom.mk' (fun g => evalTriv (g : G) (hI g g.2) x) fun g h =>
    evalTriv_mul (hI g g.2) (hI h h.2) (hI (g * h) (g * h).2) x

@[simp]
theorem evalTrivHom_apply (I : Subgroup G) (hI : ∀ g ∈ I, ∀ m : M, g • m = m)
    (x : ContH1 G M) (g : I) : evalTrivHom I hI x g = evalTriv (g : G) (hI g g.2) x := rfl

theorem continuous_evalTrivHom (I : Subgroup G) (hI : ∀ g ∈ I, ∀ m : M, g • m = m)
    (x : ContH1 G M) : Continuous (evalTrivHom I hI x) := by
  induction x using induction_on with
  | h c => exact (continuous c).comp continuous_subtype_val

end ContH1

/-! The subgroup structure on the inertia set `GaloisPi1.inertia W`. These lemmas live in the
namespace `KummerTheory.PlaceInertia` (not `GaloisPi1`) to avoid clashes with downstream copies. -/

namespace KummerTheory.PlaceInertia

open GaloisPi1

variable {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω] {W : ValuationSubring Ω}

/-- Inertia elements map `W` into itself. -/
theorem mem_of_mem_inertia {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) {a : Ω} (ha : a ∈ W) :
    σ a ∈ W := by
  rw [← W.valuation_le_one_iff] at ha ⊢
  have h : σ a = (σ a - a) + a := by ring
  rw [h]
  exact Valuation.map_add_le _ (hσ a ((W.valuation_le_one_iff _).mp ha)).le ha

theorem one_mem_inertia : (1 : Ω ≃ₐ[P] Ω) ∈ inertia W := fun a _ => by
  simp

theorem mul_mem_inertia {σ τ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) (hτ : τ ∈ inertia W) :
    σ * τ ∈ inertia W := fun a ha => by
  have h : (σ * τ) a - a = (σ (τ a) - τ a) + (τ a - a) := by rw [AlgEquiv.mul_apply]; ring
  rw [h]
  exact Valuation.map_add_lt _ (hσ _ (mem_of_mem_inertia hτ ha)) (hτ a ha)

theorem pow_mem_inertia {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) (m : ℕ) : σ ^ m ∈ inertia W := by
  induction m with
  | zero => rw [pow_zero]; exact one_mem_inertia
  | succ m ih => rw [pow_succ]; exact mul_mem_inertia ih hσ

/-- On an algebraic extension, `σ⁻¹ a = σ ^ m a` for some `m` (the orbit of `a` under `σ` is
finite, contained in the roots of the minimal polynomial of `a`). -/
theorem exists_pow_apply_eq_inv_apply [Algebra.IsIntegral P Ω] (σ : Ω ≃ₐ[P] Ω) (a : Ω) :
    ∃ m : ℕ, (σ ^ m) a = σ⁻¹ a := by
  classical
  have hint : IsIntegral P a := Algebra.IsIntegral.isIntegral a
  set S := (minpoly P a).rootSet Ω
  have hS : ∀ j : ℕ, (σ ^ j) a ∈ S := fun j => by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
  haveI : Finite S := (Polynomial.rootSet_finite _ _).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun j : ℕ => (⟨(σ ^ j) a, hS j⟩ : S))
  have heq' : (σ ^ i) a = (σ ^ j) a := congrArg Subtype.val heq
  -- `σ ^ (d + 1) a = a` for some `d`
  have key : ∀ i j : ℕ, i < j → (σ ^ i) a = (σ ^ j) a → ∃ d : ℕ, (σ ^ (d + 1)) a = a := by
    intro i j hlt h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨d, (σ ^ i).injective ?_⟩
    rw [← AlgEquiv.mul_apply, ← pow_add, h]
    congr 2
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (σ ^ (d + 1)) a = a := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h heq'
    · exact key j i h heq'.symm
  refine ⟨d, ?_⟩
  rw [pow_succ', AlgEquiv.mul_apply] at hd
  calc (σ ^ d) a = σ.symm (σ ((σ ^ d) a)) := (σ.symm_apply_apply _).symm
    _ = σ⁻¹ a := by rw [hd]; rfl

theorem inv_mem_inertia [Algebra.IsIntegral P Ω] {σ : Ω ≃ₐ[P] Ω} (hσ : σ ∈ inertia W) :
    σ⁻¹ ∈ inertia W := fun a ha => by
  obtain ⟨m, hm⟩ := exists_pow_apply_eq_inv_apply σ a
  rw [← hm]
  exact pow_mem_inertia hσ m a ha

variable (W) in
/-- **The inertia group** of a place `W` of `Ω`, as a subgroup of `Gal(Ω / P)` (for `Ω / P`
algebraic). -/
def inertiaSubgroup [Algebra.IsIntegral P Ω] : Subgroup (Ω ≃ₐ[P] Ω) where
  carrier := inertia W
  mul_mem' := mul_mem_inertia
  one_mem' := one_mem_inertia
  inv_mem' := inv_mem_inertia

theorem mem_inertiaSubgroup [Algebra.IsIntegral P Ω] {σ : Ω ≃ₐ[P] Ω} :
    σ ∈ inertiaSubgroup W ↔ σ ∈ inertia W := Iff.rfl

/-- **The inertia group is closed** in the Krull topology: `σ ↦ σ a` is locally constant. -/
theorem isClosed_inertiaSubgroup [Algebra.IsIntegral P Ω] :
    IsClosed (inertiaSubgroup (P := P) W : Set (Ω ≃ₐ[P] Ω)) := by
  letI : TopologicalSpace Ω := ⊥
  haveI : DiscreteTopology Ω := ⟨rfl⟩
  have hset : (inertiaSubgroup (P := P) W : Set (Ω ≃ₐ[P] Ω)) =
      ⋂ a ∈ W, (fun σ : Ω ≃ₐ[P] Ω => σ a) ⁻¹' {b | W.valuation (b - a) < 1} := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    rfl
  rw [hset]
  refine isClosed_biInter fun a _ => IsClosed.preimage ?_ (isClosed_discrete _)
  refine continuous_of_mul_right_invariant (MulAction.stabilizer (Ω ≃ₐ[P] Ω) a)
    (stabilizer_isOpen_of_isIntegral a) _ fun σ ν hν => ?_
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hν
  rw [AlgEquiv.mul_apply, hν]

end KummerTheory.PlaceInertia

namespace KummerTheory

namespace Curve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
  [IsGalois (K₀ k t) Ω]

variable (D : Pi1.Orbifold.GaloisData k t) (W : ValuationSubring Ω)

/-- **The inertia group `I_W ∩ H`** of a place `W` of `Ω`, as a subgroup of `H`. -/
def inertiaH : Subgroup D.H := (PlaceInertia.inertiaSubgroup W).comap D.H.subtype

omit [CharZero k] in
variable {D W} in
theorem mem_inertiaH {σ : D.H} :
    σ ∈ inertiaH D W ↔ (σ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.inertia W := Iff.rfl

omit [CharZero k] in
theorem isClosed_inertiaH : IsClosed (inertiaH D W : Set D.H) :=
  (PlaceInertia.isClosed_inertiaSubgroup (P := K₀ k t) (W := W)).preimage continuous_subtype_val

instance : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed D.H D.isClosed_H

/-- `I_W ∩ H` is compact (a closed subgroup of the profinite group `H`). -/
instance : CompactSpace (inertiaH D W) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaH D W).isCompact

variable [IsSepClosed Ω] {D W} (hk : ∀ c : k, algebraMap k Ω c ∈ W)

omit [IsSepClosed Ω] in
include hk in
theorem inertiaH_smul_zHatOne : ∀ σ ∈ inertiaH D W, ∀ x : ZHatOne (F D) Ω, σ • x = x :=
  fun _ hσ x => inertia_smul_zHatOne hk hσ (F D) x

/-- **The tame character** `θ_π : I_W ∩ H →* Ẑ(1)`, `σ ↦ (σ(π^{1/n}) / π^{1/n})_n`: the evaluation
at `σ` of the restriction to `H` of the `Ẑ(1)`-valued Kummer class of `π ∈ Fˣ`. -/
noncomputable def tameChar (π : (F D)ˣ) : inertiaH D W →* ZHatOne (F D) Ω :=
  ContH1.evalTrivHom (inertiaH D W) (inertiaH_smul_zHatOne hk)
    (resZHat D (F D) (kummerZHat (F D) Ω π))

theorem continuous_tameChar (π : (F D)ˣ) : Continuous (tameChar hk π) :=
  ContH1.continuous_evalTrivHom _ _ _

/-- The `n`-th component of `θ_π(σ)` is the level-`n` tame character `κ_F(π)|_{I_W ∩ H}`. -/
theorem proj_tameChar (π : (F D)ˣ) (σ : inertiaH D W) (i : KummerIndex (F D)) :
    ZHatOne.proj i (tameChar hk π σ) =
      ContH1.evalTriv (σ : D.H) (inertia_smul_mu hk σ.2 i.n)
        (resMu D i.n (kummer i.n (F D) Ω π)) := by
  rw [← map_proj_res_kummerZHat i π]
  change ZHatOne.proj i (ContH1.evalTriv (σ : D.H) (inertiaH_smul_zHatOne hk _ σ.2)
    (resZHat D (F D) (kummerZHat (F D) Ω π))) = _
  generalize resZHat D (F D) (kummerZHat (F D) Ω π) = x
  induction x using ContH1.induction_on with
  | h c => rfl

/-- **Independence of the choice of roots**: for every `n`-th root `α` of `π`, the `n`-th
component of `θ_π(σ)` is `σ(α) / α`. -/
theorem val_proj_tameChar (π : (F D)ˣ) (σ : inertiaH D W) (i : KummerIndex (F D)) (α : Ωˣ)
    (hα : α ^ i.n = Units.map (algebraMap (F D) Ω : F D →* Ω) π) :
    ((Mu.val (ZHatOne.proj i (tameChar hk π σ)) : Ωˣ) : Ω) =
      ((σ : D.H) : Ω ≃ₐ[K₀ k t] Ω) α / α := by
  rw [proj_tameChar, kummer_eq π α hα]
  change ((Mu.val (kummerFun α (smul_pow_of_pow_eq hα) (toGalF D σ)) : Ωˣ) : Ω) = _
  simp only [val_kummerFun, Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe, toGalF_apply]

variable {π : (F D)ˣ} (hπW : W.valuation ((π : F D) : Ω) < 1)
  (hπ : ∀ f ∈ F D, W.valuation f < 1 → W.valuation f ≤ W.valuation ((π : F D) : Ω))

include hπW hπ in
/-- **The tame character is injective** ([AbsTopIII] Prop. 1.4(i)). -/
theorem tameChar_injective : Function.Injective (tameChar hk π) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have h := eq_one_of_forall_evalTriv_kummer_eq_one hk π hπW hπ σ.2 fun n _ => by
    have := congrArg (ZHatOne.proj (⟨n, Nat.cast_ne_zero.mpr (NeZero.ne n)⟩ :
      KummerIndex (F D))) hσ
    rwa [proj_tameChar, map_one] at this
  exact Subtype.ext h

include hπW hπ in
/-- **The tame character is surjective** ([AbsTopIII] Prop. 1.4(i)): it is onto at every finite
level (`evalTriv_kummer_surjective`), and `I_W ∩ H` is compact. -/
theorem tameChar_surjective : Function.Surjective (tameChar hk π) := by
  intro x
  set S : KummerIndex (F D) → Set (inertiaH D W) := fun i =>
    {σ | ZHatOne.proj i (tameChar hk π σ) = ZHatOne.proj i x}
  have hclosed : ∀ i, IsClosed (S i) := fun i =>
    IsClosed.preimage ((ZHatOne.continuous_proj i).comp (continuous_tameChar hk π))
      (isClosed_discrete {ZHatOne.proj i x})
  have hne : ∀ i, (S i).Nonempty := fun i => by
    obtain ⟨σ, hσ, h⟩ := evalTriv_kummer_surjective (D := D) hk π hπW hπ i.n
      (ZHatOne.proj i x)
    exact ⟨⟨σ, hσ⟩, by
      change ZHatOne.proj i (tameChar hk π ⟨σ, hσ⟩) = _
      rw [proj_tameChar]
      exact h⟩
  have hanti : ∀ i j, i ≤ j → S j ⊆ S i := fun i j hij σ hσ => by
    change ZHatOne.proj i _ = ZHatOne.proj i x
    rw [← ZHatOne.transition_proj hij, ← ZHatOne.transition_proj hij x]
    exact congrArg (Mu.transition hij) hσ
  have hdir : Directed (· ⊇ ·) S := fun i j => by
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    exact ⟨l, hanti i l hil, hanti j l hjl⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir hne
    (fun i => (hclosed i).isCompact) hclosed
  rw [Set.mem_iInter] at hσ
  exact ⟨σ, Subtype.ext (funext fun i => hσ i)⟩

/-- **[AbsTopIII] Prop. 1.4(i): the inertia group `I_W ∩ H` of a place `W ⊇ k` of `Ω` (cusps
included) is isomorphic to `Ẑ(1)`** as a topological group, via the tame character `θ_π` of a
uniformiser `π` of `W ∩ F`. -/
noncomputable def inertiaZHatEquiv : inertiaH D W ≃ₜ* ZHatOne (F D) Ω :=
  let e : inertiaH D W ≃* ZHatOne (F D) Ω :=
    MulEquiv.ofBijective (tameChar hk π) ⟨tameChar_injective hk hπW hπ,
      tameChar_surjective hk hπW hπ⟩
  { e with
    continuous_toFun := continuous_tameChar hk π
    continuous_invFun := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
      (continuous_tameChar hk π)).symm.continuous }

@[simp]
theorem inertiaZHatEquiv_apply (σ : inertiaH D W) :
    inertiaZHatEquiv hk hπW hπ σ = tameChar hk π σ := rfl

end Curve

end KummerTheory
