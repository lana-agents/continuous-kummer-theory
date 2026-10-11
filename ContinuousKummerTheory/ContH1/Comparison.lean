/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Basic

/-!
# Comparison of `ContH1` with Mathlib's continuous cohomology in degree one

Mathlib defines the continuous cohomology `continuousCohomology n A` of a topological
representation `A : TopRep k G` as the cohomology of the complex of *homogeneous* continuous
cochains, i.e. of the `G`-invariants of `C(G, C(G, ..., A))` with the inductively defined
differential `TopRep.d`. Explicitly, in low degrees:

* a `0`-cochain is a continuous `τ : G → A` with `τ (g * x) = g • τ x`;
* a `1`-cochain is a continuous `σ : G → C(G, A)` with `σ (g * x) (g * y) = g • σ x y`;
* `(d τ) y z = τ z - τ y` and `(d σ) x y z = σ y z - (σ x z - σ x y)`.

We show that `σ ↦ (g ↦ σ 1 g)` identifies homogeneous `1`-cocycles with continuous crossed
homomorphisms `G → A` (with inverse `c ↦ ((x, y) ↦ c y - c x)`), and homogeneous coboundaries
with principal crossed homomorphisms. Consequently `continuousCohomology 1 A` is isomorphic to
the repository's `ContH1 G (Multiplicative A)`, where `G` acts on `Multiplicative A` through the
representation.

## Main definitions and results

* `ContH1.z1Equiv` : homogeneous continuous `1`-cocycles `≃+` continuous crossed homomorphisms.
* `ContH1.mem_B1_iff` : a homogeneous cocycle is a coboundary iff its crossed homomorphism is
  principal.
* `ContH1.continuousCohomologyOneIso` : `continuousCohomology 1 A ≅ Z¹ ⧸ B¹` in
  `TopModuleCat k`.
* `ContH1.continuousCohomologyOneEquiv` :
  `continuousCohomology 1 A ≃+ Additive (ContH1 G (Multiplicative A))`.
* `ContH1.continuousCohomologyOneEquiv_π` : its value on the class of a cocycle.
-/

open CategoryTheory TopRep ContRepresentation groupCohomology

namespace ContH1

variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G]

instance (A : TopRep k G) : MulDistribMulAction G (Multiplicative A) where
  smul g a := Multiplicative.ofAdd (A.ρ g a.toAdd)
  one_smul a := by simp [HSMul.hSMul]
  mul_smul g h a := by simp [HSMul.hSMul]
  smul_mul g a b := by simp [HSMul.hSMul]
  smul_one g := by simp [HSMul.hSMul]

variable (A : TopRep k G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem toAdd_smul (g : G) (a : Multiplicative A) : (g • a).toAdd = A.ρ g a.toAdd := rfl

lemma d_one_apply (f : C(G, A)) (y z : G) : (d A 1).hom f y z = f z - f y := by
  simp [d_succ, d_zero, hom_sub, ContIntertwiningMap.sub_apply]

lemma d_two_apply (σ : C(G, C(G, A))) (x y z : G) :
    (d A 2).hom σ x y z = σ y z - (σ x z - σ x y) := by
  simp [d_succ, d_zero, hom_sub, ContIntertwiningMap.sub_apply]

lemma cochain_one_apply_mul (σ : (homogeneousCochains A).X 1) (g x y : G) :
    σ.1 (g * x) (g * y) = A.ρ g (σ.1 x y) := by
  have := DFunLike.congr_fun (DFunLike.congr_fun ((mem_invariants _).1 σ.2 g) (g * x)) (g * y)
  simpa using this.symm

lemma cochain_zero_apply_mul (τ : (homogeneousCochains A).X 0) (g x : G) :
    τ.1 (g * x) = A.ρ g (τ.1 x) := by
  have := DFunLike.congr_fun ((mem_invariants _).1 τ.2 g) (g * x)
  simpa using this.symm

lemma d_one_two_apply (σ : (homogeneousCochains A).X 1) (x y z : G) :
    (((homogeneousCochains A).d 1 2).hom σ).1 x y z = σ.1 y z - (σ.1 x z - σ.1 x y) := by
  have := homogeneousCochains.d_apply A 1 σ
  rw [this, d_two_apply]

lemma d_zero_one_apply (τ : (homogeneousCochains A).X 0) (y z : G) :
    (((homogeneousCochains A).d 0 1).hom τ).1 y z = τ.1 z - τ.1 y := by
  have := homogeneousCochains.d_apply A 0 τ
  rw [this, d_one_apply]


/-- Shorthand for the kernel of the differential `d¹` on homogeneous `1`-cochains. -/
abbrev Z1 := ((homogeneousCochains A).d 1 2).hom.ker

variable {A}

lemma cocycle_eq (σ : Z1 A) (x y z : G) :
    σ.1.1 y z - σ.1.1 x z + σ.1.1 x y = 0 := by
  have h0 : ((homogeneousCochains A).d 1 2).hom σ.1 = 0 := σ.2
  have h := d_one_two_apply A σ.1 x y z
  rw [h0] at h
  have h' : σ.1.1 y z - (σ.1.1 x z - σ.1.1 x y) = 0 := h.symm.trans rfl
  rw [← h']
  abel

lemma apply_eq_sub (σ : Z1 A) (x y : G) : σ.1.1 x y = σ.1.1 1 y - σ.1.1 1 x := by
  have := cocycle_eq σ 1 x y
  rw [← sub_eq_zero, ← this]
  abel

lemma apply_one_mul (σ : Z1 A) (g h : G) :
    σ.1.1 1 (g * h) = A.ρ g (σ.1.1 1 h) + σ.1.1 1 g := by
  rw [← cochain_one_apply_mul, mul_one, apply_eq_sub σ g (g * h)]
  abel

/-- The inhomogeneous (multiplicative) continuous crossed homomorphism `g ↦ σ(1)(g)` attached to
a homogeneous continuous `1`-cocycle `σ`. -/
def cocycleOfZ1 (σ : Z1 A) : cocycles G (Multiplicative A) :=
  mkCocycle (fun g => Multiplicative.ofAdd (σ.1.1 1 g))
    (continuous_ofAdd.comp (σ.1.1 1).continuous)
    (fun g h => by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_ofAdd, toAdd_smul]
      exact apply_one_mul σ g h)

@[simp]
lemma toAdd_cocycleOfZ1_apply (σ : Z1 A) (g : G) :
    (cocycleOfZ1 σ g).toAdd = σ.1.1 1 g := rfl

/-- The continuous function `G → A` underlying a multiplicative cocycle. -/
def toContinuousMap (c : cocycles G (Multiplicative A)) : C(G, A) :=
  ⟨fun g => (c g).toAdd, continuous_toAdd.comp (ContH1.continuous c)⟩

omit [IsTopologicalGroup G] in
lemma isMulCocycle₁_toAdd (c : cocycles G (Multiplicative A)) (g y : G) :
    A.ρ g (toContinuousMap c y) = toContinuousMap c (g * y) - toContinuousMap c g := by
  have := congrArg Multiplicative.toAdd (isMulCocycle₁ c g y)
  rw [toAdd_mul, toAdd_smul] at this
  change _ = (c (g * y)).toAdd - (c g).toAdd
  rw [this]
  abel

/-- The homogeneous `1`-cocycle `(x, y) ↦ c(y) - c(x)` attached to a continuous crossed
homomorphism `c`. -/
def z1OfCocycle (c : cocycles G (Multiplicative A)) : Z1 A :=
  ⟨⟨(d A 1).hom (toContinuousMap c), by
    rw [mem_invariants]
    intro g
    ext x y
    change A.ρ g ((d A 1).hom (toContinuousMap c) (g⁻¹ * x) (g⁻¹ * y)) = _
    rw [d_one_apply, d_one_apply, map_sub, isMulCocycle₁_toAdd, isMulCocycle₁_toAdd,
      mul_inv_cancel_left, mul_inv_cancel_left]
    abel⟩, by
    rw [LinearMap.mem_ker]
    refine Subtype.ext (ContinuousMap.ext fun x => ContinuousMap.ext fun y =>
      ContinuousMap.ext fun z => ?_)
    refine (d_one_two_apply A _ x y z).trans ?_
    change (d A 1).hom (toContinuousMap c) y z - ((d A 1).hom (toContinuousMap c) x z -
      (d A 1).hom (toContinuousMap c) x y) = (0 : A)
    rw [d_one_apply, d_one_apply, d_one_apply]
    abel⟩

@[simp]
lemma z1OfCocycle_apply (c : cocycles G (Multiplicative A)) (x y : G) :
    (z1OfCocycle c).1.1 x y = (c y).toAdd - (c x).toAdd :=
  d_one_apply A _ x y

/-- Homogeneous continuous `1`-cocycles correspond to continuous crossed homomorphisms. -/
def z1Equiv : Z1 A ≃+ Additive (cocycles G (Multiplicative A)) where
  toFun σ := Additive.ofMul (cocycleOfZ1 σ)
  invFun c := z1OfCocycle c.toMul
  left_inv σ := by
    refine Subtype.ext (Subtype.ext (ContinuousMap.ext fun x => ContinuousMap.ext fun y => ?_))
    refine (z1OfCocycle_apply _ x y).trans ?_
    simp only [toMul_ofMul, toAdd_cocycleOfZ1_apply]
    exact (apply_eq_sub σ x y).symm
  right_inv c := by
    apply Additive.toMul.injective
    refine Subtype.ext (funext fun g => ?_)
    apply Multiplicative.toAdd.injective
    change (z1OfCocycle c.toMul).1.1 1 g = _
    rw [z1OfCocycle_apply, map_one_eq, toAdd_one, sub_zero]
  map_add' _ _ := rfl

@[simp]
lemma toAdd_z1Equiv_apply (σ : Z1 A) (g : G) :
    ((z1Equiv σ).toMul g).toAdd = σ.1.1 1 g := rfl

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-- The explicit left homology data of the short complex `C⁰ → C¹ → C²` of homogeneous
continuous cochains, given by the kernel and cokernel in `TopModuleCat`. -/
noncomputable def leftHomologyData₁ :
    ((homogeneousCochains A).sc' 0 1 2).LeftHomologyData :=
  ⟨_, _, _, _, _, TopModuleCat.isLimitKer _, by simp, TopModuleCat.isColimitCoker _⟩

lemma f'_apply_coe (τ : (homogeneousCochains A).X 0) :
    (show Z1 A from (leftHomologyData₁ A).f'.hom τ).1 =
      ((homogeneousCochains A).d 0 1).hom τ := rfl

variable (A) in
/-- The homogeneous continuous `1`-coboundaries, as a submodule of `Z1 A`. -/
noncomputable def B1 : Submodule k (Z1 A) := (leftHomologyData₁ A).f'.hom.range

lemma mem_B1_iff (σ : Z1 A) :
    σ ∈ B1 A ↔ IsMulCoboundary₁ (cocycleOfZ1 σ : G → _) := by
  unfold B1
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨Multiplicative.ofAdd (τ.1 1), fun g => ?_⟩
    apply Multiplicative.toAdd.injective
    have h := congrArg (fun σ : Z1 A => σ.1.1 1 g) hτ
    simp only at h
    change _ = σ.1.1 1 g
    refine Eq.trans ?_ h
    change _ = (((homogeneousCochains A).d 0 1).hom τ).1 1 g
    rw [d_zero_one_apply, toAdd_div, toAdd_smul, toAdd_ofAdd, ← cochain_zero_apply_mul, mul_one]
  · rintro ⟨a, ha⟩
    have ha' (g : G) : A.ρ g a.toAdd - a.toAdd = σ.1.1 1 g := by
      have := congrArg Multiplicative.toAdd (ha g)
      rwa [toAdd_div, toAdd_smul] at this
    refine ⟨⟨σ.1.1 1 + ContinuousMap.const G a.toAdd, ?_⟩, ?_⟩
    · rw [mem_invariants]
      intro g
      ext x
      change A.ρ g (σ.1.1 1 (g⁻¹ * x) + a.toAdd) = σ.1.1 1 x + a.toAdd
      have := apply_one_mul σ g (g⁻¹ * x)
      rw [mul_inv_cancel_left] at this
      rw [map_add, this, ← ha' g]
      abel
    · refine Subtype.ext (Subtype.ext (ContinuousMap.ext fun y => ContinuousMap.ext fun z => ?_))
      refine (d_zero_one_apply A _ y z).trans ?_
      change (σ.1.1 1 z + a.toAdd) - (σ.1.1 1 y + a.toAdd) = σ.1.1 y z
      rw [apply_eq_sub σ y z]
      abel

/-- The surjection from homogeneous continuous `1`-cocycles onto `ContH1`. -/
noncomputable def toH1 : Z1 A →+ Additive (ContH1 G (Multiplicative A)) :=
  (MonoidHom.toAdditive ContH1.mk).comp (z1Equiv (A := A)).toAddMonoidHom

lemma toH1_apply (σ : Z1 A) : toH1 σ = Additive.ofMul (ContH1.mk (cocycleOfZ1 σ)) := rfl

lemma toH1_surjective : Function.Surjective (toH1 (A := A)) := by
  intro x
  obtain ⟨c, hc⟩ := ContH1.mk_surjective x.toMul
  refine ⟨z1Equiv.symm (Additive.ofMul c), ?_⟩
  rw [toH1, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  exact congrArg Additive.ofMul hc

lemma ker_toH1 : (toH1 (A := A)).ker = (B1 A).toAddSubgroup := by
  ext σ
  rw [AddMonoidHom.mem_ker, toH1_apply, Submodule.mem_toAddSubgroup, mem_B1_iff,
    ← mk_eq_one_iff]
  exact Additive.ofMul.injective.eq_iff' rfl

/-- The homology of the explicit left homology data is `ContH1`. -/
noncomputable def quotEquiv :
    (Z1 A ⧸ B1 A) ≃+ Additive (ContH1 G (Multiplicative A)) :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_toH1.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ toH1_surjective)

lemma quotEquiv_mk (σ : Z1 A) : quotEquiv (Submodule.Quotient.mk σ : Z1 A ⧸ B1 A) = toH1 σ :=
  rfl

variable (A) in
/-- The first continuous cohomology is (as a topological `k`-module) the quotient of the
homogeneous continuous `1`-cocycles by the coboundaries. -/
noncomputable def continuousCohomologyOneIso :
    continuousCohomology 1 A ≅ (leftHomologyData₁ A).H :=
  (homogeneousCochains A).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (leftHomologyData₁ A).homologyIso

variable (A) in
/-- **Comparison of `H¹`.** The first continuous cohomology `continuousCohomology 1 A` of
Mathlib (homogeneous cochains) is isomorphic to `ContH1 G (Multiplicative A)` (continuous
crossed homomorphisms modulo principal ones). -/
noncomputable def continuousCohomologyOneEquiv :
    continuousCohomology 1 A ≃+ Additive (ContH1 G (Multiplicative A)) :=
  (continuousCohomologyOneIso A).toContinuousLinearEquiv.toLinearEquiv.toAddEquiv.trans quotEquiv

lemma continuousCohomologyOneEquiv_apply (x : continuousCohomology 1 A) :
    continuousCohomologyOneEquiv A x = quotEquiv ((continuousCohomologyOneIso A).hom.hom x) :=
  rfl

lemma iCycles_mem (z : ContinuousCohomology.cocycles A 1) :
    (homogeneousCochains A).iCycles 1 z ∈ Z1 A := by
  rw [LinearMap.mem_ker]
  change ((homogeneousCochains A).iCycles 1 ≫ (homogeneousCochains A).d 1 2).hom z = 0
  rw [HomologicalComplex.iCycles_d]
  rfl

/-- On the class of a homogeneous cocycle `σ`, the comparison isomorphism is given by the class
of the inhomogeneous crossed homomorphism `g ↦ σ(1)(g)`. -/
theorem continuousCohomologyOneEquiv_π (z : ContinuousCohomology.cocycles A 1) :
    continuousCohomologyOneEquiv A ((ContinuousCohomology.π A 1).hom z) =
      Additive.ofMul (ContH1.mk (cocycleOfZ1 ⟨_, iCycles_mem z⟩)) := by
  have h01 : (ComplexShape.up ℕ).prev 1 = 0 := by simp
  have h12 : (ComplexShape.up ℕ).next 1 = 2 := by simp
  have key : (homogeneousCochains A).homologyπ 1 ≫ (continuousCohomologyOneIso A).hom =
      ((homogeneousCochains A).cyclesIsoSc' 0 1 2 h01 h12).hom ≫
        (leftHomologyData₁ A).cyclesIso.hom ≫ (leftHomologyData₁ A).π := by
    rw [continuousCohomologyOneIso, Iso.trans_hom,
      HomologicalComplex.π_homologyIsoSc'_hom_assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  have hi : ((homogeneousCochains A).cyclesIsoSc' 0 1 2 h01 h12).hom ≫
      (leftHomologyData₁ A).cyclesIso.hom ≫ (leftHomologyData₁ A).i =
        (homogeneousCochains A).iCycles 1 := by
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  have h1 : (continuousCohomologyOneIso A).hom.hom ((ContinuousCohomology.π A 1).hom z) =
      (leftHomologyData₁ A).π.hom ((((homogeneousCochains A).cyclesIsoSc' 0 1 2 h01 h12).hom ≫
        (leftHomologyData₁ A).cyclesIso.hom).hom z) :=
    congrArg (fun f => f.hom z) key
  have h2 : (show Z1 A from (((homogeneousCochains A).cyclesIsoSc' 0 1 2 h01 h12).hom ≫
      (leftHomologyData₁ A).cyclesIso.hom).hom z) = ⟨_, iCycles_mem z⟩ :=
    Subtype.ext (congrArg (fun f => f.hom z) hi)
  rw [continuousCohomologyOneEquiv_apply, h1]
  exact congrArg (fun σ : Z1 A => Additive.ofMul (ContH1.mk (cocycleOfZ1 σ))) h2

end ContH1
