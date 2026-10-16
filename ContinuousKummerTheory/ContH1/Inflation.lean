/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Basic

/-!
# Inflation and descent of continuous cocycles along a quotient

Let `G` be a topological group, `N` a normal subgroup and `M` a commutative topological group
on which `G` acts through `G ⧸ N` (that is: `G ⧸ N` acts, `G` acts, and the actions are
compatible). Then:

* `ContH1.inflation N hcomp : H¹_cont(G ⧸ N, M) →* H¹_cont(G, M)` is the inflation map (pull back
  along `G → G ⧸ N`), and it is **injective** (`ContH1.inflation_injective`): this is the first
  term of the inflation-restriction sequence (Serre, *Galois Cohomology*, I.2.6(b)).
* `ContH1.descend N c hc`: a continuous cocycle `c` on `G` which is trivial on `N` is constant on
  the cosets of `N` and descends to a continuous cocycle on `G ⧸ N`, whose inflation is `c`
  (`ContH1.inflation_mk_descend`).
* `MulDistribMulAction.quotientOfLeKer`: an action of `G` in which `N` acts trivially induces an
  action of `G ⧸ N`, compatible with the given one.
-/

open groupCohomology

/-- An action of `G` on `M` in which every element of the normal subgroup `N` acts trivially
induces an action of `G ⧸ N`. -/
abbrev MulDistribMulAction.quotientOfLeKer {G M : Type*} [Group G] [Monoid M]
    [MulDistribMulAction G M] (N : Subgroup G) [N.Normal] (hN : ∀ n ∈ N, ∀ m : M, n • m = m) :
    MulDistribMulAction (G ⧸ N) M :=
  MulDistribMulAction.compHom M
    (QuotientGroup.lift N (MulDistribMulAction.toMulAut G M) fun n hn => by
      ext m
      exact hN n hn m)

theorem MulDistribMulAction.quotientOfLeKer_smul {G M : Type*} [Group G] [Monoid M]
    [MulDistribMulAction G M] (N : Subgroup G) [N.Normal] (hN : ∀ n ∈ N, ∀ m : M, n • m = m)
    (g : G) (m : M) :
    letI := MulDistribMulAction.quotientOfLeKer N hN
    (g : G ⧸ N) • m = g • m :=
  rfl

namespace ContH1

section Trivial

/-- A cocycle trivial on a subgroup `N` is constant on the left cosets of `N`. -/
theorem eq_of_trivial_on {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {N : Subgroup G} {c : G → M} (hc : IsMulCocycle₁ c) (hN : ∀ n ∈ N, c n = 1)
    {g h : G} (hgh : g⁻¹ * h ∈ N) : c g = c h := by
  have : h = g * (g⁻¹ * h) := by group
  rw [this, hc, hN _ hgh, smul_one, one_mul]

end Trivial

variable {G M : Type*} [Group G] [TopologicalSpace G]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction G M]
  (N : Subgroup G) [N.Normal] [MulDistribMulAction (G ⧸ N) M]

/-- **Inflation** `H¹_cont(G ⧸ N, M) → H¹_cont(G, M)` for an action of `G` on `M` through
`G ⧸ N`. -/
def inflation (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m) :
    ContH1 (G ⧸ N) M →* ContH1 G M :=
  map (QuotientGroup.mk' N) QuotientGroup.continuous_mk (MonoidHom.id M) continuous_id
    fun g m => hcomp g m

variable {N}

@[simp]
theorem inflation_mk (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m)
    (c : cocycles (G ⧸ N) M) (g : G) :
    (cocyclesMap (QuotientGroup.mk' N) QuotientGroup.continuous_mk (MonoidHom.id M)
      continuous_id (fun g m => hcomp g m) c : G → M) g = c (g : G ⧸ N) := rfl

/-- **Inflation is injective** in degree one. -/
theorem inflation_injective (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m) :
    Function.Injective (inflation N hcomp) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using ContH1.induction_on with
  | h c =>
    rw [inflation, map_mk, mk_eq_one_iff] at hx
    obtain ⟨m, hm⟩ := hx
    rw [mk_eq_one_iff]
    refine ⟨m, fun q => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hcomp]
    exact hm g

/-- The function on `G ⧸ N` induced by a cocycle trivial on `N`. -/
def descendFun (c : G → M) (hc : IsMulCocycle₁ c) (hN : ∀ n ∈ N, c n = 1) : G ⧸ N → M :=
  Quotient.lift c fun _ _ hgh => eq_of_trivial_on hc hN (QuotientGroup.leftRel_apply.mp hgh)

omit [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] [N.Normal]
  [MulDistribMulAction (G ⧸ N) M] in
@[simp]
theorem descendFun_mk (c : G → M) (hc : IsMulCocycle₁ c) (hN : ∀ n ∈ N, c n = 1) (g : G) :
    descendFun c hc hN (g : G ⧸ N) = c g := rfl

/-- **Descent** of a continuous cocycle trivial on `N` to `G ⧸ N`. -/
def descend (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m) (c : cocycles G M)
    (hN : ∀ n ∈ N, c n = 1) : cocycles (G ⧸ N) M :=
  mkCocycle (descendFun c (isMulCocycle₁ c) hN)
    (by
      refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr ?_
      exact continuous c)
    (by
      intro p q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, descendFun_mk, descendFun_mk, descendFun_mk, hcomp]
      exact isMulCocycle₁ c g h)

@[simp]
theorem descend_apply (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m) (c : cocycles G M)
    (hN : ∀ n ∈ N, c n = 1) (g : G) : descend hcomp c hN (g : G ⧸ N) = c g := rfl

theorem inflation_mk_descend (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m)
    (c : cocycles G M) (hN : ∀ n ∈ N, c n = 1) :
    inflation N hcomp (mk (descend hcomp c hN)) = mk c := by
  rw [inflation, map_mk]
  congr 1

omit [N.Normal] [MulDistribMulAction (G ⧸ N) M] in
/-- If two cohomologous cocycles take values in a module on which `N` acts trivially, and one of
them is trivial on `N`, then so is the other. -/
theorem trivial_on_of_mk_eq_mk {c c' : cocycles G M} (h : mk c = mk c')
    (hact : ∀ n ∈ N, ∀ m : M, n • m = m) (hc' : ∀ n ∈ N, c' n = 1) : ∀ n ∈ N, c n = 1 := by
  rw [mk_eq_mk_iff] at h
  obtain ⟨m, hm⟩ := h
  intro n hn
  have := hm n
  simp only [hact n hn, div_self'] at this
  rw [hc' n hn, div_one] at this
  exact this.symm

/-- **Descent of a class** of `H¹_cont(G, M)` which has a representative trivial on `N` to
`H¹_cont(G ⧸ N, M)`. -/
noncomputable def descendClass (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m)
    (x : ContH1 G M) (hx : ∃ c : cocycles G M, mk c = x ∧ ∀ n ∈ N, c n = 1) :
    ContH1 (G ⧸ N) M :=
  mk (descend hcomp hx.choose hx.choose_spec.2)

theorem inflation_descendClass (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m)
    (x : ContH1 G M) (hx : ∃ c : cocycles G M, mk c = x ∧ ∀ n ∈ N, c n = 1) :
    inflation N hcomp (descendClass hcomp x hx) = x := by
  rw [descendClass, inflation_mk_descend]
  exact hx.choose_spec.1

/-- The image of inflation consists of the classes with a representative trivial on `N`. -/
theorem exists_inflation_eq (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m)
    (x : ContH1 G M) (hx : ∃ c : cocycles G M, mk c = x ∧ ∀ n ∈ N, c n = 1) :
    ∃ y, inflation N hcomp y = x :=
  ⟨_, inflation_descendClass hcomp x hx⟩

/-- **Descent of a homomorphism** into `H¹_cont(G, M)` whose values have representatives trivial
on `N`: the unique homomorphism into `H¹_cont(G ⧸ N, M)` lifting it along inflation. -/
noncomputable def descendHom {A : Type*} [Monoid A]
    (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m) (φ : A →* ContH1 G M)
    (hφ : ∀ a, ∃ c : cocycles G M, mk c = φ a ∧ ∀ n ∈ N, c n = 1) :
    A →* ContH1 (G ⧸ N) M where
  toFun a := descendClass hcomp (φ a) (hφ a)
  map_one' := inflation_injective hcomp (by rw [inflation_descendClass, map_one, map_one])
  map_mul' a b := inflation_injective hcomp (by
    rw [inflation_descendClass, map_mul (inflation N hcomp), inflation_descendClass,
      inflation_descendClass, map_mul])

theorem inflation_descendHom {A : Type*} [Monoid A]
    (hcomp : ∀ (g : G) (m : M), (g : G ⧸ N) • m = g • m) (φ : A →* ContH1 G M)
    (hφ : ∀ a, ∃ c : cocycles G M, mk c = φ a ∧ ∀ n ∈ N, c n = 1) (a : A) :
    inflation N hcomp (descendHom hcomp φ hφ a) = φ a :=
  inflation_descendClass hcomp (φ a) (hφ a)

end ContH1
