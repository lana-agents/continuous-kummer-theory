/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.ContH1.Corestriction

/-!
# Independence of the corestriction from the choice of coset representatives

`ContH1.cor` is defined by the cochain formula using the fixed coset representatives
`corRep φ x = x.out`. Here we generalise the formula to an arbitrary section
`r : G ⧸ φ(H) → G` (`ContH1.corFunWith`), show that it sends cocycles to cocycles, and that two
sections `r, r'` give cocycles differing by the coboundary of `∏ₓ r(x) • c(h_x)`, where
`r'(x) = r(x) φ(h_x)` (`ContH1.corFunWith_eq_mul`). Consequently the class `ContH1.cor (mk c)`
can be computed with any section (`ContH1.cor_mk_eq_mk_corFunWith`).
-/

open groupCohomology

namespace ContH1

section CorFunWith

variable {G H M : Type*} [Group G] [Group H] [CommGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction H M] (φ : H →* G) (hφ : Function.Injective φ)
  (r : G ⧸ φ.range → G) (hr : ∀ x, (r x : G ⧸ φ.range) = x)

include hr in
omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem section_inv_mul_mem (g : G) (x : G ⧸ φ.range) :
    (r (g • x))⁻¹ * g * r x ∈ φ.range := by
  rw [mul_assoc, ← QuotientGroup.eq, hr]
  conv_lhs => rw [← hr x]
  rfl

/-- The element `φ⁻¹(r(g x)⁻¹ g r(x)) ∈ H` for a section `r` of `G → G ⧸ φ(H)`. -/
noncomputable def corEltWith (g : G) (x : G ⧸ φ.range) : H :=
  (MonoidHom.ofInjective hφ).symm ⟨_, section_inv_mul_mem φ r hr g x⟩

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem apply_corEltWith (g : G) (x : G ⧸ φ.range) :
    φ (corEltWith φ hφ r hr g x) = (r (g • x))⁻¹ * g * r x :=
  MonoidHom.apply_ofInjective_symm hφ _

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem section_mul_apply_corEltWith (g : G) (x : G ⧸ φ.range) :
    r (g • x) * φ (corEltWith φ hφ r hr g x) = g * r x := by
  rw [apply_corEltWith, mul_assoc, mul_inv_cancel_left]

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem corEltWith_mul (g₁ g₂ : G) (x : G ⧸ φ.range) :
    corEltWith φ hφ r hr (g₁ * g₂) x =
      corEltWith φ hφ r hr g₁ (g₂ • x) * corEltWith φ hφ r hr g₂ x := by
  apply hφ
  simp only [map_mul, apply_corEltWith, mul_smul, mul_assoc, mul_inv_cancel_left]

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem corElt_eq_corEltWith :
    corElt φ hφ = corEltWith φ hφ (corRep φ) (mk_corRep φ) := rfl

variable [Fintype (G ⧸ φ.range)]

/-- The corestriction of a function `c : H → M` along `φ : H →* G`, computed with an arbitrary
section `r` of `G → G ⧸ φ(H)`. -/
noncomputable def corFunWith (c : H → M) (g : G) : M :=
  ∏ x : G ⧸ φ.range, r (g • x) • c (corEltWith φ hφ r hr g x)

omit [MulDistribMulAction H M] in
theorem corFun_eq_corFunWith (c : H → M) :
    corFun φ hφ c = corFunWith φ hφ (corRep φ) (mk_corRep φ) c := rfl

variable {φ hφ r hr} (hcomp : ∀ (h : H) (m : M), φ h • m = h • m)
include hcomp

theorem corFunWith_isMulCocycle₁ {c : H → M} (hc : IsMulCocycle₁ c) :
    IsMulCocycle₁ (corFunWith φ hφ r hr c) := by
  intro g₁ g₂
  have key : ∀ x, r ((g₁ * g₂) • x) • c (corEltWith φ hφ r hr (g₁ * g₂) x) =
      g₁ • (r (g₂ • x) • c (corEltWith φ hφ r hr g₂ x)) *
        r (g₁ • (g₂ • x)) • c (corEltWith φ hφ r hr g₁ (g₂ • x)) := by
    intro x
    rw [corEltWith_mul, hc, smul_mul', ← hcomp, smul_smul, mul_smul g₁ g₂ x,
      section_mul_apply_corEltWith, mul_smul]
  simp only [corFunWith]
  rw [Finset.prod_congr rfl (fun x _ => key x), Finset.prod_mul_distrib, ← Finset.smul_prod']
  congr 1
  exact Fintype.prod_equiv (MulAction.toPerm g₂) _ _ (fun x => rfl)

end CorFunWith

section Change

variable {G H M : Type*} [Group G] [Group H] [CommGroup M] [MulDistribMulAction G M]
  [MulDistribMulAction H M] {φ : H →* G} (hφ : Function.Injective φ)
  {r : G ⧸ φ.range → G} (hr : ∀ x, (r x : G ⧸ φ.range) = x)
  {r' : G ⧸ φ.range → G} (hr' : ∀ x, (r' x : G ⧸ φ.range) = x)

include hr hr' in
omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem section_inv_mul_section_mem (x : G ⧸ φ.range) : (r x)⁻¹ * r' x ∈ φ.range :=
  QuotientGroup.eq.mp ((hr x).trans (hr' x).symm)

/-- The element `h_x = φ⁻¹(r(x)⁻¹ r'(x)) ∈ H` comparing two sections, so that
`r'(x) = r(x) φ(h_x)`. -/
noncomputable def sectionDiff (x : G ⧸ φ.range) : H :=
  (MonoidHom.ofInjective hφ).symm ⟨_, section_inv_mul_section_mem hr hr' x⟩

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem apply_sectionDiff (x : G ⧸ φ.range) :
    φ (sectionDiff hφ hr hr' x) = (r x)⁻¹ * r' x :=
  MonoidHom.apply_ofInjective_symm hφ _

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem section_mul_apply_sectionDiff (x : G ⧸ φ.range) :
    r x * φ (sectionDiff hφ hr hr' x) = r' x := by
  rw [apply_sectionDiff, mul_inv_cancel_left]

omit [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction H M] in
theorem corEltWith_eq_sectionDiff (g : G) (x : G ⧸ φ.range) :
    corEltWith φ hφ r' hr' g x = (sectionDiff hφ hr hr' (g • x))⁻¹ *
      corEltWith φ hφ r hr g x * sectionDiff hφ hr hr' x := by
  apply hφ
  simp only [map_mul, map_inv, apply_corEltWith, apply_sectionDiff]
  group

variable [Fintype (G ⧸ φ.range)]

/-- The "norm" `∏ₓ r(x) • c(h_x)` comparing the corestrictions along two sections. -/
noncomputable def sectionDiffNorm (c : H → M) : M :=
  ∏ x : G ⧸ φ.range, r x • c (sectionDiff hφ hr hr' x)

variable (hcomp : ∀ (h : H) (m : M), φ h • m = h • m)
include hcomp

/-- Changing the section changes the corestricted cocycle by the coboundary of
`sectionDiffNorm`. -/
theorem corFunWith_eq_mul {c : H → M} (hc : IsMulCocycle₁ c) (g : G) :
    corFunWith φ hφ r' hr' c g = corFunWith φ hφ r hr c g *
      (g • sectionDiffNorm hφ hr hr' c / sectionDiffNorm hφ hr hr' c) := by
  set d := sectionDiff hφ hr hr'
  have hinv : ∀ h : H, h • c h⁻¹ = (c h)⁻¹ := by
    intro h
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hc, mul_inv_cancel, map_one_of_isMulCocycle₁ hc]
  have key : ∀ x, r' (g • x) • c (corEltWith φ hφ r' hr' g x) =
      g • (r x • c (d x)) * r (g • x) • c (corEltWith φ hφ r hr g x) /
        r (g • x) • c (d (g • x)) := by
    intro x
    rw [corEltWith_eq_sectionDiff hφ hr hr', mul_assoc, hc, hc, ← section_mul_apply_sectionDiff
      hφ hr hr' (g • x), mul_smul, hcomp, smul_mul', smul_smul, mul_inv_cancel, one_smul, hinv,
      smul_mul', smul_mul', smul_inv', ← hcomp, smul_smul, section_mul_apply_corEltWith,
      mul_smul, div_eq_mul_inv]
  simp only [corFunWith, sectionDiffNorm]
  rw [Finset.prod_congr rfl (fun x _ => key x), Finset.prod_div_distrib,
    Finset.prod_mul_distrib, ← Finset.smul_prod']
  have hperm : ∏ x : G ⧸ φ.range, r (g • x) • c (d (g • x)) =
      ∏ x : G ⧸ φ.range, r x • c (d x) :=
    Fintype.prod_equiv (MulAction.toPerm g) _ _ (fun x => rfl)
  rw [hperm, mul_comm (g • _), mul_div_assoc]

/-- Two sections give cohomologous corestricted cocycles. -/
theorem isMulCoboundary₁_corFunWith_div {c : H → M} (hc : IsMulCocycle₁ c) :
    IsMulCoboundary₁ (fun g => corFunWith φ hφ r' hr' c g / corFunWith φ hφ r hr c g) :=
  ⟨sectionDiffNorm hφ hr hr' c, fun g => by
    dsimp only
    rw [corFunWith_eq_mul hφ hr hr' hcomp hc, mul_div_cancel_left]⟩

end Change

section Cor

variable {G H M : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]
  {φ : H →* G} (hφ : Function.Injective φ) [Fintype (G ⧸ φ.range)]
  (hcomp : ∀ (h : H) (m : M), φ h • m = h • m)

omit [TopologicalSpace H] in
include hcomp in
/-- Continuity of the corestricted cocycle does not depend on the section, provided the orbit
maps `g ↦ g • m` are continuous. -/
theorem continuous_corFunWith {r r' : G ⧸ φ.range → G} (hr : ∀ x, (r x : G ⧸ φ.range) = x)
    (hr' : ∀ x, (r' x : G ⧸ φ.range) = x) {c : H → M} (hc : IsMulCocycle₁ c)
    (hact : ∀ m : M, Continuous fun g : G => g • m)
    (hcont : Continuous (corFunWith φ hφ r hr c)) :
    Continuous (corFunWith φ hφ r' hr' c) := by
  have : corFunWith φ hφ r' hr' c = fun g => corFunWith φ hφ r hr c g *
      (g • sectionDiffNorm hφ hr hr' c / sectionDiffNorm hφ hr hr' c) :=
    funext (corFunWith_eq_mul hφ hr hr' hcomp hc)
  rw [this]
  exact hcont.mul ((hact _).div' continuous_const)

omit [TopologicalSpace H] in
include hcomp in
theorem continuous_corFunWith_of_corFun {r : G ⧸ φ.range → G}
    (hr : ∀ x, (r x : G ⧸ φ.range) = x) {c : H → M} (hc : IsMulCocycle₁ c)
    (hact : ∀ m : M, Continuous fun g : G => g • m)
    (hcont : Continuous (corFun φ hφ c)) :
    Continuous (corFunWith φ hφ r hr c) :=
  continuous_corFunWith hφ hcomp (mk_corRep φ) hr hc hact hcont

variable (hcont : ∀ c : cocycles H M, Continuous (corFun φ hφ (c : H → M)))

/-- The corestriction of a class may be computed with an arbitrary section `r` of
`G → G ⧸ φ(H)`: it does not depend on the choice of coset representatives. -/
theorem cor_mk_eq_mk_corFunWith (c : cocycles H M) {r : G ⧸ φ.range → G}
    (hr : ∀ x, (r x : G ⧸ φ.range) = x) (hc : Continuous (corFunWith φ hφ r hr c)) :
    cor φ hφ hcomp hcont (mk c) =
      mk ⟨corFunWith φ hφ r hr c, hc, corFunWith_isMulCocycle₁ hcomp (isMulCocycle₁ c)⟩ := by
  rw [cor_mk, mk_eq_mk_iff]
  exact isMulCoboundary₁_corFunWith_div hφ hr (mk_corRep φ) hcomp (isMulCocycle₁ c)

omit hcont in
/-- The classes of the corestricted cocycles along two sections agree. -/
theorem mk_corFunWith_eq (c : cocycles H M) {r r' : G ⧸ φ.range → G}
    (hr : ∀ x, (r x : G ⧸ φ.range) = x) (hr' : ∀ x, (r' x : G ⧸ φ.range) = x)
    (hc : Continuous (corFunWith φ hφ r hr c)) (hc' : Continuous (corFunWith φ hφ r' hr' c)) :
    mk ⟨corFunWith φ hφ r hr c, hc, corFunWith_isMulCocycle₁ hcomp (isMulCocycle₁ c)⟩ =
      (mk ⟨corFunWith φ hφ r' hr' c, hc', corFunWith_isMulCocycle₁ hcomp (isMulCocycle₁ c)⟩ :
        ContH1 G M) := by
  rw [mk_eq_mk_iff]
  exact isMulCoboundary₁_corFunWith_div hφ hr' hr hcomp (isMulCocycle₁ c)

end Cor

end ContH1
