/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Restriction
import ContinuousKummerTheory.Kummer.Corestriction

/-!
# `cor ∘ res = [L : K]` on `H¹_cont(G_K, μ_n)`

For a finite subextension `L/K` of a Galois extension `Ω/K` (with `n`-th roots of elements of `K`
and `L` in `Ω`), the composite of restriction and corestriction on `H¹_cont(Gal(Ω/K), μ_n)` is
raising to the power `[L : K]`. We deduce it from the Kummer isomorphism: on Kummer classes it is
`κ_K(N_{L/K}(a)) = κ_K(a^{[L:K]})`.
-/

namespace KummerTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] (n : ℕ)
  [HasKummerRoots n K Ω] [HasKummerRoots n L Ω]

theorem corestriction_restriction (x : ContH1 Gal(Ω/K) (Mu n Ω)) :
    corestriction L n (restriction K L Ω Ω n x) = x ^ Module.finrank K L := by
  obtain ⟨a, rfl⟩ := kummer_surjective n K Ω x
  rw [restriction_kummer, corestriction_kummer, ← map_pow]
  congr 1
  ext
  simp [Algebra.norm_algebraMap]

end KummerTheory
