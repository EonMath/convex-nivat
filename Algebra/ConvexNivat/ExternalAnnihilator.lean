import ConvexNivat.ReductionDefinitions
import Nivat.Algebra.LowComplexity
import Nivat.Algebra.ProductDifferences

namespace ConvexNivat
open scoped BigOperators

/-- Source 8.4(a). Kari–Szabados [11], An algebraic geometric approach to
Nivat's conjecture, Information and Computation 271 (2020), 104481.
The finite window need not be convex. -/
theorem external8_4a_obligation (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (S : Finset Lattice) (hS : S.Nonempty)
    (hlow : complexity ξ S ≤ S.card) : HasNontrivialIntegerAnnihilator ξ := by
  classical
  have hfinite : Nivat.FiniteRange ξ :=
    A.finite_toSet.subset (by rintro _ ⟨z, rfl⟩; exact hA z)
  have hpatterns : Nivat.patterns ξ S = patternSet ξ S := by
    unfold Nivat.patterns patternSet
    congr 1
    funext u z
    simp [Nivat.patternAt, pattern, add_comm]
  have hcomplexity : Nivat.complexity ξ S = complexity ξ S :=
    congrArg Set.ncard hpatterns
  let c : Nivat.Configuration ℚ := (Int.castRingHom ℚ) ∘ ξ
  have hc : Nivat.FiniteRange c := hfinite.map (Int.castRingHom ℚ)
  have hccomplexity : Nivat.complexity c S ≤ S.card := by
    change Nivat.complexity ((fun a : ℤ => (a : ℚ)) ∘ ξ) S ≤ S.card
    rw [Nivat.complexity_map ξ (Int.cast_injective) S, hcomplexity]
    exact hlow
  obtain ⟨f, hfne, hf⟩ :=
    Nivat.Algebra.exists_nonzero_annihilator c hc S hccomplexity
  obtain ⟨n, hn, F, hF⟩ := Nivat.Algebra.integer_filter_scale f
  have hFne : F ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hF
    exact hfne ((smul_eq_zero_iff_right (Int.cast_ne_zero.mpr hn)).mp hF.symm)
  have hFC : Nivat.Algebra.coefficientAct F ξ = 0 := by
    have he : Nivat.Algebra.coefficientAct (Nivat.Algebra.intLaurentCast F) c = 0 := by
      rw [Nivat.Algebra.coefficientAct_rat, hF, Nivat.Algebra.act_smul, hf, smul_zero]
    change Nivat.Algebra.coefficientAct
      (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℚ) F)
      ((Int.castRingHom ℚ) ∘ ξ) = 0 at he
    rw [Nivat.Algebra.coefficientAct_map] at he
    funext z
    exact Int.cast_eq_zero.mp (congrFun he z)
  refine ⟨F.coeff, AddMonoidAlgebra.coeff_eq_zero.not.mpr hFne, ?_⟩
  intro z
  rw [integerLaurentAction, ← Nivat.Algebra.coefficientAct_apply, hFC]
  rfl

end ConvexNivat
