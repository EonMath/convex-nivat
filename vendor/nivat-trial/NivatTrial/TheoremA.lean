import NivatTrial.StarWindow
import NivatTrial.QuotientSpanning
import NivatTrial.QuotientRelations
import NivatTrial.Confinement

/-! The complexity lower bound for star configurations, from their original
periodic-component and two-tail hypotheses.  The theorem has no spectral,
background, quotient-spanning, or witness-confinement premises. -/

namespace NivatTrial.TheoremA

open NivatTrial.Algebra NivatTrial.Quadratic NivatTrial.BiRecursion
open NivatTrial.GlobalSpectrum NivatTrial.SpectralGeometry NivatTrial.StarRecurrence
open NivatTrial.CoefficientField NivatTrial.QuotientIdeals NivatTrial.QuotientRelations
open NivatTrial.QuotientSpanning NivatTrial.WitnessTransform NivatTrial.Confinement
open NivatTrial.LatticePolygon
open scoped Classical Pointwise

noncomputable section

variable {ι α : Type*} [Fintype ι] [Nontrivial ι] [AddCommGroup α] [Fintype α]
    (T : Star.Data ι α)

/-- Proposition 5.3 with every input derived from the original star hypotheses
and the second branch of the colour-indicator dichotomy. -/
theorem confined_witness
    (hcase : ∀ a : α, act T.normalized.operator (Dichotomy.indicator T.total a) = 0) :
    ∃ d : G, Zonotope.embed d ∈
      Zonotope.zonotope (generators T) - Zonotope.zonotope (generators T) ∧
      d ≠ 0 ∧ witness T.normalized.operator (encodedField T) d ≠ 0 := by
  have hall := Dichotomy.annihilate_all_observations T.total T.normalized.operator hcase
  have hD : act T.normalized.operator (encodedField T) = 0 := hall (scalarEncoding T)
  obtain ⟨d₀, _, hd₀⟩ := StarRecurrence.second_case_witness T hcase
  have hker : ∀ f : R, (projection T.direction (eigenvalues T)).toLinearMap f = 0 →
      f ∈ Ideal.span {includeCoefficients (polynomial T), diagonalCoefficients (polynomial T)} := by
    intro f hf
    rw [polynomial_eq_eigenvalues, includeCoefficients_product, diagonalCoefficients_product]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hf
  have hspan : Submodule.span K (projectedMonomials
      (projection T.direction (eigenvalues T)).toLinearMap
      (differenceRegion T.direction (eigenvalues T))) = ⊤ := by
    rw [projectedMonomials_eq_image]
    exact lemma5_2 T.direction (eigenvalues T) T.direction_ne_zero T.independent
  have hsquare : act T.normalized.operator
      (fun z => encodedField T z * encodedField T z) = 0 :=
    hall (fun a => scalarEncoding T a * scalarEncoding T a)
  exact biRecursion_nonzero_witness_confined (polynomial T) T.normalized.operator
    (encodedField T) (projection T.direction (eigenvalues T)).toLinearMap
    (differenceRegion T.direction (eigenvalues T)) (witness_finite T)
    (actual_bi_recursion T hD) hker hspan ⟨d₀, hd₀⟩ hsquare

/-- **Theorem A (Theorem 7.3).** A star configuration has more patterns than
sites in every finite lattice-convex window.  In fact the statement also covers
the empty window, which has one pattern. -/
theorem complexity_lower_bound (S : Finset G) (hS : IsLatticeConvex S) :
    S.card + 1 ≤ patternComplexity T.total S := by
  by_cases hfirst : ∃ a : α, act T.normalized.operator (Dichotomy.indicator T.total a) ≠ 0
  · obtain ⟨a, ha⟩ := hfirst
    exact T.first_case_complexity (fun x => if x = a then 1 else 0) ha S
  · have hcase : ∀ a : α, act T.normalized.operator (Dichotomy.indicator T.total a) = 0 := by
      simpa only [not_exists, not_not] using hfirst
    have hD : act T.normalized.operator (encodedField T) = 0 :=
      Dichotomy.annihilate_all_observations T.total T.normalized.operator hcase (scalarEncoding T)
    obtain ⟨d, hd, _, hnonzero⟩ := confined_witness T hcase
    exact StarWindow.complexity_of_confined_witness T S hS hD d hd hnonzero

end

end NivatTrial.TheoremA
