import NivatTrial.QuotientSupport
import NivatTrial.WitnessTransform

/-! The split directional products agree with the two coefficient transforms
used by the genuine bi-recursion functional. -/

namespace NivatTrial.QuotientRelations

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.CoefficientField
open NivatTrial.QuotientFactors NivatTrial.QuotientIdeals NivatTrial.QuotientSupport
open NivatTrial.WitnessTransform
open scoped BigOperators Classical

noncomputable section

@[simp] theorem includeCoefficients_scalar (c : ℂ) :
    includeCoefficients (scalar c) = algebraMap K R (algebraMap ℂ K c) := by
  simp [scalar_apply]

@[simp] theorem diagonalCoefficients_scalar (c : ℂ) :
    diagonalCoefficients (scalar c) = algebraMap K R (algebraMap ℂ K c) := by
  simp [scalar_apply]

theorem includeCoefficients_directionProduct (v : G) (S : Finset ℂˣ) :
    includeCoefficients (∏ c ∈ S, binomial v (c : ℂ)) = aFactor v S := by
  simp only [aFactor, rootPolynomial, map_prod, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, binomial, monomial, includeCoefficients_single,
    includeCoefficients_scalar, map_one, ← constantUnit_val]
  rfl

theorem diagonalCoefficients_directionProduct (v : G) (S : Finset ℂˣ) :
    diagonalCoefficients (∏ c ∈ S, binomial v (c : ℂ)) = cFactor v S := by
  simp only [cFactor, rootPolynomial, map_prod, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, binomial, monomial, diagonalCoefficients_single,
    diagonalCoefficients_scalar, map_one, one_mul, ← constantUnit_val, wCharacter_val]

variable {ι : Type*} [Fintype ι]

theorem includeCoefficients_product (v : ι → G) (S : ι → Finset ℂˣ) :
    includeCoefficients (∏ i, ∏ c ∈ S i, binomial (v i) (c : ℂ)) = aProduct v S := by
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => includeCoefficients_directionProduct (v i) (S i))

theorem diagonalCoefficients_product (v : ι → G) (S : ι → Finset ℂˣ) :
    diagonalCoefficients (∏ i, ∏ c ∈ S i, binomial (v i) (c : ℂ)) = cProduct v S := by
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => diagonalCoefficients_directionProduct (v i) (S i))

end

end NivatTrial.QuotientRelations
