import ConvexNivat.ExceptionalPolynomialDefinitions
import ConvexNivat.CoreLattice

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

theorem exceptional_univariate_degree {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    (exceptionalUnivariate star periods i).natDegree =
      (exceptionalSpectrum star periods i).card := by
  classical
  unfold exceptionalUnivariate
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun ζ _ => Polynomial.monic_X_sub_C ζ)]
  simp

theorem exceptional_univariate_monic {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    (exceptionalUnivariate star periods i).Monic := by
  exact Polynomial.monic_prod_X_sub_C id _

theorem exceptional_univariate_constant_nonzero {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    (exceptionalUnivariate star periods i).eval 0 ≠ 0 := by
  classical
  unfold exceptionalUnivariate
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, zero_sub]
  apply Finset.prod_ne_zero_iff.mpr
  intro ζ hζ
  apply neg_ne_zero.mpr
  exact Polynomial.ne_zero_of_mem_nthRootsFinset (by simp)
    (Finset.mem_filter.mp hζ).1

theorem exceptional_polynomial_nonzero {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) : exceptionalPolynomial star periods ≠ 0 := by
  classical
  unfold exceptionalPolynomial exceptionalDirectionPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro ζ _
  have hv := primitive_ne_zero _ (star.component i).primitive
  intro h
  have hc := congrArg (fun f : LaurentPolynomial => f.coeff (star.component i).direction) h
  simp [translationMonomial, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single,
    hv] at hc

end
end ConvexNivat
