import ConvexNivat.SpectralCyclotomic
import ConvexNivat.ExceptionalPolynomialDefinitions

open scoped BigOperators
namespace ConvexNivat
noncomputable section

private lemma direction_polynomial_eval {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    exceptionalDirectionPolynomial star periods i =
      (exceptionalUnivariate star periods i).eval₂ AddMonoidAlgebra.singleZeroRingHom
        (translationMonomial (star.component i).direction) := by
  classical
  simp only [exceptionalDirectionPolynomial, exceptionalUnivariate,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C, AddMonoidAlgebra.singleZeroRingHom_apply]
  rfl

private lemma direction_polynomial_integer {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    ∃ Q : AddMonoidAlgebra ℤ Lattice,
      AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℂ) Q =
        exceptionalDirectionPolynomial star periods i := by
  obtain ⟨P, hP⟩ := exceptional_univariate_integer_coefficients star periods i
  refine ⟨P.eval₂ AddMonoidAlgebra.singleZeroRingHom
    (AddMonoidAlgebra.single (star.component i).direction (1 : ℤ)), ?_⟩
  rw [direction_polynomial_eval, ← hP, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  · ext n
    simp
  · simp [translationMonomial]

/-- Remark 2.1', integer coefficient conclusion for A. -/
theorem exceptional_polynomial_integer_coefficients {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) :
    ∀ u : Lattice, ∃ n : ℤ, (n : ℂ) = (exceptionalPolynomial star periods).coeff u := by
  classical
  choose Q hQ using direction_polynomial_integer star periods
  have heq : AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℂ) (∏ i, Q i) =
      exceptionalPolynomial star periods := by
    simp [exceptionalPolynomial, map_prod, hQ]
  intro u
  refine ⟨(∏ i, Q i).coeff u, ?_⟩
  rw [← heq, AddMonoidAlgebra.coeff_mapRingHom]
  rfl

end
end ConvexNivat
