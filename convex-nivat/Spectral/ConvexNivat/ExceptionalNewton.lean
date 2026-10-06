import ConvexNivat.ExceptionalAnnihilation
import ConvexNivat.ExceptionalNewtonHelpers
import ConvexNivat.SpectralNewton

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

theorem exceptional_polynomial_newton {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) :
    newtonPolygon (exceptionalPolynomial star periods) =
      (spectralZonotope star periods).carrier := by
  classical
  have hdir (i : Fin star.m) : exceptionalDirectionPolynomial star periods i ≠ 0 := by
    apply ne_zero_of_dvd_ne_zero (exceptional_polynomial_nonzero star periods)
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  unfold exceptionalPolynomial
  rw [finite_product_newton laurent_newton_polygon_mul _ _ (fun i _ => hdir i)]
  have hnewt (i : Fin star.m) : newtonPolygon (exceptionalDirectionPolynomial star periods i) =
      (fun t : ℝ => t • embed (star.component i).direction) ''
        Set.Icc (0 : ℝ) (exceptionalSpectrum star periods i).card := by
    apply finite_binomial_newton laurent_newton_polygon_mul _
      (primitive_ne_zero _ (star.component i).primitive)
    intro ζ hζ
    exact Polynomial.ne_zero_of_mem_nthRootsFinset (by simp) (Finset.mem_filter.mp hζ).1
  simp_rw [hnewt]
  rw [sum_parameter_segments]
  rfl

end
end ConvexNivat
