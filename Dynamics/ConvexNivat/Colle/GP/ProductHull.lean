import ConvexNivat.Colle.GP.ProductFaces
import ConvexNivat.Colle.Shared.AlgebraNewton
import ConvexNivat.Colle.Shared.AlgebraMembership
import ConvexNivat.ExceptionalNewtonHelpers

namespace ConvexNivat.Colle
open scoped BigOperators Pointwise
noncomputable section

private theorem product_cast (m : ℕ) (h : Fin m → Lattice) :
    integerPolynomialComplex (differenceFactors m h) = ∏ i, differencePolynomial (h i) := by
  have hcast (P : AddMonoidAlgebra ℤ Lattice) :
      integerPolynomialComplex P.coeff = integerCoefficientCast P := by
    ext z
    simp [integerPolynomialComplex, integerCoefficientCast]
  rw [differenceFactors, hcast, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp [integerCoefficientCast, differencePolynomial, translationMonomial,
    AddMonoidAlgebra.one_def]

private theorem product_binomial_ne (v : Lattice) (hv : v ≠ 0) :
    differencePolynomial v ≠ 0 := by
  intro he
  have hc := congrArg (fun p : LaurentPolynomial => p.coeff v) he
  simp [differencePolynomial, translationMonomial, AddMonoidAlgebra.one_def, hv] at hc

private theorem product_binomial_hull (v : Lattice) (hv : v ≠ 0) :
    newtonPolygon (differencePolynomial v) =
      (fun t : ℝ => t • embed v) '' Set.Icc (0 : ℝ) 1 := by
  have he := finite_binomial_newton laurent_newton_polygon_mul v hv
    ({1} : Finset ℂ) (by simp)
  simpa [differencePolynomial, AddMonoidAlgebra.one_def] using he

theorem reflected_difference_product_actual_zonotope (m : ℕ) (h : Fin m → Lattice)
    (hne : ∀ i, h i ≠ 0) :
    differenceFactors m h ≠ 0 ∧
      windowHull (supportWindow (differenceFactors m h)) = reflectedFactorHull m h := by
  classical
  have hcne : integerPolynomialComplex (differenceFactors m h) ≠ 0 := by
    rw [product_cast]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => product_binomial_ne _ (hne i)
  refine ⟨fun hz => hcne (by simp [hz, integerPolynomialComplex]), ?_⟩
  rw [supportWindow, convexLatticeWindow_hull, reflectedSupport, reflected_windowHull,
    ← integerPolynomialComplex_support, product_cast]
  change -newtonPolygon (∏ i, differencePolynomial (h i)) = _
  rw [finite_product_newton laurent_newton_polygon_mul _ _
    (fun i _ => product_binomial_ne _ (hne i))]
  simp_rw [product_binomial_hull _ (hne _)]
  have hs := sum_parameter_segments (fun i => embed (h i)) (fun _ => 1)
  simp only [Nat.cast_one] at hs
  rw [hs]
  have hneg (i : Fin m) : embed (-h i) = -embed (h i) := by
    ext <;> simp [embed]
  ext x
  simp only [Set.mem_neg, Set.mem_setOf_eq, reflectedFactorHull]
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨t, ht, ?_⟩
    have he := congrArg Neg.neg hx
    simpa only [neg_neg, hneg, smul_neg, ← Finset.sum_neg_distrib] using he
  · rintro ⟨t, ht, hx⟩
    refine ⟨t, ht, ?_⟩
    have he := congrArg Neg.neg hx
    simpa only [hneg, smul_neg, Finset.sum_neg_distrib, neg_neg] using he

theorem reflected_difference_product_interior (m : ℕ) (hm : 2 ≤ m)
    (h : Fin m → Lattice) (hne : ∀ i, h i ≠ 0)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j))) :
    (interior (windowHull (supportWindow (differenceFactors m h)))).Nonempty := by
  rw [(reflected_difference_product_actual_zonotope m h hne).2]
  let Z : IntegralZonotope m := ⟨fun i => -h i, fun _ => 1, by simp⟩
  rw [reflected_factor_hull_integral_zonotope m h Z (by intro i; simp [Z])]
  apply Z.interior_nonempty hm
  have hi : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    intro he
    have := congrArg Fin.val he
    simp at this
  have he := hpair hi
  simpa [Z, IntegralZonotope.firstDirection, IntegralZonotope.secondDirection,
    Nonparallel, det] using he

end
end ConvexNivat.Colle
