import ConvexNivat.Operators

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

private theorem transform_coeff (J : (ℤ × ℤ) →₀ ℂ) (z : ℤ × ℤ) :
    (finiteLaurentTransform J).coeff z = J (-z) := by
  change (J.mapDomain (fun z => -z)) z = J (-z)
  simpa only [neg_neg] using
    Finsupp.mapDomain_apply_of_injective neg_injective J (-z)

theorem finiteLaurentTransform_injective :
    Function.Injective finiteLaurentTransform := by
  intro J K h
  ext z
  have hc := congrArg (fun p : LaurentPolynomial => p.coeff (-z)) h
  simpa only [transform_coeff, neg_neg] using hc

/-- This fixes the transform sign and connects the finite ring product to the field action. -/
theorem finiteConvolution_apply (p : LaurentPolynomial) (J : (ℤ × ℤ) →₀ ℂ) (z : ℤ × ℤ) :
    finiteConvolution p J z = applyLaurent p (fun t => J t) z := by
  change ((p * finiteLaurentTransform J).coeff.mapDomain (fun z => -z)) z = _
  rw [← neg_neg z, Finsupp.mapDomain_apply_of_injective neg_injective,
    AddMonoidAlgebra.coeff_mul_apply_left]
  simp only [neg_neg]
  change p.coeff.sum (fun u c => c * (finiteLaurentTransform J).coeff (-u + -z)) =
    p.coeff.sum (fun u c => c * J (z + u))
  simp only [transform_coeff, neg_add, neg_neg, add_comm]

theorem finiteLaurentTransform_convolution (p : LaurentPolynomial) (J : (ℤ × ℤ) →₀ ℂ) :
    finiteLaurentTransform (finiteConvolution p J) = p * finiteLaurentTransform J := by
  ext z
  rw [transform_coeff]
  change ((p * finiteLaurentTransform J).coeff.mapDomain (fun z => -z)) (-z) = _
  exact Finsupp.mapDomain_apply_of_injective neg_injective _ z

theorem applyLaurent_finite_support (p : LaurentPolynomial) (J : ScalarField)
    (hJ : ScalarHasFiniteSupport J) : ScalarHasFiniteSupport (applyLaurent p J) := by
  have heq : (fun z => finiteConvolution p (fieldToFinsupp J hJ) z) =
      applyLaurent p J := by
    funext z
    rw [finiteConvolution_apply]
    rfl
  rw [← heq]
  exact (finiteConvolution p (fieldToFinsupp J hJ)).hasFiniteSupport

/-- Lemma 1.2, at the source's full strength: arbitrary nonzero finite scalar support. -/
theorem lemma_1_2 (J : ScalarField) (hJ : ScalarHasFiniteSupport J) (hJne : J ≠ 0)
    (p : LaurentPolynomial) (hp : p ≠ 0) : applyLaurent p J ≠ 0 := by
  intro hzero
  have hconv : finiteConvolution p (fieldToFinsupp J hJ) = 0 := by
    ext z
    rw [finiteConvolution_apply]
    exact congrFun hzero z
  have hmul : p * finiteLaurentTransform (fieldToFinsupp J hJ) = 0 := by
    rw [← finiteLaurentTransform_convolution, hconv]
    simp [finiteLaurentTransform]
  have htransform := (mul_eq_zero.mp hmul).resolve_left hp
  have hfin : fieldToFinsupp J hJ = 0 :=
    finiteLaurentTransform_injective (by simpa [finiteLaurentTransform] using htransform)
  apply hJne
  exact congrArg (fun F : (ℤ × ℤ) →₀ ℂ => (fun z => F z)) hfin

/-- The stronger injection form useful for finite-support polynomial relations. -/
theorem applyLaurent_injective_on_finite_support (p : LaurentPolynomial) (hp : p ≠ 0)
    (J K : ScalarField) (hJ : ScalarHasFiniteSupport J) (hK : ScalarHasFiniteSupport K)
    (h : applyLaurent p J = applyLaurent p K) : J = K := by
  have hconv : finiteConvolution p (fieldToFinsupp J hJ) =
      finiteConvolution p (fieldToFinsupp K hK) := by
    ext z
    rw [finiteConvolution_apply, finiteConvolution_apply]
    exact congrFun h z
  have hmul : p * finiteLaurentTransform (fieldToFinsupp J hJ) =
      p * finiteLaurentTransform (fieldToFinsupp K hK) := by
    rw [← finiteLaurentTransform_convolution, ← finiteLaurentTransform_convolution, hconv]
  have hfin := finiteLaurentTransform_injective (mul_left_cancel₀ hp hmul)
  exact congrArg (fun F : (ℤ × ℤ) →₀ ℂ => (fun z => F z)) hfin

end

end ConvexNivat
