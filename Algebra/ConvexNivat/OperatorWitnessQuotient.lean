import ConvexNivat.OperatorWitness

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

private theorem witness_transform_coefficient (J : ScalarField)
    (hJ : ScalarHasFiniteSupport J) (z : ℤ × ℤ) :
    (finiteLaurentTransform (fieldToFinsupp J hJ)).coeff (-z) = J z := by
  exact Finsupp.mapDomain_apply_of_injective neg_injective _ z

private theorem witness_transform_translate_coefficient (J : ScalarField)
    (hJ : ScalarHasFiniteSupport J) (s z : ℤ × ℤ) :
    (translationMonomial s * finiteLaurentTransform (fieldToFinsupp J hJ)).coeff (-z) =
      J (z + s) := by
  rw [translationMonomial, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  have hneg : -s + -z = -(z + s) := by abel
  rw [hneg, witness_transform_coefficient]

private theorem witness_first_transform_relation (A : LaurentPolynomial)
    (J : (ℤ × ℤ) → ScalarField) (hJ : ∀ d, ScalarHasFiniteSupport (J d))
    (h₁ : applyInDifference A J = 0) (d : ℤ × ℤ) :
    A.coeff.sum (fun s c => c • finiteLaurentTransform
      (fieldToFinsupp (J (d + s)) (hJ (d + s)))) = 0 := by
  apply AddMonoidAlgebra.coeff_injective
  ext v
  obtain ⟨z, rfl⟩ := neg_surjective v
  have hz := congrFun (congrFun h₁ d) z
  change A.coeff.sum (fun s c => c * J (d + s) z) = 0 at hz
  simpa only [Finsupp.sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    witness_transform_coefficient, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hz

private theorem witness_second_transform_relation (A : LaurentPolynomial)
    (J : (ℤ × ℤ) → ScalarField) (hJ : ∀ d, ScalarHasFiniteSupport (J d))
    (h₂ : applyAtFirstPoint A J = 0) (d : ℤ × ℤ) :
    A.coeff.sum (fun s c => c • (translationMonomial s * finiteLaurentTransform
      (fieldToFinsupp (J (d - s)) (hJ (d - s))))) = 0 := by
  apply AddMonoidAlgebra.coeff_injective
  ext v
  obtain ⟨z, rfl⟩ := neg_surjective v
  have hz := congrFun (congrFun h₂ d) z
  change A.coeff.sum (fun s c => c * J (d - s) (z + s)) = 0 at hz
  simpa only [Finsupp.sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    witness_transform_translate_coefficient, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] using hz

private theorem witness_fraction_map_smul (c : ℂ) (p : LaurentPolynomial) :
    algebraMap LaurentPolynomial LaurentRationalField (c • p) =
      algebraMap ℂ LaurentRationalField c * algebraMap LaurentPolynomial LaurentRationalField p := by
  rw [Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply ℂ LaurentPolynomial LaurentRationalField]

private theorem witness_first_fraction_relation (A : LaurentPolynomial)
    (J : (ℤ × ℤ) → ScalarField) (hJ : ∀ d, ScalarHasFiniteSupport (J d))
    (h₁ : applyInDifference A J = 0) (d : ℤ × ℤ) :
    A.coeff.sum (fun s c => algebraMap ℂ LaurentRationalField c *
      witnessTransformValues J hJ (d + s)) = 0 := by
  have h := congrArg (algebraMap LaurentPolynomial LaurentRationalField)
    (witness_first_transform_relation A J hJ h₁ d)
  simpa only [Finsupp.sum, map_sum, map_zero, witness_fraction_map_smul,
    witnessTransformValues] using h

private theorem witness_second_fraction_relation (A : LaurentPolynomial)
    (J : (ℤ × ℤ) → ScalarField) (hJ : ∀ d, ScalarHasFiniteSupport (J d))
    (h₂ : applyAtFirstPoint A J = 0) (d : ℤ × ℤ) :
    A.coeff.sum (fun s c =>
      (algebraMap ℂ LaurentRationalField c *
        algebraMap LaurentPolynomial LaurentRationalField (translationMonomial s)) *
      witnessTransformValues J hJ (d - s)) = 0 := by
  have h := congrArg (algebraMap LaurentPolynomial LaurentRationalField)
    (witness_second_transform_relation A J hJ h₂ d)
  simpa only [Finsupp.sum, map_sum, map_zero, witness_fraction_map_smul,
    map_mul, witnessTransformValues, mul_assoc] using h

private theorem basisFunctional_single_coefficient
    (values : (ℤ × ℤ) → LaurentRationalField) (d : ℤ × ℤ) (c : LaurentRationalField) :
    laurentBasisFunctional values (AddMonoidAlgebra.single d c) = c * values d := by
  simp [laurentBasisFunctional, Finsupp.linearCombination_apply]

private theorem basisFunctional_single_mul
    (values : (ℤ × ℤ) → LaurentRationalField) (d : ℤ × ℤ) (q : WitnessLaurentAlgebra) :
    laurentBasisFunctional values (AddMonoidAlgebra.single d 1 * q) =
      q.coeff.sum (fun s c => c * values (d + s)) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single q]
  simp only [Finsupp.sum, Finset.mul_sum, map_sum,
    AddMonoidAlgebra.single_mul_single, one_mul, basisFunctional_single_coefficient]

private theorem basisFunctional_multiples (L : WitnessLaurentAlgebra →ₗ[LaurentRationalField]
      LaurentRationalField) (p : WitnessLaurentAlgebra)
    (hp : ∀ d : ℤ × ℤ, L (AddMonoidAlgebra.single d 1 * p) = 0)
    (q : WitnessLaurentAlgebra) : L (q * p) = 0 := by
  induction q using AddMonoidAlgebra.induction_on with
  | of d => exact hp d
  | add q r hq hr => simp only [add_mul, map_add, hq, hr, add_zero]
  | smul c q hq => rw [smul_mul_assoc, map_smul, hq, smul_zero]

theorem witnessTransformFunctional_kills_ideal (A : LaurentPolynomial)
    (J : (ℤ × ℤ) → ScalarField) (hJ : ∀ d, ScalarHasFiniteSupport (J d))
    (h₁ : applyInDifference A J = 0) (h₂ : applyAtFirstPoint A J = 0) :
    ∀ q ∈ biRecursionIdeal A, witnessTransformFunctional J hJ q = 0 := by
  have hg₁ : ∀ d : ℤ × ℤ, witnessTransformFunctional J hJ
      (AddMonoidAlgebra.single d 1 * differenceRecursionPolynomial A) = 0 := by
    intro d
    change laurentBasisFunctional (witnessTransformValues J hJ) _ = 0
    rw [basisFunctional_single_mul]
    change (A.coeff.mapRange (algebraMap ℂ LaurentRationalField) (map_zero _)).sum
      (fun s c => c * witnessTransformValues J hJ (d + s)) = 0
    rw [Finsupp.sum_mapRange_index (by intros; simp)]
    exact witness_first_fraction_relation A J hJ h₁ d
  have hg₂ : ∀ d : ℤ × ℤ, witnessTransformFunctional J hJ
      (AddMonoidAlgebra.single d 1 * firstPointRecursionPolynomial A) = 0 := by
    intro d
    change laurentBasisFunctional (witnessTransformValues J hJ) _ = 0
    simp only [firstPointRecursionPolynomial, Finsupp.sum, Finset.mul_sum,
      map_sum, AddMonoidAlgebra.single_mul_single, one_mul,
      basisFunctional_single_coefficient, ← sub_eq_add_neg]
    exact witness_second_fraction_relation A J hJ h₂ d
  intro q hq
  obtain ⟨r, t, rfl⟩ := Ideal.mem_span_pair.mp hq
  rw [map_add, basisFunctional_multiples _ _ hg₁ r,
    basisFunctional_multiples _ _ hg₂ t, add_zero]

theorem witness_confined_by_quotient_span (A : LaurentPolynomial)
    (B : Set (ℤ × ℤ)) (hspan : QuotientSpannedBy A B)
    (J : (ℤ × ℤ) → ScalarField) (hJ : ∀ d, ScalarHasFiniteSupport (J d))
    (h₁ : applyInDifference A J = 0) (h₂ : applyAtFirstPoint A J = 0)
    (hne : ∃ d, J d ≠ 0) : ∃ d ∈ B, J d ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let L := witnessTransformFunctional J hJ
  let P := (biRecursionIdeal A).restrictScalars LaurentRationalField
  have hker : P ≤ LinearMap.ker L := by
    intro q hq
    exact witnessTransformFunctional_kills_ideal A J hJ h₁ h₂ q hq
  let Lbar : BiRecursionQuotient A →ₗ[LaurentRationalField] LaurentRationalField :=
    (P.liftQ L hker).comp
      (Submodule.Quotient.restrictScalarsEquiv LaurentRationalField
        (biRecursionIdeal A)).symm.toLinearMap
  have hbar (d : ℤ × ℤ) : Lbar (quotientMonomial A d) = witnessTransformValues J hJ d := by
    simp only [Lbar, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      quotientMonomial, ← Ideal.Quotient.mk_eq_mk,
      Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply,
      L, witnessTransformFunctional, laurentBasisFunctional_monomial]
  have hspanKer : Submodule.span LaurentRationalField (quotientMonomial A '' B) ≤
      LinearMap.ker Lbar := by
    apply Submodule.span_le.mpr
    rintro q ⟨d, hd, rfl⟩
    change Lbar (quotientMonomial A d) = 0
    rw [hbar]
    have hz : fieldToFinsupp (J d) (hJ d) = 0 := by
      ext z
      change J d z = 0
      rw [h d hd]
      rfl
    simp [witnessTransformValues, hz, finiteLaurentTransform]
  rw [hspan] at hspanKer
  obtain ⟨d, hd⟩ := hne
  have hLd : witnessTransformValues J hJ d = 0 := by
    rw [← hbar]
    exact hspanKer (Submodule.mem_top)
  have hT : finiteLaurentTransform (fieldToFinsupp (J d) (hJ d)) = 0 := by
    apply IsFractionRing.injective LaurentPolynomial LaurentRationalField
    simpa only [witnessTransformValues, map_zero] using hLd
  apply hd
  funext z
  have hz := congrArg (fun p : LaurentPolynomial => p.coeff (-z)) hT
  simpa only [witness_transform_coefficient, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply, Pi.zero_apply] using hz

end

end ConvexNivat
