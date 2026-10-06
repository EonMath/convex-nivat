import ConvexNivat.QuotientDefinitions

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

private def firstCharacter : Multiplicative Lattice →* WitnessLaurentAlgebra where
  toFun u := AddMonoidAlgebra.single (-u.toAdd)
    (algebraMap LaurentPolynomial LaurentRationalField (translationMonomial u.toAdd))
  map_one' := by change AddMonoidAlgebra.single 0 ((algebraMap LaurentPolynomial LaurentRationalField) 1) = 1; simp [AddMonoidAlgebra.one_def]
  map_mul' u v := by
    change AddMonoidAlgebra.single (-(u.toAdd + v.toAdd)) _ = _
    rw [neg_add, AddMonoidAlgebra.single_mul_single]
    congr 1
    rw [← map_mul]
    congr 1
    simp [translationMonomial, AddMonoidAlgebra.single_mul_single]

private def firstHom : LaurentPolynomial →+* WitnessLaurentAlgebra :=
  AddMonoidAlgebra.liftNCRingHom
    ((AddMonoidAlgebra.singleZeroRingHom).comp (algebraMap ℂ LaurentRationalField))
    firstCharacter (fun _ _ => Commute.all _ _)

private theorem firstHom_apply (p : LaurentPolynomial) :
    firstHom p = firstPointRecursionPolynomial p := by
  unfold firstHom AddMonoidAlgebra.liftNCRingHom AddMonoidAlgebra.liftNC
  unfold firstPointRecursionPolynomial
  apply Finsupp.sum_congr
  intro s hs
  change AddMonoidAlgebra.single 0 _ * AddMonoidAlgebra.single (-s) _ = _
  simp [AddMonoidAlgebra.single_mul_single]

private def secondHom : LaurentPolynomial →+* WitnessLaurentAlgebra :=
  AddMonoidAlgebra.mapRingHom Lattice (algebraMap ℂ LaurentRationalField)

private theorem secondHom_apply (p : LaurentPolynomial) :
    secondHom p = differenceRecursionPolynomial p := rfl

/-- Inclusion needed to construct the source's natural quotient projections. -/
theorem spectral_bi_ideal_le_pair {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) : biRecursionIdeal family.polynomial ≤ family.pairIdeal i j := by
  classical
  apply Ideal.span_le.mpr
  intro x hx
  rcases hx with rfl | rfl
  · have h := Finset.dvd_prod_of_mem
      (fun k => secondHom (family.directionPolynomial k)) (Finset.mem_univ i)
    rw [← map_prod] at h
    exact Ideal.mem_of_dvd _ h (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal,
      ← secondHom_apply, FiniteSpectralFamily.secondPointFactor]))
  · have h := Finset.dvd_prod_of_mem
      (fun k => firstHom (family.directionPolynomial k)) (Finset.mem_univ j)
    rw [← map_prod, firstHom_apply, firstHom_apply] at h
    exact Ideal.mem_of_dvd _ h (Ideal.subset_span (by simp [FiniteSpectralFamily.firstPointFactor]))

theorem spectral_pair_selector_vanishes_other {m : ℕ} (family : FiniteSpectralFamily m)
    (i j i' j' : Fin m) (hother : i' ≠ i ∨ j' ≠ j) :
    Ideal.Quotient.mk (family.pairIdeal i' j') (spectralPairSelector family i j) = 0 := by
  classical
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  unfold spectralPairSelector
  rcases hother with hi | hj
  · apply Ideal.mul_mem_right
    apply Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩))
    exact Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal])
  · apply Ideal.mul_mem_left
    apply Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩))
    exact Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal])

end
end ConvexNivat
