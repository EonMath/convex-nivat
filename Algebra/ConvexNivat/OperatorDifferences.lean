import ConvexNivat.OperatorAction

namespace ConvexNivat
open scoped BigOperators Pointwise
noncomputable section

theorem differenceProduct_split {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) (i : ι) (hi : i ∈ s) :
    differenceProduct s H = differencePolynomial (H i) * otherDifferenceProduct s H i := by
  exact (Finset.mul_prod_erase s (fun j => differencePolynomial (H j)) hi).symm

theorem differenceProduct_polynomial_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) :
    differenceProduct s H = ∑ C ∈ s.powerset,
      AddMonoidAlgebra.single (formalExponent H C) ((-1 : ℂ) ^ (s.card - C.card)) := by
  unfold differenceProduct differencePolynomial
  simp_rw [sub_eq_add_neg]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro C hC
  have hCs : C ⊆ s := Finset.mem_powerset.mp hC
  have hmono : (∏ i ∈ C, translationMonomial (H i)) =
      AddMonoidAlgebra.single (formalExponent H C) 1 := by
    simp [translationMonomial, AddMonoidAlgebra.prod_single, formalExponent]
  rw [hmono, Finset.prod_const, Finset.card_sdiff_of_subset hCs]
  have hneg : (-1 : LaurentPolynomial) = AddMonoidAlgebra.single 0 (-1 : ℂ) := by
    simp [AddMonoidAlgebra.one_def]
  rw [hneg, AddMonoidAlgebra.single_pow]
  simp

theorem differenceProduct_support_subset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) :
    (differenceProduct s H).coeff.support ⊆ formalExponentSet s H := by
  rw [differenceProduct_polynomial_expansion, AddMonoidAlgebra.coeff_sum]
  intro u hu
  have hu' := Finsupp.support_finsetSum hu
  obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu'
  have hEq : formalExponent H C = u := by
    simpa using (Finset.mem_singleton.mp (Finsupp.support_single_subset huC)).symm
  exact Finset.mem_image.mpr ⟨C, hC, hEq⟩

theorem difference_positive_multiple (u : ℤ × ℤ) (n : ℕ) :
    differencePolynomial (n • u) = differencePolynomial u * geometricTranslationSum u n := by
  have hp (k : ℕ) : translationMonomial u ^ k = translationMonomial (k • u) := by
    simp [translationMonomial, AddMonoidAlgebra.single_pow]
  unfold differencePolynomial geometricTranslationSum
  simp_rw [← hp]
  exact (mul_geom_sum (translationMonomial u) n).symm

theorem geometricTranslationSum_ne_zero (u : ℤ × ℤ) (n : ℕ) (hn : 0 < n) :
    geometricTranslationSum u n ≠ 0 := by
  have hsum : (geometricTranslationSum u n).coeff.sum (fun _ c => c) = (n : ℂ) := by
    unfold geometricTranslationSum
    rw [AddMonoidAlgebra.coeff_sum, ← Finsupp.sum_finsetSum_index
      (fun _ => rfl) (fun _ _ _ => rfl)]
    simp [translationMonomial]
  intro hzero
  rw [hzero] at hsum
  simpa using (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn) : (n : ℂ) ≠ 0) hsum.symm

theorem differenceProduct_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) (f : ScalarField) (z : ℤ × ℤ) :
    applyLaurent (differenceProduct s H) f z =
      ∑ C ∈ s.powerset, (-1 : ℂ) ^ (s.card - C.card) * f (z + formalExponent H C) := by
  rw [differenceProduct_polynomial_expansion]
  unfold applyLaurent
  rw [AddMonoidAlgebra.coeff_sum, ← Finsupp.sum_finsetSum_index
    (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  apply Finset.sum_congr rfl
  intro C hC
  simp

theorem otherDifferenceProduct_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) (i : ι) (f : ScalarField) (z : ℤ × ℤ) :
    applyLaurent (otherDifferenceProduct s H i) f z =
      ∑ C ∈ (s.erase i).powerset,
        (-1 : ℂ) ^ ((s.erase i).card - C.card) * f (z + formalExponent H C) := by
  exact differenceProduct_expansion (s.erase i) H f z

theorem differenceProduct_ne_zero {ι : Type*}
    (s : Finset ι) (H : ι → ℤ × ℤ) (hH : ∀ i ∈ s, H i ≠ 0) :
    differenceProduct s H ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i hi => differencePolynomial_ne_zero (hH i hi)

theorem differenceProduct_kills_period {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) (i : ι) (hi : i ∈ s) (f : ScalarField)
    (hf : ∀ z, f (z + H i) = f z) :
    applyLaurent (differenceProduct s H) f = 0 := by
  rw [differenceProduct_split s H i hi, mul_comm, applyLaurent_mul,
    difference_kills_period (H i) f hf]
  ext z
  simp [applyLaurent]

theorem differenceProduct_kills_constant {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (H : ι → ℤ × ℤ) (c : ℂ) :
    applyLaurent (differenceProduct s H) (fun _ => c) = 0 := by
  classical
  obtain ⟨i, hi⟩ := hs
  exact differenceProduct_kills_period s H i hi (fun _ => c) (fun _ => rfl)

end
end ConvexNivat
