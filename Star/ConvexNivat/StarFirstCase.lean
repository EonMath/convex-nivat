import ConvexNivat.StarFiniteSupport
import ConvexNivat.CorePatterns
import ConvexNivat.OperatorDifferences
import ConvexNivat.OperatorFiniteSupport

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

private theorem applyLaurent_sum {ι : Type*} (s : Finset ι)
    (q : ι → LaurentPolynomial) (f : ScalarField) :
    applyLaurent (∑ i ∈ s, q i) f = ∑ i ∈ s, applyLaurent (q i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [applyLaurent_zero]
  | @insert i s hi ih => simp [hi, applyLaurent_add, ih]

/-- The constant and coordinate indicators on actual patterns are independent
when a difference operator produces a nonzero field with finite support. -/
theorem indicator_pattern_linearIndependent {A : Type*} [DecidableEq A]
    (f : Configuration A) (a : A) (S : Finset Lattice)
    (D : LaurentPolynomial)
    (hconst : ∀ c : ℂ, applyLaurent D (fun _ => c) = 0)
    (hfinite : ScalarHasFiniteSupport (applyLaurent D (scalarColourIndicator f a)))
    (hne : applyLaurent D (scalarColourIndicator f a) ≠ 0) :
    LinearIndependent ℂ (fun i : Option S =>
      (fun γ : patternSet f S =>
        show ℂ from match i with
        | none => (1 : ℂ)
        | some s => if γ.val s = a then 1 else 0)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let q : LaurentPolynomial := ∑ s : S, AddMonoidAlgebra.single s.val (c (some s))
  have hq_apply : applyLaurent q (scalarColourIndicator f a) = fun _ => -c none := by
    funext z
    have hz := congrFun hc ⟨pattern f S z, ⟨z, rfl⟩⟩
    simp only [Fintype.sum_option, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, mul_one, Pi.zero_apply] at hz
    change c none + (∑ s : S, c (some s) *
      (if f (z + s.val) = a then 1 else 0)) = 0 at hz
    change applyLaurent (∑ s : S, AddMonoidAlgebra.single s.val (c (some s)))
      (scalarColourIndicator f a) z = -c none
    rw [applyLaurent_sum]
    rw [Finset.sum_apply]
    simpa only [applyLaurent_single, scalarColourIndicator] using
      eq_neg_of_add_eq_zero_right hz
  have hq_zero : q = 0 := by
    by_contra hq
    apply lemma_1_2 _ hfinite hne q hq
    rw [applyLaurent_commute, hq_apply, hconst]
  have hcoeff (s : S) : c (some s) = 0 := by
    have hs := congrArg (fun q : LaurentPolynomial => q.coeff s.val) hq_zero
    have hqs : q.coeff s.val = c (some s) := by
      simp only [q, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
      rw [Finset.sum_apply', Finset.sum_eq_single s]
      · exact Finsupp.single_eq_same
      · intro t _ hts
        exact Finsupp.single_eq_of_ne (fun h => hts (Subtype.ext h.symm))
      · simp
    simpa [hqs] using hs
  have hc_none : c none = 0 := by
    have hz := congrFun hc ⟨pattern f S 0, ⟨0, rfl⟩⟩
    simpa [Fintype.sum_option, hcoeff] using hz
  intro i
  cases i with
  | none => exact hc_none
  | some s => exact hcoeff s

/-- Counting version of the independence argument, for every finite window. -/
theorem complexity_lower_bound_of_finite_difference {A : Type*} [Finite A] [DecidableEq A]
    (f : Configuration A) (a : A) (S : Finset Lattice)
    (D : LaurentPolynomial)
    (hconst : ∀ c : ℂ, applyLaurent D (fun _ => c) = 0)
    (hfinite : ScalarHasFiniteSupport (applyLaurent D (scalarColourIndicator f a)))
    (hne : applyLaurent D (scalarColourIndicator f a) ≠ 0) :
    S.card + 1 ≤ complexity f S := by
  classical
  let : Fintype (patternSet f S) := (patternSet_finite f S).fintype
  have h := (indicator_pattern_linearIndependent f a S D hconst hfinite hne).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_coe] at h
  have hcard : Fintype.card (patternSet f S) = complexity f S := by
    unfold complexity
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rwa [hcard] at h

/-- Positive enlargement preserves the vanishing dichotomy whenever the original
result has actual finite support. -/
theorem differenceProduct_positive_enlargement_iff {ι : Type*}
    (s : Finset ι) (H : ι → Lattice) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (f : ScalarField)
    (hfinite : ScalarHasFiniteSupport (applyLaurent (differenceProduct s H) f)) :
    applyLaurent (differenceProduct s (fun i => n i • H i)) f = 0 ↔
      applyLaurent (differenceProduct s H) f = 0 := by
  classical
  let R : LaurentPolynomial := ∏ i ∈ s, geometricTranslationSum (H i) (n i)
  have hR : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    geometricTranslationSum_ne_zero (H i) (n i) (hn i hi)
  have hprod : differenceProduct s (fun i => n i • H i) =
      differenceProduct s H * R := by
    simp only [differenceProduct, difference_positive_multiple, Finset.prod_mul_distrib, R]
  rw [hprod, mul_comm, applyLaurent_mul]
  constructor
  · intro h
    by_contra hne
    exact lemma_1_2 _ hfinite hne R hR h
  · intro h
    rw [h]
    funext z
    simp [applyLaurent]

/-- Compare any two admissible choices through coordinatewise common positive multiples. -/
theorem starDifference_choices_iff_of_finite_support {p : ℕ} (d : StarData p)
    (P Q : StarPeriodData d) (f : ScalarField)
    (hP : ScalarHasFiniteSupport (applyLaurent (starDifference P) f))
    (hQ : ScalarHasFiniteSupport (applyLaurent (starDifference Q) f)) :
    applyLaurent (starDifference P) f = 0 ↔
      applyLaurent (starDifference Q) f = 0 := by
  have hcommon : (fun i => Q.multiplier i • P.vector i) =
      (fun i => P.multiplier i • Q.vector i) := by
    funext i
    simp only [StarPeriodData.vector, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    rw [mul_comm]
  have hPQ := differenceProduct_positive_enlargement_iff Finset.univ P.vector
    Q.multiplier (fun i _ => Q.multiplier_pos i) f hP
  have hQP := differenceProduct_positive_enlargement_iff Finset.univ Q.vector
    P.multiplier (fun i _ => P.multiplier_pos i) f hQ
  rw [hcommon] at hPQ
  exact hPQ.symm.trans hQP

private theorem star_colourIndicator_finite_support {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (a : ZMod p) :
    ScalarHasFiniteSupport (applyLaurent (starDifference P)
      (scalarColourIndicator d.configuration a)) := by
  have h := lemma_1_1 d P {0}
    (fun γ => if γ ⟨0, by simp⟩ = a then (1 : ℂ) else 0)
  have heq : starLocalFunction d {0}
      (fun γ => if γ ⟨0, by simp⟩ = a then (1 : ℂ) else 0) =
      scalarColourIndicator d.configuration a := by
    funext z
    simp [starLocalFunction, scalarColourIndicator, pattern]
  rwa [heq] at h

/-- Proposition 1.3, without convexity, for every nonempty finite window. -/
theorem proposition_1_3 {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (a : ZMod p)
    (ha : applyLaurent (starDifference P) (scalarColourIndicator d.configuration a) ≠ 0)
    (S : Finset Lattice) (hS : S.Nonempty) :
    S.card + 1 ≤ complexity d.configuration S := by
  rcases hS with ⟨_, _⟩
  have : NeZero p := ⟨d.prime.ne_zero⟩
  exact complexity_lower_bound_of_finite_difference d.configuration a S
    (starDifference P) (starDifference_kills_constant d P)
    (star_colourIndicator_finite_support d P a) ha

/-- Remark 1.4: the zero/nonzero dichotomy is invariant under positive enlargement
of each admissible period. -/
theorem starDifference_dichotomy_independent {p : ℕ} (d : StarData p)
    (P Q : StarPeriodData d) (a : ZMod p) :
    applyLaurent (starDifference P) (scalarColourIndicator d.configuration a) = 0 ↔
      applyLaurent (starDifference Q) (scalarColourIndicator d.configuration a) = 0 := by
  exact starDifference_choices_iff_of_finite_support d P Q
    (scalarColourIndicator d.configuration a)
    (star_colourIndicator_finite_support d P a) (star_colourIndicator_finite_support d Q a)

end
end ConvexNivat
