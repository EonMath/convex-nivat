import ConvexNivat.Operators

/-!
Reusable operator statement scaffolds for §§0.3,1,4–5.
All theorem bodies are intentional proof obligations for F-Reviewer approval.
-/

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

theorem applyLaurent_single (u : ℤ × ℤ) (c : ℂ) (f : ScalarField) (z : ℤ × ℤ) :
    applyLaurent (AddMonoidAlgebra.single u c) f z = c * f (z + u) := by
  simp [applyLaurent]

theorem applyLaurent_zero (f : ScalarField) : applyLaurent 0 f = 0 := by
  funext z
  simp [applyLaurent]

theorem applyLaurent_one (f : ScalarField) : applyLaurent 1 f = f := by
  funext z
  simp [AddMonoidAlgebra.one_def, applyLaurent_single]

theorem applyLaurent_add (p q : LaurentPolynomial) (f : ScalarField) :
    applyLaurent (p + q) f = applyLaurent p f + applyLaurent q f := by
  funext z
  simp [applyLaurent, Finsupp.sum_add_index, add_mul]

theorem applyLaurent_sub (p q : LaurentPolynomial) (f : ScalarField) :
    applyLaurent (p - q) f = applyLaurent p f - applyLaurent q f := by
  funext z
  simp [applyLaurent, Finsupp.sum_sub_index, sub_mul]

theorem applyLaurent_add_field (p : LaurentPolynomial) (f g : ScalarField) :
    applyLaurent p (f + g) = applyLaurent p f + applyLaurent p g := by
  funext z
  simp [applyLaurent, mul_add, Finsupp.sum_add]

theorem applyLaurent_smul_field (p : LaurentPolynomial) (c : ℂ) (f : ScalarField) :
    applyLaurent p (c • f) = c • applyLaurent p f := by
  funext z
  simp [applyLaurent, Finsupp.sum, Pi.smul_apply, smul_eq_mul,
    mul_left_comm, Finset.mul_sum]

theorem applyLaurent_mul (p q : LaurentPolynomial) (f : ScalarField) :
    applyLaurent (p * q) f = applyLaurent p (applyLaurent q f) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp [applyLaurent_zero]
  | add p q hp hq => simp only [add_mul, applyLaurent_add, hp, hq]
  | single u c =>
      induction q using AddMonoidAlgebra.induction_linear with
      | zero =>
          funext z
          simp [applyLaurent_zero, applyLaurent_single]
      | add p q hp hq =>
          simp only [mul_add, applyLaurent_add, applyLaurent_add_field, hp, hq]
      | single v d =>
          funext z
          simp [AddMonoidAlgebra.single_mul_single, applyLaurent_single,
            add_assoc, mul_assoc]

theorem applyLaurent_commute (p q : LaurentPolynomial) (f : ScalarField) :
    applyLaurent p (applyLaurent q f) = applyLaurent q (applyLaurent p f) := by
  rw [← applyLaurent_mul, ← applyLaurent_mul, mul_comm]

theorem applyLaurent_translate (p : LaurentPolynomial) (f : ScalarField) (u : ℤ × ℤ) :
    applyLaurent p (fun z => f (z + u)) = fun z => applyLaurent p f (z + u) := by
  funext z
  simp [applyLaurent, add_left_comm, add_comm]

theorem apply_difference (u : ℤ × ℤ) (f : ScalarField) (z : ℤ × ℤ) :
    applyLaurent (differencePolynomial u) f z = f (z + u) - f z := by
  simp [differencePolynomial, translationMonomial, applyLaurent_sub,
    applyLaurent_single, applyLaurent_one]

theorem difference_kills_period (u : ℤ × ℤ) (f : ScalarField)
    (hf : ∀ z, f (z + u) = f z) :
    applyLaurent (differencePolynomial u) f = 0 := by
  funext z
  simp [apply_difference, hf]

theorem difference_zero_iff_period (u : ℤ × ℤ) (f : ScalarField) :
    applyLaurent (differencePolynomial u) f = 0 ↔ ∀ z, f (z + u) = f z := by
  constructor
  · intro h z
    have hz := congrFun h z
    simpa [apply_difference, sub_eq_zero] using hz
  · exact difference_kills_period u f

theorem differencePolynomial_ne_zero {u : ℤ × ℤ} (hu : u ≠ 0) :
    differencePolynomial u ≠ 0 := by
  intro h
  have hsingle : AddMonoidAlgebra.single u (1 : ℂ) =
      AddMonoidAlgebra.single 0 (1 : ℂ) := by
    simpa [differencePolynomial, translationMonomial,
      sub_eq_zero, AddMonoidAlgebra.one_def] using h
  exact hu (AddMonoidAlgebra.single_left_injective one_ne_zero hsingle)

theorem laurent_mul_ne_zero {p q : LaurentPolynomial} (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 := by
  exact mul_ne_zero hp hq

theorem laurent_mul_injective_of_ne_zero {p : LaurentPolynomial} (hp : p ≠ 0) :
    Function.Injective (fun q : LaurentPolynomial => p * q) := by
  intro q r h
  exact mul_left_cancel₀ hp h

end

end ConvexNivat
