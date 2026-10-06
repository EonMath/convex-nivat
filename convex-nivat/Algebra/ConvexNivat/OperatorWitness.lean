import ConvexNivat.OperatorAction

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

theorem scalarEncoding_indicator_sum {A : Type*} [Fintype A] [DecidableEq A]
    (θ : (ℤ × ℤ) → A) (w : A → ℂ) :
    scalarEncoding θ w = ∑ a : A, w a • scalarColourIndicator θ a := by
  ext z
  simp [scalarEncoding, scalarColourIndicator, Finset.sum_apply, eq_comm]

theorem indicators_killed_encoding_killed {A : Type*} [Fintype A] [DecidableEq A]
    (θ : (ℤ × ℤ) → A) (D : LaurentPolynomial)
    (h : ∀ a, applyLaurent D (scalarColourIndicator θ a) = 0) (w : A → ℂ) :
    applyLaurent D (scalarEncoding θ w) = 0 := by
  rw [scalarEncoding_indicator_sum]
  ext z
  simp only [applyLaurent, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have hz := congrFun (h a) z
  change ∑ u ∈ D.coeff.support, D.coeff u * scalarColourIndicator θ a (z + u) = 0 at hz
  calc
    _ = w a * ∑ u ∈ D.coeff.support,
        D.coeff u * scalarColourIndicator θ a (z + u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = 0 := by rw [hz, mul_zero]

theorem quadraticWitness_zero_displacement {A : Type*} [Fintype A] [DecidableEq A]
    (θ : (ℤ × ℤ) → A) (D : LaurentPolynomial)
    (h : ∀ a, applyLaurent D (scalarColourIndicator θ a) = 0) (w : A → ℂ) :
    quadraticWitness D (scalarEncoding θ w) 0 = 0 := by
  have hw : (fun z => scalarEncoding θ w z * scalarEncoding θ w (z + 0)) =
      scalarEncoding θ (fun a => w a * w a) := by
    funext z
    simp [scalarEncoding]
  rw [quadraticWitness, hw]
  exact indicators_killed_encoding_killed θ D h (fun a => w a * w a)

theorem applyInDifference_quadratic (g D : LaurentPolynomial) (η : ScalarField)
    (d z : ℤ × ℤ) :
    applyInDifference g (quadraticWitness D η) d z =
      applyLaurent D (fun t => η t * applyLaurent g η (t + d)) z := by
  simp only [applyInDifference, quadraticWitness, applyLaurent, Finsupp.sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro t ht
  simp only [add_assoc]
  ring

theorem applyAtFirstPoint_quadratic (g D : LaurentPolynomial) (η : ScalarField)
    (d z : ℤ × ℤ) :
    applyAtFirstPoint g (quadraticWitness D η) d z =
      applyLaurent D (fun t => applyLaurent g η t * η (t + d)) z := by
  simp only [applyAtFirstPoint, quadraticWitness, applyLaurent, Finsupp.sum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro t ht
  have hfirst : z + t + u = z + u + t := by abel
  have hsecond : z + u + t + (d - t) = z + u + d := by abel
  rw [hfirst, hsecond]
  ring

theorem laurentBasisFunctional_monomial (values : (ℤ × ℤ) → LaurentRationalField)
    (d : ℤ × ℤ) :
    laurentBasisFunctional values (AddMonoidAlgebra.single d 1) = values d := by
  simp [laurentBasisFunctional, Finsupp.linearCombination_apply]

theorem differenceProduct_periodic_factor {ι : Type*}
    (s : Finset ι) (H : ι → ℤ × ℤ) (η b : ScalarField)
    (hb : ∀ i ∈ s, ∀ z, b (z + H i) = b z) :
    applyLaurent (differenceProduct s H) (η * b) =
      fun z => applyLaurent (differenceProduct s H) η z * b z := by
  classical
  induction s using Finset.induction_on generalizing η with
  | empty => simp only [differenceProduct, Finset.prod_empty, applyLaurent_one]; rfl
  | @insert i s hi ih =>
    have his : ∀ j ∈ s, ∀ z, b (z + H j) = b z := by
      intro j hj
      exact hb j (Finset.mem_insert_of_mem hj)
    have hii : ∀ z, b (z + H i) = b z := hb i (Finset.mem_insert_self i s)
    have hins : differenceProduct (insert i s) H =
        differencePolynomial (H i) * differenceProduct s H := by
      simp only [differenceProduct, Finset.prod_insert hi]
    rw [hins, applyLaurent_mul, applyLaurent_mul]
    rw [ih η his]
    ext z
    rw [apply_difference, apply_difference]
    simp only [hii]
    ring

theorem lemma_5_1 {ι : Type*}
    (s : Finset ι) (H : ι → ℤ × ℤ) (A : LaurentPolynomial) (η b : ScalarField)
    (hDη : applyLaurent (differenceProduct s H) η = 0)
    (hAη : applyLaurent A η = b)
    (hb : ∀ i ∈ s, ∀ z, b (z + H i) = b z) :
    applyInDifference A (quadraticWitness (differenceProduct s H) η) = 0 ∧
      applyAtFirstPoint A (quadraticWitness (differenceProduct s H) η) = 0 := by
  constructor
  · ext d z
    rw [applyInDifference_quadratic, hAη]
    have hbd : ∀ i ∈ s, ∀ t, b (t + H i + d) = b (t + d) := by
      intro i hi t
      have ht : t + H i + d = t + d + H i := by abel
      rw [ht]
      exact hb i hi (t + d)
    have hf := differenceProduct_periodic_factor s H η (fun t => b (t + d)) hbd
    change applyLaurent (differenceProduct s H) (η * (fun t => b (t + d))) z = 0
    rw [hf, hDη]
    simp
  · ext d z
    rw [applyAtFirstPoint_quadratic, hAη]
    have hf := differenceProduct_periodic_factor s H (fun t => η (t + d)) b hb
    have hη : applyLaurent (differenceProduct s H) (fun t => η (t + d)) = 0 := by
      rw [applyLaurent_translate, hDη]
      rfl
    have hcomm : (fun t => b t * η (t + d)) = (fun t => η (t + d)) * b := by
      ext t
      simp [mul_comm]
    rw [hcomm, hf, hη]
    simp

end

end ConvexNivat
