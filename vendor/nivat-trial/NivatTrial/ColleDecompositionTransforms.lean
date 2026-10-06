import NivatTrial.ExternalInputs

/-! Exact translation and period normalization of the integer decomposition.
These transformations keep its actual components and its number of directions. -/

namespace NivatTrial.ColleDecompositionTransforms

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.ExternalInputs
open scoped Classical
noncomputable section

def translate {M n : ℕ} {x : Lattice → Fin M}
    (E : IntegerDecomposition (integerField x) n) (t : Lattice) :
    IntegerDecomposition (integerField (shift t x)) n where
  component i := shift t (E.component i)
  period := E.period
  period_ne_zero := E.period_ne_zero
  independent := E.independent
  component_period i := (E.component_period i).shift t
  sum_eq := by
    funext z
    have he := congrFun E.sum_eq (t+z)
    simpa only [Finset.sum_apply,integerField,encode,Function.comp_apply,shift_apply] using he

@[simp] theorem translate_period {M n : ℕ} {x : Lattice → Fin M}
    (E : IntegerDecomposition (integerField x) n) (t : Lattice) :
    (translate E t).period = E.period := rfl

def scalePeriods {f : Lattice → ℤ} {n : ℕ} (E : IntegerDecomposition f n)
    (q : Fin n → ℕ) (hq : ∀ i, 0 < q i) : IntegerDecomposition f n where
  component := E.component
  period i := q i • E.period i
  period_ne_zero i := fun he => E.period_ne_zero i
    ((nsmul_eq_zero_iff_right (Nat.ne_of_gt (hq i))).mp he)
  independent i j hij := by
    simp only [← natCast_zsmul,det_zsmul_left,det_zsmul_right]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt (hq j))
      (mul_ne_zero (by exact_mod_cast Nat.ne_of_gt (hq i)) (E.independent i j hij))
  component_period i := (E.component_period i).nsmul (q i)
  sum_eq := E.sum_eq

@[simp] theorem scalePeriods_period {f : Lattice → ℤ} {n : ℕ}
    (E : IntegerDecomposition f n) (q : Fin n → ℕ) (hq : ∀ i, 0 < q i) (i : Fin n) :
    (scalePeriods E q hq).period i = q i • E.period i := rfl

/-- Normalize the selected component direction to an actual period of the
reference, while retaining the original components and all other directions. -/
theorem exists_reference_normalized {A : Type*} {f : Lattice → ℤ} {n : ℕ}
    (E : IntegerDecomposition f n) (p : Lattice → A)
    (i : Fin n) (q : ℕ) (hq : 0 < q) (hp : IsPeriod p (q•E.period i)) :
    ∃ E' : IntegerDecomposition f n, E'.component = E.component ∧
      IsPeriod p (E'.period i) ∧ E'.period i = q•E.period i ∧
      ∀ j, j ≠ i → E'.period j = E.period j := by
  let r : Fin n → ℕ := fun j => if j = i then q else 1
  have hr : ∀ j, 0 < r j := by
    intro j
    dsimp [r]
    split_ifs <;> omega
  refine ⟨scalePeriods E r hr,rfl,?_,?_,?_⟩
  · simpa [r] using hp
  · simp [r]
  · intro j hji
    simp [r,hji]

end
end NivatTrial.ColleDecompositionTransforms
