import ConvexNivat.Colle.Shared.AlgebraDefinitions

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

@[simp] theorem complexAction_zero (f : Configuration ℂ) (z : Lattice) :
    complexAction 0 f z = 0 := by simp [complexAction]

@[simp] theorem complexAction_add (φ ψ : ComplexLaurent) (f : Configuration ℂ) (z : Lattice) :
    complexAction (φ + ψ) f z = complexAction φ f z + complexAction ψ f z := by
  classical
  simp [complexAction, Finsupp.sum_add_index, add_mul]

@[simp] theorem complexAction_single (u : Lattice) (c : ℂ) (f : Configuration ℂ) (z : Lattice) :
    complexAction (AddMonoidAlgebra.single u c) f z = c * f (z - u) := by
  classical
  simp [complexAction]

theorem complexAction_mul (φ ψ : ComplexLaurent) (f : Configuration ℂ) (z : Lattice) :
    complexAction (φ * ψ) f z = complexAction φ (fun w => complexAction ψ f w) z := by
  induction φ using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, ha, hb]
  | single u c =>
    induction ψ using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [mul_add, ha, hb, mul_add]
    | single v d =>
      simp [AddMonoidAlgebra.single_mul_single, mul_assoc, sub_sub]

theorem complexAnnihilatorIdeal_membership (f : Configuration ℂ) (φ : ComplexLaurent) :
    φ ∈ complexAnnihilatorIdeal f ↔ ∀ z, complexAction φ f z = 0 := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => intro z; simp
    | add x y hx hy hxi hyi => intro z; simp [hxi z, hyi z]
    | smul a x hx hxi =>
      intro z
      change complexAction (a * x) f z = 0
      rw [complexAction_mul]
      have he : (fun w => complexAction x f w) = (fun _ => 0) := funext hxi
      rw [he]
      simp [complexAction]
  · intro h
    exact Ideal.subset_span h

theorem integerPolynomialComplex_support (ψ : IntegerLaurent) :
    (integerPolynomialComplex ψ).coeff.support = ψ.support := by
  exact Finsupp.support_mapRange_of_injective Int.cast_zero ψ Int.cast_injective

theorem integerPolynomialComplex_action (ψ : IntegerLaurent) (ξ : Configuration ℤ) (z : Lattice) :
    complexAction (integerPolynomialComplex ψ) (integerFieldComplex ξ) z =
      (laurentAction ψ ξ z : ℂ) := by
  classical
  unfold complexAction integerPolynomialComplex integerFieldComplex laurentAction
  rw [AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapRange_index]
  · simp [Finsupp.sum, Int.cast_sum, Int.cast_mul]
  · intro u; simp

theorem integer_complex_annihilator_support_bridge (ξ : Configuration ℤ)
    (ψ : IntegerLaurent) (hψ : ψ ≠ 0) :
    integerPolynomialComplex ψ ≠ 0 ∧
      complexSupportWindow (integerPolynomialComplex ψ) = supportWindow ψ ∧
      (Annihilates ψ ξ ↔ integerPolynomialComplex ψ ∈
        complexAnnihilatorIdeal (integerFieldComplex ξ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply hψ
    ext u
    have hh := congrArg (fun f : ComplexLaurent => f.coeff u) he
    simpa [integerPolynomialComplex] using hh
  · unfold complexSupportWindow supportWindow reflectedSupport
    rw [integerPolynomialComplex_support]
  · rw [complexAnnihilatorIdeal_membership]
    simp only [Annihilates, integerPolynomialComplex_action, Int.cast_eq_zero]

end
end ConvexNivat.Colle
