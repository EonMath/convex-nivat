import NivatTrial.CoefficientField
import NivatTrial.BiRecursion

/-! The finite Laurent transform and coefficient-field functional of §5.3.
The sign convention is `J(z) ↦ Σ J(z) X^(-z)`, so translating `J` by `s`
multiplies its transform by `X^s`. -/

namespace NivatTrial.WitnessTransform

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.CoefficientField
open NivatTrial.BiRecursion
open scoped Classical

noncomputable section

def flipLinear : (G →₀ ℂ) →ₗ[ℂ] Laurent where
  toFun := flip
  map_add' f g := by ext z; simp [flip_coeff]
  map_smul' c f := by ext z; simp [flip_coeff]

@[simp] theorem flipLinear_apply (f : G →₀ ℂ) : flipLinear f = flip f := rfl

def transform : (G →₀ ℂ) →ₗ[ℂ] K :=
  (IsScalarTower.toAlgHom ℂ Laurent K).toLinearMap.comp flipLinear

@[simp] theorem transform_apply (f : G →₀ ℂ) :
    transform f = algebraMap Laurent K (flip f) := rfl

theorem transform_injective : Function.Injective transform := by
  intro f g h
  have hflip : flip f = flip g := IsFractionRing.injective Laurent K h
  ext z
  have hz := congrArg (fun p : Laurent => p.coeff (-z)) hflip
  simpa using hz

theorem transform_ne_zero {f : G →₀ ℂ} (hf : f ≠ 0) : transform f ≠ 0 := by
  intro h
  apply hf
  exact transform_injective (h.trans (map_zero transform).symm)

def shift (f : G →₀ ℂ) (s : G) : G →₀ ℂ :=
  f.comapDomain (fun z => z + s) (add_left_injective s).injOn

@[simp] theorem shift_apply (f : G →₀ ℂ) (s z : G) : shift f s z = f (z + s) := rfl

theorem flip_shift (f : G →₀ ℂ) (s : G) : flip (shift f s) = monomial s * flip f := by
  ext z
  have h := coeff_mul_flip (monomial s) f (-z)
  simpa [flip_coeff, shift_apply, monomial] using h.symm

theorem transform_shift (f : G →₀ ℂ) (s : G) :
    transform (shift f s) = (xUnit s : K) * transform f := by
  simp only [transform_apply, flip_shift, map_mul, xUnit_val]

def diagonalCharacter : Multiplicative G →* R where
  toFun u := AddMonoidAlgebra.single (-u.toAdd) (xUnit u.toAdd : K)
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' u v := by simp [xUnit_add, add_comm]

def diagonalCoefficients : Laurent →ₐ[ℂ] R :=
  AddMonoidAlgebra.lift ℂ R G diagonalCharacter

@[simp] theorem diagonalCoefficients_single (s : G) (c : ℂ) :
    diagonalCoefficients (AddMonoidAlgebra.single s c) =
      AddMonoidAlgebra.single (-s) (algebraMap ℂ K c * (xUnit s : K)) := by
  simp [diagonalCoefficients, diagonalCharacter,
    Algebra.smul_def]

def functional (J : G → G →₀ ℂ) : R →ₗ[K] K where
  toFun f := f.coeff.sum fun d c => c * transform (J d)
  map_add' f g := by simp [Finsupp.sum_add_index, add_mul]
  map_smul' c f := by
    simp [Finsupp.sum_smul_index, smul_eq_mul, Finsupp.mul_sum, mul_assoc]

@[simp] theorem functional_single (J : G → G →₀ ℂ) (d : G) (c : K) :
    functional J (AddMonoidAlgebra.single d c) = c * transform (J d) := by
  simp [functional]

theorem includeCoefficients_sum (P : Laurent) :
    includeCoefficients P = ∑ s ∈ P.coeff.support,
      AddMonoidAlgebra.single s (algebraMap ℂ K (P.coeff s)) := by
  have hP : P = ∑ s ∈ P.coeff.support, AddMonoidAlgebra.single s (P.coeff s) :=
    (AddMonoidAlgebra.sum_coeff_single P).symm
  calc
    includeCoefficients P = includeCoefficients
      (∑ s ∈ P.coeff.support, AddMonoidAlgebra.single s (P.coeff s)) := congrArg _ hP
    _ = _ := by simp only [map_sum, includeCoefficients_single]

theorem diagonalCoefficients_sum (P : Laurent) :
    diagonalCoefficients P = ∑ s ∈ P.coeff.support,
      AddMonoidAlgebra.single (-s) (algebraMap ℂ K (P.coeff s) * (xUnit s : K)) := by
  have hP : P = ∑ s ∈ P.coeff.support, AddMonoidAlgebra.single s (P.coeff s) :=
    (AddMonoidAlgebra.sum_coeff_single P).symm
  calc
    diagonalCoefficients P = diagonalCoefficients
      (∑ s ∈ P.coeff.support, AddMonoidAlgebra.single s (P.coeff s)) := congrArg _ hP
    _ = _ := by simp only [map_sum, diagonalCoefficients_single]

theorem functional_monomial_include (J : G → G →₀ ℂ) (P : Laurent) (d : G) :
    functional J (AddMonoidAlgebra.single d 1 * includeCoefficients P) =
      ∑ s ∈ P.coeff.support, algebraMap ℂ K (P.coeff s) * transform (J (d + s)) := by
  rw [includeCoefficients_sum, Finset.mul_sum, map_sum]
  simp only [AddMonoidAlgebra.single_mul_single, one_mul, functional_single]

theorem functional_monomial_diagonal (J : G → G →₀ ℂ) (P : Laurent) (d : G) :
    functional J (AddMonoidAlgebra.single d 1 * diagonalCoefficients P) =
      ∑ s ∈ P.coeff.support,
        algebraMap ℂ K (P.coeff s) * ((xUnit s : K) * transform (J (d - s))) := by
  rw [diagonalCoefficients_sum, Finset.mul_sum, map_sum]
  simp only [AddMonoidAlgebra.single_mul_single, one_mul, functional_single,
    sub_eq_add_neg, mul_assoc]

theorem transformed_displacement_zero (J : G → G →₀ ℂ) (P : Laurent)
    (hrec : ∀ d z, displacementAction P (fun d z => J d z) d z = 0) (d : G) :
    ∑ s ∈ P.coeff.support, algebraMap ℂ K (P.coeff s) * transform (J (d + s)) = 0 := by
  have hzero : ∑ s ∈ P.coeff.support, P.coeff s • J (d + s) = 0 := by
    ext z
    simpa [displacementAction, Finsupp.sum] using hrec d z
  have h := congrArg transform hzero
  simpa only [map_sum, map_smul, map_zero, Algebra.smul_def] using h

theorem transformed_diagonal_zero (J : G → G →₀ ℂ) (P : Laurent)
    (hrec : ∀ d z, diagonalAction P (fun d z => J d z) d z = 0) (d : G) :
    ∑ s ∈ P.coeff.support,
      algebraMap ℂ K (P.coeff s) * ((xUnit s : K) * transform (J (d - s))) = 0 := by
  have hzero : ∑ s ∈ P.coeff.support, P.coeff s • shift (J (d - s)) s = 0 := by
    ext z
    simpa [diagonalAction, Finsupp.sum] using hrec d z
  have h := congrArg transform hzero
  simpa only [map_sum, map_smul, map_zero, transform_shift, Algebra.smul_def] using h

theorem functional_mul_zero_of_monomials (J : G → G →₀ ℂ) (p : R)
    (h : ∀ d : G, functional J (AddMonoidAlgebra.single d 1 * p) = 0) (g : R) :
    functional J (g * p) = 0 := by
  induction g using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_mul, hf, hg]
  | single d c =>
    have hs : (AddMonoidAlgebra.single d c : R) = c • AddMonoidAlgebra.single d 1 := by simp
    rw [hs, smul_mul_assoc, map_smul, h d, smul_zero]

theorem functional_mul_include_zero (J : G → G →₀ ℂ) (P : Laurent)
    (hrec : ∀ d z, displacementAction P (fun d z => J d z) d z = 0) (g : R) :
    functional J (g * includeCoefficients P) = 0 := by
  apply functional_mul_zero_of_monomials J _ _ g
  intro d
  rw [functional_monomial_include]
  exact transformed_displacement_zero J P hrec d

theorem functional_mul_diagonal_zero (J : G → G →₀ ℂ) (P : Laurent)
    (hrec : ∀ d z, diagonalAction P (fun d z => J d z) d z = 0) (g : R) :
    functional J (g * diagonalCoefficients P) = 0 := by
  apply functional_mul_zero_of_monomials J _ _ g
  intro d
  rw [functional_monomial_diagonal]
  exact transformed_diagonal_zero J P hrec d

/-- The functional kills the whole two-generated ideal, not just its generators. -/
theorem functional_ideal_zero (J : G → G →₀ ℂ) (P : Laurent)
    (hdisp : ∀ d z, displacementAction P (fun d z => J d z) d z = 0)
    (hdiag : ∀ d z, diagonalAction P (fun d z => J d z) d z = 0)
    (f : R) (hf : f ∈ Ideal.span {includeCoefficients P, diagonalCoefficients P}) :
    functional J f = 0 := by
  obtain ⟨g, h, heq⟩ := Ideal.mem_span_pair.mp hf
  rw [← heq, map_add, functional_mul_include_zero J P hdisp,
    functional_mul_diagonal_zero J P hdiag, add_zero]

end

end NivatTrial.WitnessTransform
