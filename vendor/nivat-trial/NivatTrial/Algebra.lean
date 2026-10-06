import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Laurent polynomial actions and finite support

The positive translation convention here agrees with the paper: a monomial
with exponent `u` sends `J z` to `J (z + u)`.
-/

namespace NivatTrial.Algebra

abbrev G := ℤ × ℤ
abbrev Laurent := AddMonoidAlgebra ℂ G

noncomputable section

/-- The Laurent polynomial action on a complex-valued configuration. -/
def act (f : Laurent) (J : G → ℂ) (z : G) : ℂ :=
  f.coeff.sum fun u c => c * J (z + u)

@[simp] theorem act_zero (J : G → ℂ) : act 0 J = 0 := by
  funext z
  simp [act]

@[simp] theorem act_zero_config (f : Laurent) : act f 0 = 0 := by
  funext z
  simp [act]

@[simp] theorem act_single (u : G) (c : ℂ) (J : G → ℂ) (z : G) :
    act (AddMonoidAlgebra.single u c) J z = c * J (z + u) := by
  simp [act]

theorem act_add (f g : Laurent) (J : G → ℂ) :
    act (f + g) J = act f J + act g J := by
  funext z
  simp [act, Finsupp.sum_add_index, add_mul]

theorem act_sub (f g : Laurent) (J : G → ℂ) :
    act (f - g) J = act f J - act g J := by
  funext z
  simp [act, Finsupp.sum_sub_index, sub_mul]

theorem act_add_config (f : Laurent) (J K : G → ℂ) :
    act f (J + K) = act f J + act f K := by
  funext z
  simp [act, mul_add, Finsupp.sum_add]

theorem act_sub_config (f : Laurent) (J K : G → ℂ) :
    act f (J - K) = act f J - act f K := by
  funext z
  simp [act, mul_sub, Finsupp.sum_sub]

theorem act_smul_config (f : Laurent) (c : ℂ) (J : G → ℂ) :
    act f (c • J) = c • act f J := by
  funext z
  simp [act, Finsupp.mul_sum, mul_left_comm]

theorem act_sum_config {ι : Type*} (f : Laurent) (s : Finset ι) (J : ι → G → ℂ) :
    act f (∑ i ∈ s, J i) = ∑ i ∈ s, act f (J i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, act_add_config, ih]

theorem act_sum {ι : Type*} (s : Finset ι) (p : ι → Laurent) (J : G → ℂ) :
    act (∑ i ∈ s, p i) J = ∑ i ∈ s, act (p i) J := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, act_add, ih]

theorem act_mul (f g : Laurent) (J : G → ℂ) :
    act (f * g) J = act f (act g J) := by
  funext z
  simp [act, AddMonoidAlgebra.mul_def, Finsupp.sum_sum_index,
    Finsupp.mul_sum, add_mul, mul_assoc, add_assoc]

/-- Laurent polynomial actions commute. -/
theorem act_comm (f g : Laurent) (J : G → ℂ) :
    act f (act g J) = act g (act f J) := by
  rw [← act_mul, ← act_mul, mul_comm]

theorem act_eq_zero_of_dvd {f g : Laurent} {J : G → ℂ}
    (hdivides : f ∣ g) (hannihilates : act f J = 0) : act g J = 0 := by
  obtain ⟨q, rfl⟩ := hdivides
  rw [mul_comm, act_mul, hannihilates, act_zero_config]

/-- The value of a Laurent polynomial at `(1, 1)`. -/
def coeffSum (f : Laurent) : ℂ := f.coeff.sum fun _ c => c

theorem act_const (f : Laurent) (b : ℂ) :
    act f (fun _ => b) = fun _ => coeffSum f * b := by
  funext z
  simp [act, coeffSum, Finsupp.sum_mul]

theorem act_const_eq_zero (f : Laurent) (h : coeffSum f = 0) (b : ℂ) :
    act f (fun _ => b) = 0 := by
  funext z
  simp [act_const, h]

/-- Reverse exponents to turn positive translations into convolution. -/
def flip (J : G →₀ ℂ) : Laurent :=
  AddMonoidAlgebra.ofCoeff (J.comapDomain (fun z => -z) neg_injective.injOn)

@[simp] theorem flip_coeff (J : G →₀ ℂ) (z : G) :
    (flip J).coeff z = J (-z) := rfl

theorem flip_ne_zero {J : G →₀ ℂ} (hJ : J ≠ 0) : flip J ≠ 0 := by
  intro h
  apply hJ
  ext z
  have hz := congrArg (fun f : Laurent => f.coeff (-z)) h
  simpa using hz

/-- The convolution coefficient is exactly the translated action. -/
theorem coeff_mul_flip (f : Laurent) (J : G →₀ ℂ) (z : G) :
    (f * flip J).coeff (-z) = act f J z := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp [act, add_comm]

/-- Lemma 1.2: a nonzero Laurent polynomial cannot annihilate a nonzero
finitely supported configuration. -/
theorem lemma1_2_finsupp {f : Laurent} {J : G →₀ ℂ}
    (hf : f ≠ 0) (hJ : J ≠ 0) : act f J ≠ 0 := by
  intro h
  have hprod : f * flip J = 0 := by
    ext z
    have hz := congrArg (fun K : G → ℂ => K (-z)) h
    simpa [← coeff_mul_flip] using hz
  exact mul_ne_zero hf (flip_ne_zero hJ) hprod

/-- Lemma 1.2 in the paper's ordinary-function representation. -/
theorem lemma1_2 {f : Laurent} {J : G → ℂ}
    (hf : f ≠ 0) (hJ : J ≠ 0) (hfinite : (Function.support J).Finite) :
    act f J ≠ 0 := by
  have hJ' : Finsupp.ofSupportFinite J hfinite ≠ 0 := by
    intro h
    apply hJ
    exact congrArg (fun K : G →₀ ℂ => (K : G → ℂ)) h
  exact lemma1_2_finsupp hf hJ'

end

end NivatTrial.Algebra
