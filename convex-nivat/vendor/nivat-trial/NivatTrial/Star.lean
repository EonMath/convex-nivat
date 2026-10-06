import NivatTrial.Dichotomy

/-! The original star hypotheses and their normalization into the data used by
the finite-difference and quadratic-witness arguments. The value group may be
any additive commutative group; a finite field is an instance. -/

namespace NivatTrial.Star

open NivatTrial.Algebra NivatTrial.Geometry NivatTrial.Periodicity
open NivatTrial.Quadratic
open scoped Classical

noncomputable section

structure Data (ι A : Type*) [Fintype ι] [AddCommGroup A] where
  direction : ι → G
  primitive : ∀ i, Int.gcd (direction i).1 (direction i).2 = 1
  independent : ∀ i j, i ≠ j → det (direction i) (direction j) ≠ 0
  component : ι → G → A
  multiplier : ι → ℕ
  multiplier_pos : ∀ i, 0 < multiplier i
  component_period : ∀ i, IsPeriod (component i) (multiplier i • direction i)
  not_doublyPeriodic : ∀ i, ¬IsDoublyPeriodic (component i)
  leftTail : ι → G → A
  rightTail : ι → G → A
  left_doublyPeriodic : ∀ i, IsDoublyPeriodic (leftTail i)
  right_doublyPeriodic : ∀ i, IsDoublyPeriodic (rightTail i)
  lower : ι → ℤ
  upper : ι → ℤ
  bounds : ∀ i, lower i ≤ upper i + 1
  left_agreement : ∀ i z, det (direction i) z < lower i → component i z = leftTail i z
  right_agreement : ∀ i z, upper i < det (direction i) z → component i z = rightTail i z

namespace Data

variable {ι A : Type*} [Fintype ι] [AddCommGroup A] (T : Data ι A)

def total (z : G) : A := ∑ i, T.component i z

def tails (j : ι × Bool) : G → A := if j.2 then T.rightTail j.1 else T.leftTail j.1

theorem tails_doublyPeriodic (j : ι × Bool) : IsDoublyPeriodic (T.tails j) := by
  rcases j with ⟨i, b⟩
  cases b
  · exact T.left_doublyPeriodic i
  · exact T.right_doublyPeriodic i

theorem direction_ne_zero (i : ι) : T.direction i ≠ 0 := by
  intro h
  have hg := T.primitive i
  simp [h] at hg

theorem component_ne_rightTail (i : ι) : T.component i ≠ T.rightTail i := by
  intro h
  exact T.not_doublyPeriodic i (h ▸ T.right_doublyPeriodic i)

theorem component_ne_leftTail (i : ι) : T.component i ≠ T.leftTail i := by
  intro h
  exact T.not_doublyPeriodic i (h ▸ T.left_doublyPeriodic i)

theorem exists_common_multipliers : ∃ κ : ι → ℕ, ∀ i,
    0 < κ i ∧ T.multiplier i ∣ κ i ∧
    IsPeriod (T.component i) (κ i • T.direction i) ∧
    ∀ j : ι × Bool, IsPeriod (T.tails j) (κ i • T.direction i) := by
  have hex (i : ι) := synchronize_direction_period (T.component i) T.tails
    (T.direction i) (T.multiplier i) (T.multiplier_pos i) (T.component_period i)
    T.tails_doublyPeriodic
  exact Classical.axiomOfChoice hex

/-- Common multiples exist by periodicity of all pure tails, without adding a
normalization hypothesis to the original star data. -/
def commonMultiplier : ι → ℕ := Classical.choose T.exists_common_multipliers

theorem commonMultiplier_spec (i : ι) :
    0 < T.commonMultiplier i ∧ T.multiplier i ∣ T.commonMultiplier i ∧
    IsPeriod (T.component i) (T.commonMultiplier i • T.direction i) ∧
    ∀ j : ι × Bool, IsPeriod (T.tails j) (T.commonMultiplier i • T.direction i) :=
  Classical.choose_spec T.exists_common_multipliers i

def normalized : Strips.StripSystem ι A where
  direction := T.direction
  period i := T.commonMultiplier i • T.direction i
  lower := T.lower
  upper := T.upper
  component := T.component
  leftTail := T.leftTail
  rightTail := T.rightTail
  component_period i := (T.commonMultiplier_spec i).2.2.1
  left_period i j := (T.commonMultiplier_spec j).2.2.2 (i, false)
  right_period i j := (T.commonMultiplier_spec j).2.2.2 (i, true)
  left_agreement := T.left_agreement
  right_agreement := T.right_agreement
  independent := T.independent

@[simp] theorem normalized_total : T.normalized.total = T.total := rfl

theorem normalized_period_nonzero (i : ι) : T.normalized.period i ≠ 0 :=
  nsmul_lattice_ne_zero (T.direction_ne_zero i) (T.commonMultiplier_spec i).1

theorem normalized_transverse (i j : ι) (hij : i ≠ j) :
    det (T.normalized.direction i) (T.normalized.period j) ≠ 0 := by
  change det (T.direction i) (T.commonMultiplier j • T.direction j) ≠ 0
  rw [det_nsmul_right]
  exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt (T.commonMultiplier_spec j).1))
    (T.independent i j hij)

/-- The first-case conclusion directly from (S1)--(S3). -/
theorem first_case_complexity [Nonempty ι] [Fintype A] (w : A → ℂ)
    (h : act T.normalized.operator (fun z => w (T.total z)) ≠ 0) (S : Finset G) :
    S.card + 1 ≤ patternComplexity T.total S :=
  T.normalized.first_case_complexity w h S

/-- From the original star hypotheses, either every finite window already has
the desired lower bound, or there is a nonzero finite-support quadratic witness.
Confining that witness to the exceptional zonotope remains a separate step. -/
theorem complexity_or_quadratic_witness [Nontrivial ι] [Fintype A]
    (w : A → ℂ) (hw : Function.Injective w) :
    (∀ S : Finset G, S.card + 1 ≤ patternComplexity T.total S) ∨
    (∃ d : G, d ≠ 0 ∧
      (Function.support (act T.normalized.operator
        (twoPoint (fun z => w (T.total z)) 0 d))).Finite ∧
      act T.normalized.operator (twoPoint (fun z => w (T.total z)) 0 d) ≠ 0) := by
  exact Dichotomy.first_case_or_quadratic_witness T.normalized w hw
    T.component_ne_rightTail T.normalized_transverse

end Data

end

end NivatTrial.Star
