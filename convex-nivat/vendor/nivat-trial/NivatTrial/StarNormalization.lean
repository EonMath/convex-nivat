import NivatTrial.ReducedDecomposition
import NivatTrial.Star

/-! Primitive normalization of a reduced decomposition with aligned periodic tails. -/

namespace NivatTrial.StarNormalization

open NivatTrial.Geometry NivatTrial.Periodicity
open NivatTrial.ReducedDecomposition
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [AddCommGroup A]

/-- A nonzero lattice vector has a positive multiple decomposition with a
primitive vector. The primitive vector keeps the original orientation. -/
theorem exists_primitive_multiple (h : G) (hne : h ≠ 0) :
    ∃ k : ℕ, ∃ v : G, 0 < k ∧ Int.gcd v.1 v.2 = 1 ∧ h = k • v := by
  have hg : 0 < Int.gcd h.1 h.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hx := Int.gcd_dvd_left h.1 h.2
    have hy := Int.gcd_dvd_right h.1 h.2
    rw [hz] at hx hy
    simp only [Nat.cast_zero, zero_dvd_iff] at hx hy
    exact hne (Prod.ext hx hy)
  obtain ⟨k, x, y, hk, hprimitive, hx, hy⟩ := Int.exists_gcd_one' hg
  refine ⟨k, (x, y), hk, hprimitive, ?_⟩
  ext
  · simpa [nsmul_eq_mul, mul_comm] using hx
  · simpa [nsmul_eq_mul, mul_comm] using hy

structure AlignedTails (T : ReducedDecomposition.Data A) where
  leftTail : Fin T.count → G → A
  rightTail : Fin T.count → G → A
  left_doublyPeriodic : ∀ i, IsDoublyPeriodic (leftTail i)
  right_doublyPeriodic : ∀ i, IsDoublyPeriodic (rightTail i)
  leftBound : Fin T.count → ℤ
  rightBound : Fin T.count → ℤ
  left_agreement : ∀ i z,
    Geometry.det (T.period i) z ≤ leftBound i → T.component i z = leftTail i z
  right_agreement : ∀ i z,
    rightBound i ≤ Geometry.det (T.period i) z → T.component i z = rightTail i z

namespace Reduced

variable (T : ReducedDecomposition.Data A)

def multiplier (i : Fin T.count) : ℕ :=
  Classical.choose (exists_primitive_multiple (T.period i) (T.period_ne_zero i))

def direction (i : Fin T.count) : G :=
  Classical.choose (Classical.choose_spec
    (exists_primitive_multiple (T.period i) (T.period_ne_zero i)))

theorem primitive_spec (i : Fin T.count) :
    0 < multiplier T i ∧ Int.gcd (direction T i).1 (direction T i).2 = 1 ∧
      T.period i = multiplier T i • direction T i :=
  Classical.choose_spec (Classical.choose_spec
    (exists_primitive_multiple (T.period i) (T.period_ne_zero i)))

theorem independent (i j : Fin T.count) (hij : i ≠ j) :
    Geometry.det (direction T i) (direction T j) ≠ 0 := by
  intro hzero
  apply T.independent i j hij
  rw [(primitive_spec T i).2.2, (primitive_spec T j).2.2,
    ReducedDecomposition.det_nsmul_both, hzero, mul_zero]

theorem det_period (i : Fin T.count) (z : G) :
    Geometry.det (T.period i) z = (multiplier T i : ℤ) * Geometry.det (direction T i) z := by
  rw [(primitive_spec T i).2.2]
  simpa using ReducedDecomposition.det_nsmul_both (direction T i) z (multiplier T i) 1

end Reduced

namespace AlignedTails

variable {T : ReducedDecomposition.Data A} (L : AlignedTails T)

/-- Choosing farther integer cutoffs avoids division and works for either sign
of each original cutoff. -/
def lower (i : Fin T.count) : ℤ := min (L.leftBound i) 0

def upper (i : Fin T.count) : ℤ := max (L.rightBound i) 0

theorem bounds (i : Fin T.count) : L.lower i ≤ L.upper i + 1 := by
  have hl := min_le_right (L.leftBound i) (0 : ℤ)
  have hu := le_max_right (L.rightBound i) (0 : ℤ)
  dsimp [lower, upper]
  omega

theorem left_agreement_primitive (i : Fin T.count) (z : G)
    (hz : Geometry.det (Reduced.direction T i) z < L.lower i) :
    T.component i z = L.leftTail i z := by
  apply L.left_agreement i z
  rw [Reduced.det_period]
  have hk : (1 : ℤ) ≤ Reduced.multiplier T i := by
    exact_mod_cast (Reduced.primitive_spec T i).1
  have hz₀ : Geometry.det (Reduced.direction T i) z < 0 :=
    lt_of_lt_of_le hz (min_le_right _ _)
  have hzb : Geometry.det (Reduced.direction T i) z < L.leftBound i :=
    lt_of_lt_of_le hz (min_le_left _ _)
  nlinarith

theorem right_agreement_primitive (i : Fin T.count) (z : G)
    (hz : L.upper i < Geometry.det (Reduced.direction T i) z) :
    T.component i z = L.rightTail i z := by
  apply L.right_agreement i z
  rw [Reduced.det_period]
  have hk : (1 : ℤ) ≤ Reduced.multiplier T i := by
    exact_mod_cast (Reduced.primitive_spec T i).1
  have hz₀ : 0 < Geometry.det (Reduced.direction T i) z :=
    lt_of_le_of_lt (le_max_right _ _) hz
  have hza : L.rightBound i < Geometry.det (Reduced.direction T i) z :=
    lt_of_le_of_lt (le_max_left _ _) hz
  nlinarith

def toStar : Star.Data (Fin T.count) A where
  direction := Reduced.direction T
  primitive i := (Reduced.primitive_spec T i).2.1
  independent := Reduced.independent T
  component := T.component
  multiplier := Reduced.multiplier T
  multiplier_pos i := (Reduced.primitive_spec T i).1
  component_period i := by
    rw [← (Reduced.primitive_spec T i).2.2]
    exact T.component_period i
  not_doublyPeriodic := T.not_doublyPeriodic
  leftTail := L.leftTail
  rightTail := L.rightTail
  left_doublyPeriodic := L.left_doublyPeriodic
  right_doublyPeriodic := L.right_doublyPeriodic
  lower := L.lower
  upper := L.upper
  bounds := L.bounds
  left_agreement := L.left_agreement_primitive
  right_agreement := L.right_agreement_primitive

@[simp] theorem toStar_component : L.toStar.component = T.component := rfl

@[simp] theorem toStar_total : L.toStar.total = T.total := rfl

end AlignedTails

theorem exists_star (T : ReducedDecomposition.Data A)
    (left right : Fin T.count → G → A) (a b : Fin T.count → ℤ)
    (hleft : ∀ i, IsDoublyPeriodic (left i))
    (hright : ∀ i, IsDoublyPeriodic (right i))
    (hleftAgreement : ∀ i z,
      Geometry.det (T.period i) z ≤ b i → T.component i z = left i z)
    (hrightAgreement : ∀ i z,
      a i ≤ Geometry.det (T.period i) z → T.component i z = right i z) :
    ∃ U : Star.Data (Fin T.count) A, U.total = T.total := by
  let L : AlignedTails T := {
    leftTail := left
    rightTail := right
    left_doublyPeriodic := hleft
    right_doublyPeriodic := hright
    leftBound := b
    rightBound := a
    left_agreement := hleftAgreement
    right_agreement := hrightAgreement }
  exact ⟨L.toStar, rfl⟩

end

end NivatTrial.StarNormalization
