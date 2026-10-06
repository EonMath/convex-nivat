import ConvexNivat.ReductionJoinElementary

namespace ConvexNivat
open scoped BigOperators

theorem firstHalfPlaneData_admissible (p : ℕ) (θ : Configuration (ZMod p))
    (D : FirstHalfPlaneData p θ)
    (hlower : ∀ i, ∃ β : ℤ, β < D.threshold i ∧
      FullyPeriodicOn (D.field i) (lowerHalf (D.direction i) β)) :
    ∃ E : AdmissibleDecomposition p θ D.length,
      (∀ i, E.field i = D.field i) ∧
      (∀ i, E.period i = (D.multiplier i : ℤ) • D.direction i) ∧
      (∀ i, ¬ DoublyPeriodic (E.field i)) ∧
      Pairwise (fun i j => Nonparallel (E.period i) (E.period j)) ∧
      ∀ i, realDot (embed (E.period i)) (E.left i).normal = 0 := by
  classical
  choose β hβ hfull using hlower
  have hv : ∀ i, D.direction i ≠ 0 := fun i => primitive_ne_zero _ (D.primitive i)
  have hnormal : ∀ i, ((-(D.direction i).2 : ℝ), ((D.direction i).1 : ℝ)) ≠ 0 := by
    intro i h
    apply hv i
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    change -((D.direction i).2 : ℝ) = 0 at hfst
    change ((D.direction i).1 : ℝ) = 0 at hsnd
    have hzero₂ : (D.direction i).2 = 0 := by exact_mod_cast neg_eq_zero.mp hfst
    have hzero₁ : (D.direction i).1 = 0 := by exact_mod_cast hsnd
    exact Prod.ext hzero₁ hzero₂
  let U : Fin D.length → HalfPlane := fun i =>
    ⟨(-((D.direction i).2 : ℝ), ((D.direction i).1 : ℝ)), hnormal i,
      (D.threshold i : ℝ), false⟩
  let V : Fin D.length → HalfPlane := fun i =>
    ⟨(((D.direction i).2 : ℝ), -((D.direction i).1 : ℝ)), by
      intro h
      apply hv i
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      change ((D.direction i).2 : ℝ) = 0 at hfst
      change -((D.direction i).1 : ℝ) = 0 at hsnd
      have hzero₂ : (D.direction i).2 = 0 := by exact_mod_cast hfst
      have hzero₁ : (D.direction i).1 = 0 := by exact_mod_cast neg_eq_zero.mp hsnd
      exact Prod.ext hzero₁ hzero₂,
      -(β i : ℝ), false⟩
  have hU : ∀ i, (U i).carrier = upperHalf (D.direction i) (D.threshold i) := by
    intro i
    ext z
    have heq : realDot (embed z) (U i).normal = (det (D.direction i) z : ℝ) := by
      simp [U, realDot, embed, det]
      ring
    simp only [HalfPlane.carrier, U, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
    rw [heq]
    exact Int.cast_le
  have hV : ∀ i, (V i).carrier = lowerHalf (D.direction i) (β i) := by
    intro i
    ext z
    have heq : realDot (embed z) (V i).normal = -(det (D.direction i) z : ℝ) := by
      simp [V, realDot, embed, det]
      ring
    change -(β i : ℝ) ≤ realDot (embed z) (V i).normal ↔ det (D.direction i) z ≤ β i
    rw [heq, neg_le_neg_iff]
    exact Int.cast_le
  let period : Fin D.length → Lattice := fun i => (D.multiplier i : ℤ) • D.direction i
  have hperiod_nonzero : ∀ i, period i ≠ 0 := by
    intro i hz
    apply hv i
    have hscalar : (D.multiplier i : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (D.positive_multiplier i)
    exact Prod.ext
      ((mul_eq_zero.mp (by simpa [period] using congrArg Prod.fst hz)).resolve_left hscalar)
      ((mul_eq_zero.mp (by simpa [period] using congrArg Prod.snd hz)).resolve_left hscalar)
  let E : AdmissibleDecomposition p θ D.length := {
    field := D.field
    period := period
    period_nonzero := hperiod_nonzero
    has_period := D.has_period
    sum_eq := D.sum_eq
    left := U
    right := V
    disjoint := by
      intro i
      rw [hU, hV]
      apply Set.disjoint_left.mpr
      intro z hzu hzv
      change D.threshold i ≤ det (D.direction i) z at hzu
      change det (D.direction i) z ≤ β i at hzv
      exact (not_le_of_gt (hβ i)) (le_trans hzu hzv)
    full_left := by intro i; rw [hU]; exact D.full_upper i
    full_right := by intro i; rw [hV]; exact hfull i }
  refine ⟨E, fun _ => rfl, fun _ => rfl, D.not_double, ?_, ?_⟩
  · intro i j hij
    change det (period i) (period j) ≠ 0
    have heq : det (period i) (period j) =
        (D.multiplier i : ℤ) * (D.multiplier j : ℤ) * det (D.direction i) (D.direction j) := by
      simp [period, det]
      ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero
      (by exact_mod_cast Nat.ne_of_gt (D.positive_multiplier i))
      (by exact_mod_cast Nat.ne_of_gt (D.positive_multiplier j)))
      (D.distinct_directions hij)
  · intro i
    change realDot (embed (period i)) (U i).normal = 0
    simp [period, U, realDot, embed]
    ring

end ConvexNivat
