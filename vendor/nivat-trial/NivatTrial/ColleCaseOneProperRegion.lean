import NivatTrial.ColleBoundaryLimits

/-! An actual aperiodic field with a finite integer decomposition cannot
agree with a tangentially periodic reference on an entire half-plane.
Consequently every actual agreement region omits a point of that half-plane.
The conclusion concerns the original field, with no replacement by a limit. -/

namespace NivatTrial.ColleCaseOneProperRegion

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.Nonexpansive NivatTrial.Dynamics
open NivatTrial.ColleBoundaryLimits NivatTrial.ExternalInputs
open scoped Classical
noncomputable section

theorem exists_halfPlane_defect_of_tangent_period
    {M m : ℕ} (x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField x) m)
    (hnot : ¬IsPeriodic x) (u : Lattice) (hu : u ≠ 0)
    (h : Lattice) (hh : h ≠ 0) (htan : det u h = 0)
    (hp : IsPeriod p h) (b : ℤ) :
    ∃ z : Lattice, b ≤ det u z ∧ x z ≠ p z := by
  by_contra hnone
  have hagree (z : Lattice) (hz : b ≤ det u z) : x z = p z := by
    by_contra hn
    exact hnone ⟨z,hz,hn⟩
  have hhalf : ∀ z, b ≤ det u z → x (z+h) = x z := by
    intro z hz
    have hzh : b ≤ det u (z+h) := by
      simpa only [det_add_right,htan,add_zero] using hz
    exact (hagree (z+h) hzh).trans ((hp z).trans (hagree z hz).symm)
  obtain ⟨Q,hQ,hperiod⟩ := global_period_of_integer_hull_halfPlane_period E
    (self_mem_languageHull x) u hu h htan b hhalf
  apply hnot
  refine ⟨Q•h,?_,hperiod⟩
  intro he
  exact hh ((nsmul_eq_zero_iff_right (Nat.ne_of_gt hQ)).mp he)

/-- No closure or maximality of the agreement region is needed for this
obstruction: actual agreement alone prevents it from filling the half-plane. -/
theorem exists_halfPlane_point_outside_of_tangent_period
    {M m : ℕ} (x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField x) m)
    (hnot : ¬IsPeriodic x) (u : Lattice) (hu : u ≠ 0)
    (h : Lattice) (hh : h ≠ 0) (htan : det u h = 0)
    (hp : IsPeriod p h) (R : Set Lattice) (hxp : AgreeOn x p R) (b : ℤ) :
    ∃ z : Lattice, b ≤ det u z ∧ z ∉ R := by
  obtain ⟨z,hz,hneq⟩ := exists_halfPlane_defect_of_tangent_period
    x p E hnot u hu h hh htan hp b
  exact ⟨z,hz,fun hmem => hneq (hxp z hmem)⟩

theorem exists_halfPlane_point_outside_of_multiple_period
    {M m : ℕ} (x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField x) m)
    (hnot : ¬IsPeriodic x) (u : Lattice) (hu : u ≠ 0)
    (P : ℕ) (hP : 0 < P) (hp : IsPeriod p (P•u))
    (R : Set Lattice) (hxp : AgreeOn x p R) (b : ℤ) :
    ∃ z : Lattice, b ≤ det u z ∧ z ∉ R := by
  have hPu : P•u ≠ 0 := by
    intro he
    exact hu ((nsmul_eq_zero_iff_right (Nat.ne_of_gt hP)).mp he)
  exact exists_halfPlane_point_outside_of_tangent_period x p E hnot u hu
    (P•u) hPu (by simp only [det_nsmul_right,det_self,mul_zero]) hp R hxp b

theorem exists_halfPlane_point_outside_of_period
    {M m : ℕ} (x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField x) m)
    (hnot : ¬IsPeriodic x) (u : Lattice) (hu : u ≠ 0)
    (hp : IsPeriod p u) (R : Set Lattice) (hxp : AgreeOn x p R) (b : ℤ) :
    ∃ z : Lattice, b ≤ det u z ∧ z ∉ R :=
  exists_halfPlane_point_outside_of_tangent_period x p E hnot u hu
    u hu (det_self u) hp R hxp b

end
end NivatTrial.ColleCaseOneProperRegion
