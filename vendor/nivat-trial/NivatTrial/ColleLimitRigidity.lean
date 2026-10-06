import NivatTrial.ColleMinimality

/-!
# Excluding a global period with two distinct singly periodic orbit limits

This is the period-direction core of Colle's Case 2. Every global period
passes to every language-hull point. A hull point which has one period but
is not doubly periodic forces every global period to be parallel to its own.
Two such limits in independent directions leave no nonzero global period.
-/

namespace NivatTrial.ColleLimitRigidity

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity

open scoped Classical
noncomputable section

theorem period_passes_to_languageHull {A : Type*}
    {x y : Lattice → A} {u : Lattice}
    (hu : IsPeriod x u) (hy : y ∈ languageHull x) :
    IsPeriod y u := by
  intro z
  obtain ⟨t, ht⟩ := hy {z, z + u}
  calc
    y (z + u) = x (t + (z + u)) := (ht _ (by simp)).symm
    _ = x (t + z) := by simpa [add_assoc] using hu (t + z)
    _ = y z := ht _ (by simp)

theorem period_parallel_of_singly_periodic_limit {A : Type*}
    {x y : Lattice → A} {h u : Lattice}
    (hy : y ∈ languageHull x) (hper : IsPeriod y h)
    (hnotDP : ¬IsDoublyPeriodic y)
    (hu : IsPeriod x u) : det u h = 0 := by
  by_contra htrans
  exact hnotDP ⟨u, h, htrans, period_passes_to_languageHull hu hy, hper⟩

/-- If two hull points have independent period directions but neither is
doubly periodic, their common source is nonperiodic. No ambiguity or region
structure is assumed in this period argument. -/
theorem aperiodic_of_two_singly_periodic_limits {A : Type*}
    (x y₁ y₂ : Lattice → A) (h k : Lattice)
    (hy₁ : y₁ ∈ languageHull x) (hy₂ : y₂ ∈ languageHull x)
    (hper₁ : IsPeriod y₁ h) (hper₂ : IsPeriod y₂ k)
    (hnot₁ : ¬IsDoublyPeriodic y₁) (hnot₂ : ¬IsDoublyPeriodic y₂)
    (hdet : det h k ≠ 0) : ¬IsPeriodic x := by
  rintro ⟨u, hu, hperiod⟩
  have hu₁ : det u h = 0 :=
    period_parallel_of_singly_periodic_limit hy₁ hper₁ hnot₁ hperiod
  have hu₂ : det u k = 0 :=
    period_parallel_of_singly_periodic_limit hy₂ hper₂ hnot₂ hperiod
  have hh : det h u = 0 := by rw [det_swap, hu₁]; simp
  have hk : det k u = 0 := by rw [det_swap, hu₂]; simp
  have hz : u = 0 :=
    (det_pair_injective h k hdet) (by
      apply Prod.ext <;> simp [hh, hk])
  exact hu hz

end
end NivatTrial.ColleLimitRigidity
