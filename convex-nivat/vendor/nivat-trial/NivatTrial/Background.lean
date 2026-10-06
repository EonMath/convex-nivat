import NivatTrial.Differences
import NivatTrial.Periodicity

/-! Removing finite defects from annihilated configurations. This is the last
algebraic step in the background argument of §3. The sector argument which
produces a finite exceptional set is a separate, unfinished geometric input. -/

namespace NivatTrial.Background

open NivatTrial.Algebra NivatTrial.Differences NivatTrial.Periodicity

noncomputable section

theorem eq_of_annihilated_finite_difference (D : Laurent) (hD : D ≠ 0)
    (F B : G → ℂ) (hF : act D F = 0) (hB : act D B = 0)
    (hfinite : (Function.support (F - B)).Finite) : F = B := by
  by_contra hne
  have hnonzero : F - B ≠ 0 := sub_ne_zero.mpr hne
  have hzero : act D (F - B) = 0 := by rw [act_sub_config, hF, hB, sub_self]
  exact lemma1_2 hD hnonzero hfinite hzero

theorem eq_of_annihilated_agreement (D : Laurent) (hD : D ≠ 0)
    (F B : G → ℂ) (hF : act D F = 0) (hB : act D B = 0)
    (E : Set G) (hE : E.Finite) (hagrees : ∀ z, z ∉ E → F z = B z) : F = B := by
  apply eq_of_annihilated_finite_difference D hD F B hF hB
  apply hE.subset
  intro z hz
  by_contra hnot
  exact hz (sub_eq_zero.mpr (hagrees z hnot))

/-- An almost-period with only finitely many defects is a true period when a
nonzero Laurent operator annihilates the configuration. -/
theorem period_of_finite_defect (D : Laurent) (hD : D ≠ 0) (F : G → ℂ)
    (hF : act D F = 0) (h : G)
    (hfinite : (Function.support (act (difference h) F)).Finite) : IsPeriod F h := by
  apply period_of_difference_eq_zero
  by_contra hne
  apply lemma1_2 hD hne hfinite
  rw [act_comm, hF, act_zero_config]

theorem period_of_period_outside_finite (D : Laurent) (hD : D ≠ 0) (F : G → ℂ)
    (hF : act D F = 0) (h : G) (E : Set G) (hE : E.Finite)
    (hperiod : ∀ z, z ∉ E → F (z + h) = F z) : IsPeriod F h := by
  apply period_of_finite_defect D hD F hF h
  apply hE.subset
  intro z hz
  by_contra hnot
  apply hz
  rw [act_difference, hperiod z hnot, sub_self]

theorem doublyPeriodic_of_finite_defects (D : Laurent) (hD : D ≠ 0) (F : G → ℂ)
    (hF : act D F = 0) (h k : G) (hdet : Geometry.det h k ≠ 0)
    (hh : (Function.support (act (difference h) F)).Finite)
    (hk : (Function.support (act (difference k) F)).Finite) : IsDoublyPeriodic F :=
  ⟨h, k, hdet, period_of_finite_defect D hD F hF h hh,
    period_of_finite_defect D hD F hF k hk⟩

/-- The exceptional polynomial preserves every annihilating equation, by
commutation of the two actual Laurent actions. -/
theorem act_annihilated (D A : Laurent) (F : G → ℂ) (hF : act D F = 0) :
    act D (act A F) = 0 := by
  rw [act_comm, hF, act_zero_config]

theorem polynomial_background_doublyPeriodic (D A : Laurent) (hD : D ≠ 0)
    (F : G → ℂ) (hF : act D F = 0) (h k : G) (hdet : Geometry.det h k ≠ 0)
    (Eh Ek : Set G) (hEh : Eh.Finite) (hEk : Ek.Finite)
    (hh : ∀ z, z ∉ Eh → act A F (z + h) = act A F z)
    (hk : ∀ z, z ∉ Ek → act A F (z + k) = act A F z) :
    IsDoublyPeriodic (act A F) :=
  ⟨h, k, hdet,
    period_of_period_outside_finite D hD (act A F) (act_annihilated D A F hF) h Eh hEh hh,
    period_of_period_outside_finite D hD (act A F) (act_annihilated D A F hF) k Ek hEk hk⟩

end

end NivatTrial.Background
