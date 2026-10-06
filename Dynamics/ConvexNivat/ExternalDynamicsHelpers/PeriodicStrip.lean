import ConvexNivat.ExternalDynamicsHelpers.PeriodicStripExpansive
import ConvexNivat.ExternalDynamicsHelpers.PeriodicStripGeometry
import ConvexNivat.ExternalDynamicsHelpers.PeriodicStripPropagation

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

theorem periodic_expansive_orientation_transverse_period (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (v h : Lattice) (hv : Primitive v) (hh : h ≠ 0)
    (hparallel : det v h = 0) (hperiod : HasPeriod ξ h)
    (hexp : ¬ OneSidedNonexpansive ξ (normal v)) :
    ∃ w : Lattice, 0 < det v w ∧ HasPeriod ξ w := by
  obtain ⟨S, hS, hconv, harea, g, hface, hgen⟩ :=
    closed_expansive_singleton_generated_face ξ A hA v hv hexp
  obtain ⟨w, hw⟩ := primitive_height_surjective v hv 1
  change det v w = 1 at hw
  have hwpos : 0 < det v w := by omega
  let a := rowMinimum v S hS
  let b := rowMaximum v S hS
  have hab : a ≤ b := by
    obtain ⟨z, hz⟩ := hS
    exact (Finset.inf'_le (det v) hz).trans (Finset.le_sup' (det v) hz)
  have hSin : (S : Set Lattice) ⊆ latticeStrip v a b := by
    intro z hz
    exact ⟨Finset.inf'_le _ hz, Finset.le_sup' _ hz⟩
  obtain ⟨B, hB, hBconv, hSB, hBstrip, hcode⟩ :=
    periodic_strip_convex_coding_window ξ h v hh hv hperiod hparallel a b hab S hSin
  have hwidth : rowHeight v S hS ≤ b - a := le_rfl
  have hp := periodic_strip_bounded_half_periods ξ A hA S hS v hv g hface hgen
    w hwpos a b hwidth B hcode
  obtain ⟨q, hq, hqN, hqperiod⟩ :=
    bounded_cofinal_half_period_global ξ v w hwpos b (complexity ξ B) hp
  refine ⟨(q : ℤ) • w, ?_, hqperiod⟩
  have he : det v ((q : ℤ) • w) = (q : ℤ) * det v w := by dsimp [det]; ring
  rw [he, hw, mul_one]
  exact_mod_cast hq

end
end ConvexNivat.ExternalDynamicsHelpers
