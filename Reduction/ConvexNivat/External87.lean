import ConvexNivat.ReductionDefinitions
import ExternalNivatAdapters
import NivatTrial.TheoremB

namespace ConvexNivat
open scoped BigOperators

theorem external8_7_obligation (ξ : Configuration ℤ) (m : ℕ)
    (hminimal : MinimalOrderCounterexample ξ m) (n : RealPlane)
    (hplus : OneSidedNonexpansive ξ n) (hminus : OneSidedNonexpansive ξ (-n)) :
    ∃ η ∈ OrbitClosure ξ, ¬ Periodic η ∧
      ∃ R : TwoRayPolygonalRegion ξ n,
        FullyPeriodicOn η (embed ⁻¹' R.carrier) := by
  exfalso
  rcases hminimal.1 with ⟨A, hpositive, hA⟩
  obtain ⟨S, hS, hconv, hlow⟩ := hminimal.2.2.1
  have hperiod := NivatTrial.TheoremB.periodic_of_low_convex_complexity
    (ExternalNivatAdapters.alphabetLift A ξ hA) S hS
    ((ExternalNivatAdapters.latticeConvex_iff S).mp hconv)
    (by rw [ExternalNivatAdapters.alphabetLift_complexity_eq]; exact hlow)
  exact hminimal.2.1 ((ExternalNivatAdapters.alphabetLift_periodic_iff A ξ hA).mp hperiod)

end ConvexNivat
