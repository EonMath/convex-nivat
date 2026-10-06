import ConvexNivat.Colle.GeneratingBasic
import ConvexNivat.ReductionJoinElementary
import ConvexNivat.ExternalFactors
import ConvexNivat.ExternalDecomposition

namespace ConvexNivat.Colle
open scoped BigOperators

theorem minimal_decomposition_pairwise (ξ : Configuration ℤ) (m : ℕ)
    (D : PeriodicDecomposition ℤ ξ m) (hminimal : MinimalPeriodicOrder ℤ ξ m) :
    Pairwise (fun i j => Nonparallel (D.period i) (D.period j)) := by
  exact minimalPeriodicOrder_pairwise_periods ξ m hminimal D

/-- Source Theorem 1.4 followed by minimum-order selection and merging parallel
components, supplying the actual input decomposition for §3.1 and §4.2. -/
theorem annihilator_minimal_decomposition (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ)
    (hξ : ¬ Periodic ξ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ D : PeriodicDecomposition ℤ ξ m,
      MinimalPeriodicOrder ℤ ξ m ∧
        Pairwise (fun i j => Nonparallel (D.period i) (D.period j)) := by
  obtain ⟨n, h, hn, hp, ha⟩ := external8_4b_factors_obligation ξ A hA hann
  obtain ⟨f, hf, hs⟩ := external8_4b_decomposition_obligation n h hn hp ξ ha
  have hD : HasPeriodicDecomposition ℤ ξ n :=
    ⟨{ field := f, period := h, period_nonzero := hn, has_period := hf, sum_eq := hs }⟩
  obtain ⟨m, hm⟩ := minimalPeriodicOrder_exists_of_decomposition ξ n hD
  obtain ⟨D⟩ := hm.1
  exact ⟨m, minimal_order_nonperiodic_ge_two ξ m hξ hm, D, hm,
    minimal_decomposition_pairwise ξ m D hm⟩

end ConvexNivat.Colle
