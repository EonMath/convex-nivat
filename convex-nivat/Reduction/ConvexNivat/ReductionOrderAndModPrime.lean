import ConvexNivat.ReductionJoinElementary
import ConvexNivat.ExternalAnnihilator
import ConvexNivat.ExternalFactors
import ConvexNivat.ExternalDecomposition

namespace ConvexNivat
open scoped BigOperators

theorem remark8_3_equal_order (ξ : Configuration ℤ) (m : ℕ)
    (hminimal : MinimalOrderCounterexample ξ m) (η : Configuration ℤ)
    (hη : η ∈ OrbitClosure ξ) (haperiodic : ¬ Periodic η) :
    LowConvexComplexity η ∧ MinimalPeriodicOrder ℤ η m := by
  rcases hminimal with ⟨⟨A, hpositive, hA⟩, _, hlow, horder, hglobal⟩
  have hηA := integer_orbitClosure_range ξ η A hA hη
  have hηlow := lowConvexComplexity_integer_orbitClosure ξ η A hA hη hlow
  obtain ⟨D⟩ := horder.1
  have hpairwise := minimalPeriodicOrder_pairwise_periods ξ m horder D
  have hann := mixedDifference_periodicDecomposition ξ m D
  have hηann := orbitClosure_preserves_mixedDifference ξ η hη m D.period hann
  obtain ⟨component, hperiod, hsum⟩ := external8_4b_decomposition_obligation
    m D.period D.period_nonzero hpairwise η hηann
  have hηdecomp : HasPeriodicDecomposition ℤ η m :=
    ⟨{ field := component, period := D.period, period_nonzero := D.period_nonzero,
       has_period := hperiod, sum_eq := hsum }⟩
  obtain ⟨n, hηorder⟩ := minimalPeriodicOrder_exists_of_decomposition η m hηdecomp
  have hmn : m ≤ n := hglobal η n ⟨A, hpositive, hηA⟩ haperiodic hηlow hηorder
  have hnm : n ≤ m := hηorder.2 m hηdecomp
  have hnmEq := Nat.le_antisymm hnm hmn
  subst n
  exact ⟨hηlow, hηorder⟩

theorem remark8_3_select_minimal (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hpositive : ∀ a ∈ A, 0 < a)
    (haperiodic : ¬ Periodic ξ) (hlow : LowConvexComplexity ξ) :
    ∃ η : Configuration ℤ, ∃ m : ℕ, MinimalOrderCounterexample η m := by
  obtain ⟨S, hS, hconvex, hScomplexity⟩ := hlow
  have hann := external8_4a_obligation ξ A hA S hS hScomplexity
  obtain ⟨m, h, hnonzero, hpairwise, hproduct⟩ := external8_4b_factors_obligation ξ A hA hann
  obtain ⟨component, hperiod, hsum⟩ := external8_4b_decomposition_obligation
    m h hnonzero hpairwise ξ hproduct
  have hdecomp : HasPeriodicDecomposition ℤ ξ m :=
    ⟨{ field := component, period := h, period_nonzero := hnonzero,
       has_period := hperiod, sum_eq := hsum }⟩
  obtain ⟨n, horder⟩ := minimalPeriodicOrder_exists_of_decomposition ξ m hdecomp
  exact minimalOrderCounterexample_exists_of_order ξ A hA hpositive haperiodic
    ⟨S, hS, hconvex, hScomplexity⟩ n horder

theorem lemma8_5 (ξ η : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hpositive : ∀ a ∈ A, 0 < a)
    (hη : η ∈ OrbitClosure ξ) (m : ℕ) (h : Fin m → Lattice)
    (hnonzero : ∀ i, h i ≠ 0)
    (hpairwise : Pairwise (fun i j => Nonparallel (h i) (h j)))
    (hann : ∀ z, mixedDifference h Finset.univ ξ z = 0)
    (p : ℕ) (hp : p.Prime) (hlarge : ∀ a ∈ A, a < (p : ℤ)) :
    (∀ z, mixedDifference h Finset.univ η z = 0) ∧
    ∃ component : Fin m → Configuration ℤ,
      (∀ i, HasPeriod (component i) (h i)) ∧
      (∀ z, η z = ∑ i, component i z) ∧
      (∀ z, (η z : ZMod p) = ∑ i, (component i z : ZMod p)) ∧
      (∀ i, HasPeriod (fun z => (component i z : ZMod p)) (h i)) ∧
      (¬ Periodic η → 2 ≤ m) ∧
      (∀ a ∈ A, ∀ b ∈ A, (a : ZMod p) = (b : ZMod p) → a = b) := by
  have hηann := orbitClosure_preserves_mixedDifference ξ η hη m h hann
  obtain ⟨component, hperiod, hsum⟩ := external8_4b_decomposition_obligation
    m h hnonzero hpairwise η hηann
  let D : PeriodicDecomposition ℤ η m :=
    { field := component, period := h, period_nonzero := hnonzero,
      has_period := hperiod, sum_eq := hsum }
  refine ⟨hηann, component, hperiod, hsum, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [hsum z]
    exact modPrime_sum p m component z
  · intro i
    exact modPrime_preserves_period p (component i) (h i) (hperiod i)
  · exact periodicDecomposition_at_least_two η m D
  · exact modPrime_alphabet_injective p A hpositive hlarge

end ConvexNivat
