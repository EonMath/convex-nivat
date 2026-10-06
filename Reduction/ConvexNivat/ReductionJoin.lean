import ConvexNivat.ReductionJoinHalfPlanes
import ConvexNivat.ReductionOrderAndModPrime
import ColleJoins86.External86
import ConvexNivat.FirstHalfPlaneCorollary
import ConvexNivat.SecondHalfPlane
import ConvexNivat.External87

/-! Exact original 8.1 assembly; the original 8.7 provider is now supplied independently. -/
namespace ConvexNivat
open scoped BigOperators

theorem theorem8_1 (ξ : Configuration ℤ) (m : ℕ)
    (hminimal : MinimalOrderCounterexample ξ m) :
    ∃ p : ℕ, p.Prime ∧
      (∀ z, 0 ≤ ξ z ∧ ξ z < (p : ℤ)) ∧
      ∃ η ∈ OrbitClosure ξ, ¬ Periodic η ∧
        ¬ Periodic (fun z => (η z : ZMod p)) ∧
        ∃ n : ℕ, 2 ≤ n ∧
          ∃ D : AdmissibleDecomposition p (fun z => (η z : ZMod p)) n,
            (∀ i, ¬ DoublyPeriodic (D.field i)) ∧
            Pairwise (fun i j => Nonparallel (D.period i) (D.period j)) ∧
            ∀ i, realDot (embed (D.period i)) (D.left i).normal = 0 := by
  rcases hminimal.1 with ⟨A, hpositive, hA⟩
  have haperiodic := hminimal.2.1
  have hlow := hminimal.2.2.1
  obtain ⟨p, hp, hlarge, hencoding⟩ := prime_above_positive_alphabet ξ A hA hpositive
  obtain ⟨S, hS, hconvex, hScomplexity⟩ := hlow
  have hann := external8_4a_obligation ξ A hA S hS hScomplexity
  obtain ⟨r, h, hnonzero, hpairwise, hproduct⟩ := external8_4b_factors_obligation ξ A hA hann
  obtain ⟨normal, hplus, hminus⟩ := external8_6_both_directions_obligation ξ A hA hann haperiodic
  obtain ⟨η, hη, hηaperiodic, R, hηfull⟩ :=
    external8_7_obligation ξ m hminimal normal hplus hminus
  have hηA := integer_orbitClosure_range ξ η A hA hη
  have hinjective := modPrime_alphabet_injective p A hpositive hlarge
  have hθaperiodic : ¬ Periodic (fun z => (η z : ZMod p)) := by
    intro hperiod
    exact hηaperiodic ((modPrime_periodic_iff_on_alphabet p η A hηA hinjective).mp hperiod)
  obtain ⟨_, component, hperiod, _, hsum, _, _, _⟩ :=
    lemma8_5 ξ η A hA hpositive hη r h hnonzero hpairwise hproduct p hp hlarge
  let E : PeriodicDecomposition (ZMod p) (fun z => (η z : ZMod p)) r := {
    field := fun i z => (component i z : ZMod p)
    period := h
    period_nonzero := hnonzero
    has_period := fun i => modPrime_preserves_period p (component i) (h i) (hperiod i)
    sum_eq := hsum }
  have hR : LatticeConvexRegion (embed ⁻¹' R.carrier) :=
    ⟨R.carrier, R.closed, R.convex, rfl⟩
  have hθfull := fullyPeriodicOn_modPrime p η (embed ⁻¹' R.carrier) hηfull
  obtain ⟨D, _⟩ := corollary8_10 p hp (fun z => (η z : ZMod p)) hθaperiodic r E
    hpairwise (embed ⁻¹' R.carrier) hR hθfull
  have hηlow := lowConvexComplexity_integer_orbitClosure ξ η A hA hη
    ⟨S, hS, hconvex, hScomplexity⟩
  have hθlow : LowConvexComplexity (fun z => (η z : ZMod p)) := by
    obtain ⟨T, hT, hTconvex, hTcomplexity⟩ := hηlow
    refine ⟨T, hT, hTconvex, ?_⟩
    rw [modPrime_complexity_eq_on_alphabet p η A hηA hinjective T]
    exact hTcomplexity
  have hlower := theorem8_12 p hp (fun z => (η z : ZMod p)) D hθaperiodic hθlow
  obtain ⟨F, _, _, hnotdouble, hdistinct, haligned⟩ :=
    firstHalfPlaneData_admissible p (fun z => (η z : ZMod p)) D hlower
  exact ⟨p, hp, hencoding, η, hη, hηaperiodic, hθaperiodic,
    D.length, D.at_least_two, F, hnotdouble, hdistinct, haligned⟩

end ConvexNivat
