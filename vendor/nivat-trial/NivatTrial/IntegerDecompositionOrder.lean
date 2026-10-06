import NivatTrial.ModularReduction
import NivatTrial.TwoComponent

/-! The two-component theorem rules out decomposition orders zero, one and
two for a nonperiodic low-complexity convex configuration. -/

namespace NivatTrial.IntegerDecompositionOrder

open NivatTrial.ExternalInputs NivatTrial.ModularReduction
open NivatTrial.Periodicity NivatTrial.Dynamics NivatTrial.LatticePolygon
open scoped Classical
noncomputable section

theorem periodic_of_order_le_two {M n : ℕ} (θ : Lattice → Fin M)
    (S : Finset Lattice) (hne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card)
    (hD : HasIntegerDecomposition (integerField θ) n) (hn : n ≤ 2) : IsPeriodic θ := by
  obtain ⟨D⟩ := hD
  apply (isPeriodic_encode_iff (modCode_injective M) θ).mp
  have hsum := modularComponent_sum D
  have hcomplex := modular_low_complexity θ S hlow
  interval_cases n
  · have hz : encode modCode θ = 0 := by simpa using hsum.symm
    refine ⟨(1,0),by norm_num,?_⟩
    rw [hz]
    intro z
    rfl
  · have he : modularComponent D 0 = encode modCode θ := by simpa using hsum
    rw [← he]
    exact ⟨D.period 0,D.period_ne_zero 0,modularComponent_period D 0⟩
  · have he : modularComponent D 0 + modularComponent D 1 = encode modCode θ := by
      simpa only [Fin.sum_univ_two] using hsum
    rw [← he] at hcomplex ⊢
    exact NivatTrial.TwoComponent.periodic_of_low_convex_complexity
      (modularComponent D 0) (modularComponent D 1) (D.period 0) (D.period 1)
      (modularComponent_period D 0) (modularComponent_period D 1)
      (D.independent 0 1 (by decide)) S hne hS hcomplex

theorem three_le_order_of_aperiodic {M n : ℕ} (θ : Lattice → Fin M)
    (S : Finset Lattice) (hne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card) (hnot : ¬IsPeriodic θ)
    (hD : HasIntegerDecomposition (integerField θ) n) : 3 ≤ n := by
  by_contra hn
  exact hnot (periodic_of_order_le_two θ S hne hS hlow hD (by omega))

end
end NivatTrial.IntegerDecompositionOrder
