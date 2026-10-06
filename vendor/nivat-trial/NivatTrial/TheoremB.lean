import NivatTrial.RegionalReduction
import NivatTrial.ModularReduction
import NivatTrial.ColleRegionalConclusion

/-! Convex Nivat from the actual finite-window complexity bound.
The integer decomposition, regional configuration, and regional-to-global
periodicity are all proved inside this project. -/

namespace NivatTrial.TheoremB

open NivatTrial.Periodicity NivatTrial.Dynamics NivatTrial.LatticePolygon
open NivatTrial.ExternalInputs NivatTrial.ModularReduction NivatTrial.RegionalReduction

noncomputable section

theorem finite_integer_alphabet (M : ℕ)
    (θ : Lattice → Fin M) (S : Finset Lattice) (hne : S.Nonempty)
    (hS : IsLatticeConvex S) (hlow : patternComplexity θ S ≤ S.card) : IsPeriodic θ := by
  by_contra hnot
  obtain ⟨m,hD⟩ := low_complexity_integer_decomposition M θ S hne hlow
  obtain ⟨η,hη,hηnot,R,hR,hRne,a,b,hab,ha,hb⟩ :=
    ColleRegionalConclusion.regional_configuration_of_low_complexity θ S hne hS hlow hnot hD
  have hηlow : patternComplexity η S ≤ S.card :=
    (patternComplexity_le_of_mem_languageHull hη S).trans hlow
  obtain ⟨E⟩ := hD
  obtain ⟨D⟩ := decomposition_in_languageHull E hη
  have hp := periodic_of_regional_decomposition (modularComponent D) D.period
    D.period_ne_zero (modularComponent_period D) D.independent R hR hRne a b hab
    (by simpa only [modularComponent_sum] using periodicOn_encode modCode ha)
    (by simpa only [modularComponent_sum] using periodicOn_encode modCode hb)
    S hne hS (by simpa only [modularComponent_sum] using modular_low_complexity η S hηlow)
  apply modular_not_periodic η hηnot
  simpa only [modularComponent_sum] using hp

/-- **Theorem B (8.18).** The window,
pattern complexity, and nonzero period have their actual mathematical meanings. -/
theorem periodic_of_low_convex_complexity
    {A : Type*} [Fintype A] (θ : Lattice → A) (S : Finset Lattice)
    (hne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card) : IsPeriodic θ := by
  let e := Fintype.equivFin A
  have he : Function.Injective e := e.injective
  have hcomplex : patternComplexity (encode e θ) S ≤ S.card := by
    rwa [patternComplexity_encode_eq he]
  have hp := finite_integer_alphabet (Fintype.card A) (encode e θ) S hne hS hcomplex
  exact (isPeriodic_encode_iff he θ).mp hp

end
end NivatTrial.TheoremB
