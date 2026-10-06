import NivatTrial.ColleCaseOneConclusion
import NivatTrial.ColleCaseOneNormalizedReference
import NivatTrial.ColleCaseTwoConclusion
import NivatTrial.ColleRegionalEntry
import NivatTrial.IntegerDecompositionOrder

/-! The complete regional conclusion of Colle's argument.  Aperiodicity,
low convex complexity and an actual integer decomposition give an actual
aperiodic hull point with two independent periods on a nonempty convex
region.  All directional and maximal-region inputs are constructed inside
the two genuine branches. -/

namespace NivatTrial.ColleRegionalConclusion

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.Nonexpansive NivatTrial.RegionGeometry NivatTrial.ExternalInputs
open NivatTrial.LatticePolygon NivatTrial.LatticeCoordinates
open NivatTrial.ColleGenerating NivatTrial.ColleRegionalBranches
open NivatTrial.ColleCaseOneConclusion NivatTrial.ColleCaseOneNormalizedReference
open NivatTrial.ColleCaseTwoConclusion NivatTrial.ColleRegionalEntry
open NivatTrial.ColleCoordinateTransport NivatTrial.IntegerDecompositionOrder
open scoped Classical
noncomputable section

theorem regional_configuration_of_periodic_wedge
    {M n : ℕ} (hn : 2 ≤ n) (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) n)
    (S : Finset Lattice) (hS : IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card) (i : Fin n)
    (hcase : HasPeriodicWedge θ E.period (E.period i)) :
    ∃ x ∈ languageHull θ, ¬IsPeriodic x ∧
      ∃ R : Set Lattice, LatticeConvexRegion R ∧ R.Nonempty ∧
        ∃ a b : Lattice, det a b ≠ 0 ∧ PeriodicOn x R a ∧ PeriodicOn x R b := by
  obtain ⟨T,_,hT,_⟩ := exists_generating_window θ S hS hlow
  obtain ⟨x,hx,hnot,Ex,p,hpx,_,k,hk,c,hik,hp,hxp⟩ :=
    exists_normalized_reference_of_periodic_wedge θ E i hcase
  exact regional_configuration_of_wedge_agreement hn θ x p Ex T hT hx hnot
    hpx i k c hk hik hp hxp

/-- No uniform-order, opposite-direction, periodic-reference or seed-window
assumption remains in this regional theorem. -/
theorem regional_configuration_of_low_complexity
    {M n : ℕ} (θ : Lattice → Fin M) (S : Finset Lattice)
    (hne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card) (hnot : ¬IsPeriodic θ)
    (hD : HasIntegerDecomposition (integerField θ) n) :
    ∃ x ∈ languageHull θ, ¬IsPeriodic x ∧
      ∃ R : Set Lattice, LatticeConvexRegion R ∧ R.Nonempty ∧
        ∃ a b : Lattice, det a b ≠ 0 ∧ PeriodicOn x R a ∧ PeriodicOn x R b := by
  have hn3 : 3 ≤ n := three_le_order_of_aperiodic θ S hne hS hlow hnot hD
  have hn : 2 ≤ n := by omega
  obtain ⟨E⟩ := hD
  obtain ⟨e,F,i,p,hpHull,_,hp,hproper,hcase⟩ :=
    low_complexity_regional_dichotomy hn θ E S hS hlow hnot
  let S' : Finset Lattice := mapWindow e.symm S
  have hS' : IsLatticeConvex S' := isLatticeConvex_mapWindow e.symm hS
  have hlow' : patternComplexity (θ ∘ e) S' ≤ S'.card := by
    calc
      patternComplexity (θ ∘ e) S' =
          patternComplexity ((θ ∘ e) ∘ e.symm) S :=
        patternComplexity_mapWindow e.symm (θ ∘ e) S
      _ = patternComplexity θ S := by
        congr 1
        funext z
        simp
      _ ≤ S.card := hlow
      _ = S'.card := (card_mapWindow e.symm S).symm
  apply pull_back_regional_conclusion θ e
  rcases hcase with hwedge | hpatch
  · exact regional_configuration_of_periodic_wedge hn (θ ∘ e) F S' hS' hlow' i hwedge
  · exact regional_configuration_of_defective_patches hn (θ ∘ e) p F S' hS' hlow'
      i hpHull hp hproper hpatch

end
end NivatTrial.ColleRegionalConclusion
