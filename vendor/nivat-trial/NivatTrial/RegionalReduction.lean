import NivatTrial.SecondHalfPlane
import NivatTrial.StarNormalization
import NivatTrial.TheoremA

/-! The complete internal reduction from a directional decomposition and an
actual doubly periodic convex region to a nonzero global period. -/

namespace NivatTrial.RegionalReduction

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.Dynamics
open NivatTrial.RegionGeometry NivatTrial.LatticePolygon
open scoped Classical

noncomputable section

/-- The internal part of Section 8. All half-plane, limit, two-component,
normalization, and star-complexity steps are proved within the project. -/
theorem periodic_of_regional_decomposition
    {ι A : Type*} [Fintype ι] [AddCommGroup A] [Fintype A]
    (F : ι → Lattice → A) (h : ι → Lattice)
    (hne : ∀ i, h i ≠ 0) (hp : ∀ i, IsPeriod (F i) (h i))
    (hind : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0)
    (R : Set Lattice) (hR : LatticeConvexRegion R) (hRne : R.Nonempty)
    (a b : Lattice) (hab : det a b ≠ 0)
    (ha : PeriodicOn (∑ i, F i) R a) (hb : PeriodicOn (∑ i, F i) R b)
    (S : Finset Lattice) (hSne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (∑ i, F i) S ≤ S.card) :
    IsPeriodic (∑ i, F i) := by
  by_contra hnot
  obtain ⟨T, hT⟩ := ReducedDecomposition.reduce F h hne hind hp hnot
  letI : Nontrivial (Fin T.count) := T.index_nontrivial
  have hsum : (∑ i, T.component i) = ∑ i, F i := by
    funext z
    simpa only [ReducedDecomposition.Data.total, Finset.sum_apply] using congrFun hT z
  obtain ⟨v, g, c, U, _, hvp, hpos, hpair, hU, hupper⟩ :=
    FirstHalfPlane.one_sided_tails T.component T.period T.period_ne_zero
      T.component_period T.independent T.not_doublyPeriodic R hR hRne a b hab
      (hsum.symm ▸ ha) (hsum.symm ▸ hb)
  let T' : ReducedDecomposition.Data A := {
    T with
    period := v
    period_ne_zero := fun i he => by simpa [he, det] using hpos i
    independent := hpair
    component_period := hvp }
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  have hlowT : patternComplexity (∑ i, T.component i) S ≤ S.card := hsum.symm ▸ hlow
  have hleft := SecondHalfPlane.all_lower_tails T.component U v g c hvp hpos hpair
    T.not_doublyPeriodic hU hupper S hSne hS hlowT
  choose β L hL hLagrees using hleft
  obtain ⟨W, hW⟩ := StarNormalization.exists_star T' L U c β hL hU hLagrees hupper
  have hbound := TheoremA.complexity_lower_bound W S hS
  have htotal : W.total = ∑ i, F i := hW.trans hT
  rw [htotal] at hbound
  omega

end
end NivatTrial.RegionalReduction
