import NivatTrial.ColleGeneralBoundaryReference
import NivatTrial.ColleReferenceRegion

/-! Closing the defective-patch branch: the original aperiodic hull witness
has two independent periods on a nonempty convex subregion. -/

namespace NivatTrial.ColleCaseTwoConclusion

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.Periodicity NivatTrial.Nonexpansive NivatTrial.RegionGeometry
open NivatTrial.ColleGenerating NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces NivatTrial.ColleMaximalAgreementLimit
open NivatTrial.ColleSecondBoundaryDefects NivatTrial.ColleSecondBoundaryStrip
open NivatTrial.ColleLeftwardCoordinates NivatTrial.ColleGeneralBoundaryReference
open NivatTrial.ColleReferenceRegion NivatTrial.ColleCaseTwoAperiodic
open NivatTrial.ColleZonotopeEnvelope NivatTrial.ColleProperReferences
open NivatTrial.ColleRegionalBranches NivatTrial.ExternalInputs
open scoped Classical
noncomputable section

theorem two_period_region_of_maximal_agreement {A : Type*} [Fintype A]
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (x p : Lattice → A) (hx : x ∈ languageHull θ) (hpHull : p ∈ languageHull θ)
    (hagree : AgreeOn x p R) (u : Lattice) (hu : u ∈ D) (hnu : -u ∈ D)
    (hzero : 0 ∈ R) (hout : u ∉ R)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hbackFor : ForwardInvariant R (-u))
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N≤det u z) (hp : IsPeriod p u)
    (hmax : FiniteExtensionMaximal D x p R {z | 0≤det u z})
    (hexhaust : ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
      ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R ∧
        IsEnvelope D (W : Set Lattice) ∧ LongFaces D (W : Set Lattice) ∧ 0 ∈ W) :
    ∃ K : Set Lattice, LatticeConvexRegion K ∧ K.Nonempty ∧ K ⊆ R ∧
      ∃ a b : Lattice, det a b≠0 ∧ PeriodicOn x K a ∧ PeriodicOn x K b := by
  obtain ⟨k,_,w,_,huk,_,hforward,hevent,T,_,hbad⟩ :=
    exists_second_boundary_defect_band D R hR x p hagree u hu hnu
      hzero hout hback hheight hmax hexhaust
  have hu0 : u≠0 := by
    intro he
    exact hout (he ▸ hzero)
  have hk0 : k≠0 := by
    intro he
    simp [he,det] at huk
  obtain ⟨c,e,hc,hek,hdet⟩ := exists_leftward_coordinates k hk0
  have hstrips : ∀ height width : ℤ, ∃ v : Lattice, x (e v)≠p (e v) ∧
      ∀ z : Lattice, v.2<z.2 → z.2≤v.2+height → z.1≤v.1+width →
        x (e z)=p (e z) := by
    intro height width
    exact inner_strip_from_boundary_defect_band R x p k w hagree hforward hevent
      e c (by exact_mod_cast hc) hek hdet T hbad height width
  obtain ⟨M,hM,b,hsecond⟩ := reference_det_halfPlane_period_of_inner_strips
    θ S hS u hu0 hx hpHull hp k huk c e hc hek hdet hstrips
  exact two_period_region_of_reference_halfPlane_period x p R hR.latticeConvex
    u k huk hbackFor hforward hheight hagree hp b M hM hsecond

theorem regional_configuration_of_defective_patches {M n : ℕ} (hn : 2≤n)
    (θ p : Lattice → Fin M) (E : IntegerDecomposition (integerField θ) n)
    (S : Finset Lattice) (hS : NivatTrial.LatticePolygon.IsLatticeConvex S)
    (hlow : patternComplexity θ S≤S.card)
    (i : Fin n) (hpHull : p ∈ languageHull θ) (hp : IsPeriod p (E.period i))
    (hproper : ¬HasDoublyPeriodicExtension p (halfPlane (embed (E.period i)) 0))
    (hpatch : HasDefectiveHalfStripPatches θ p E.period i) :
    ∃ y ∈ languageHull θ, ¬IsPeriodic y ∧
      ∃ K : Set Lattice, LatticeConvexRegion K ∧ K.Nonempty ∧
        ∃ a b : Lattice, det a b≠0 ∧ PeriodicOn y K a ∧ PeriodicOn y K b := by
  obtain ⟨T,_,hT,_⟩ := exists_generating_window θ S hS hlow
  obtain ⟨y,hy,hnot,_,_,q,hq,_,R,hRe,_,_,hzero,hout,_,hback,hheight,
      hqp,hyq,hyper,_,_,hmax,hexhaust⟩ :=
    aperiodic_region_of_defective_patches hn θ p E i hpHull hp hproper hpatch
  have hu : E.period i ∈ signedDirections E.period :=
    (mem_signedDirections E.period _).mpr ⟨i,Or.inl rfl⟩
  have hnu : -E.period i ∈ signedDirections E.period :=
    (mem_signedDirections E.period _).mpr ⟨i,Or.inr rfl⟩
  obtain ⟨K,hK,hKn,_,a,b,hab,ha,hb⟩ := two_period_region_of_maximal_agreement
    θ T hT (signedDirections E.period) R hRe y q hy (languageHull_trans hpHull hq)
      hyq (E.period i) hu hnu hzero hout hback hyper.1 hheight hqp hmax hexhaust
  exact ⟨y,hy,hnot,K,hK,hKn,a,b,hab,ha,hb⟩

end
end NivatTrial.ColleCaseTwoConclusion
