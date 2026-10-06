import NivatTrial.ColleDefectiveGrowingEnvelopes
import NivatTrial.ColleCaseTwoWindows
import NivatTrial.ColleReferenceRigidity
import NivatTrial.ColleDecompositionHull

/-! The genuine second branch: finite defective patches produce a
nonperiodic hull configuration, with a periodic reference on an infinite
convex region. Nonperiodicity uses an actual defect retained by compactness. -/

namespace NivatTrial.ColleCaseTwoAperiodic

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.RegionGeometry NivatTrial.ExternalInputs
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleZonotopeEnvelope NivatTrial.ColleFiniteEnvelope
open NivatTrial.ColleRegionalBranches NivatTrial.ColleCaseTwoWindows
open NivatTrial.ColleDefectiveGrowingEnvelopes NivatTrial.ColleDecompositionHull
open NivatTrial.ColleProperReferences NivatTrial.ColleReferenceRigidity
open NivatTrial.ColleMaximalAgreementLimit
open scoped Classical
noncomputable section

theorem aperiodic_region_of_defective_patches {M n : ℕ} (hn : 2 ≤ n)
    (θ p : Lattice → Fin M) (E : IntegerDecomposition (integerField θ) n)
    (i : Fin n) (hpHull : p ∈ languageHull θ) (hp : IsPeriod p (E.period i))
    (hproper : ¬HasDoublyPeriodicExtension p (halfPlane (embed (E.period i)) 0))
    (hpatch : HasDefectiveHalfStripPatches θ p E.period i) :
    ∃ y ∈ languageHull θ, ¬IsPeriodic y ∧
      ∃ Ey : IntegerDecomposition (integerField y) n, Ey.period = E.period ∧
      ∃ q ∈ languageHull p,
        ¬HasDoublyPeriodicExtension q (halfPlane (embed (E.period i)) 0) ∧
      ∃ R : Set Lattice,
        IsEnvelope (signedDirections E.period) R ∧ LongFaces (signedDirections E.period) R ∧
        LatticeConvexRegion R ∧ 0 ∈ R ∧ E.period i ∉ R ∧
        (∀ z ∈ R, 0 ≤ det (E.period i) z) ∧
        (∀ t : ℕ, -(t•E.period i) ∈ R) ∧
        (∀ N : ℤ, ∃ z ∈ R, N ≤ det (E.period i) z) ∧
        IsPeriod q (E.period i) ∧ AgreeOn y q R ∧
        PeriodicOn y R (-(E.period i)) ∧
        (∃ d ∈ signedDirections E.period, 0 < det (E.period i) d ∧ ForwardInvariant R d) ∧
        (∃ z, 0 ≤ det (E.period i) z ∧ y z ≠ q z) ∧
        FiniteExtensionMaximal (signedDirections E.period) y q R
          {z | 0 ≤ det (E.period i) z} ∧
        (∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
          ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R ∧
            IsEnvelope (signedDirections E.period) (W : Set Lattice) ∧
            LongFaces (signedDirections E.period) (W : Set Lattice) ∧ 0 ∈ W) := by
  obtain ⟨k,hk,huk,T,x,hx,hTe,hTf,hzero,hback,hheight,hhalf,hagree,hQe,hQf,hmax⟩ :=
    exists_case_two_maximal_sequence hn θ p E.period E.independent i hpatch
  have huD : E.period i ∈ signedDirections E.period :=
    (mem_signedDirections E.period _).mpr ⟨i,Or.inl rfl⟩
  have hnuD : -E.period i ∈ signedDirections E.period :=
    (mem_signedDirections E.period _).mpr ⟨i,Or.inr rfl⟩
  obtain ⟨y,hy,q,hq,R,hphase,hqp,hyq,hRe,hRf,hRc,hRzero,hRout,hRh,hRb,hRheight,
    ⟨d,hd,hud,hRu,hRd⟩,⟨zbad,hzbad,hybad⟩,hlimitmax,hexhaust⟩ := extract_region_with_actual_defect θ p
      integerCode (integerCode_injective M) (Finset.univ.toList.map E.period)
      (period_list_nonzero E) (period_list_pairwise E) (actual_product_recurrence E)
      (signedDirections E.period) (period_list_signed E) (E.period i) k huk huD hnuD
      hpHull hp T (fun N => halfStrip (T N) (E.period i))
      hTe hTf hzero hback hheight hhalf hQe
      (fun N => base_subset_halfStrip (T N) (E.period i)) hQf x hx hagree hmax
  have hqproper : ¬HasDoublyPeriodicExtension q (halfPlane (embed (E.period i)) 0) := by
    obtain ⟨c,huc,hqc⟩ := hphase
    have hscore : score (embed (E.period i)) c = 0 := by
      change ((E.period i).1 : ℝ)*c.2 - ((E.period i).2 : ℝ)*c.1 = 0
      exact_mod_cast huc
    intro he
    exact hproper ((extension_iff_tangent_shift p (embed (E.period i)) 0 c hscore).mp
      (hqc ▸ he))
  obtain ⟨Ey,hEy⟩ := exists_decomposition_with_same_periods E hy
  have hnot : ¬IsPeriodic y := aperiodic_of_proper_reference_and_defect y q Ey
    (signedDirections E.period) R hRe (E.period i) k huk hRzero hRb hRheight
    hyq hqp hqproper zbad hzbad hybad
  have hper : PeriodicOn y R (-(E.period i)) := by
    refine ⟨hRu,?_⟩
    intro z hz
    exact (hyq _ (hRu z hz)).trans ((hqp.neg z).trans (hyq z hz).symm)
  exact ⟨y,hy,hnot,Ey,hEy,q,hq,hqproper,R,hRe,hRf,hRc,hRzero,hRout,hRh,hRb,
    hRheight,hqp,hyq,hper,⟨d,hd,hud,hRd⟩,⟨zbad,hzbad,hybad⟩,hlimitmax,hexhaust⟩

end
end NivatTrial.ColleCaseTwoAperiodic
