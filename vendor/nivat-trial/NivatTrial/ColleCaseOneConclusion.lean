import NivatTrial.ColleCaseOneFixedRegion
import NivatTrial.ColleFirstBoundaryTranslation
import NivatTrial.ColleCaseOneProperRegion
import NivatTrial.ColleCaseOneReflectionTransport

/-! The periodic-wedge branch closes through a maximal agreement region
of the same aperiodic configuration and its periodic reference. -/

namespace NivatTrial.ColleCaseOneConclusion

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.Nonexpansive NivatTrial.RegionGeometry NivatTrial.ExternalInputs
open NivatTrial.ColleGenerating NivatTrial.ColleZonotopeEnvelope
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleFiniteMaximalTranslation
open NivatTrial.ColleFirstBoundaryTranslation NivatTrial.ColleCaseOneProperRegion
open NivatTrial.ColleCaseOneFixedRegion NivatTrial.ColleCaseOneSeedRegion
open NivatTrial.ColleCaseOneReflectionTransport NivatTrial.ColleCaseOne
open scoped Classical
noncomputable section

theorem regional_configuration_of_wedge_agreement {M n : ℕ}
    (hn : 2≤n) (θ x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField x) n)
    (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (hx : x ∈ languageHull θ) (hnot : ¬IsPeriodic x)
    (hpHull : p ∈ languageHull x) (i : Fin n) (k : Lattice) (c : ℤ)
    (hk : k ∈ signedDirections E.period) (huk : 0<det (E.period i) k)
    (hp : IsPeriod p (E.period i)) (hxp : AgreeOn x p (wedge (E.period i) k c)) :
    ∃ y ∈ languageHull θ, ¬IsPeriodic y ∧
      ∃ K : Set Lattice, LatticeConvexRegion K ∧ K.Nonempty ∧
        ∃ a b : Lattice, det a b≠0 ∧ PeriodicOn y K a ∧ PeriodicOn y K b := by
  let u := E.period i
  let D := signedDirections E.period
  obtain ⟨W,a,b,R,_,_,_,_,ha,hab,_,_,hWR,_,hRe,_,hRa,hmax,hex,hray,_,hheight⟩ :=
    exists_fixed_agreement_region hn x x p E (self_mem_languageHull x) hpHull i k c hk huk hxp
  have hproper : ∃ z : Lattice, b≤det u z ∧ z ∉ R :=
    exists_halfPlane_point_outside_of_period x p E hnot u (E.period_ne_zero i) hp R hRa b
  obtain ⟨t,htb,ht,hzero,hout,hray',hf,hheight'⟩ :=
    exists_recentered_first_boundary_at_height D R hRe u k a huk b
      (hWR ha) hab hray hheight hproper
  have hex' : ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
      ∃ T : Finset Lattice, F ⊆ T ∧ (T : Set Lattice) ⊆ R ∧
        IsEnvelope D (T : Set Lattice) ∧ LongFaces D (T : Set Lattice) := by
    intro F hF
    obtain ⟨T,_,hFT,hTR,hTe,hTf⟩ := hex F hF
    exact ⟨T,hFT,hTR,hTe,hTf⟩
  have hmax' := finiteExtensionMaximal_recenter hmax t
  change NivatTrial.ColleMaximalAgreementLimit.FiniteExtensionMaximal D
    (shift t x) (shift t p) (recenter R t) (recenter {z | b≤det u z} t) at hmax'
  rw [recenter_bottomHalfPlane u t b htb] at hmax'
  have hu : u ∈ D := (mem_signedDirections E.period _).mpr ⟨i,Or.inl rfl⟩
  have hnu : -u ∈ D := (mem_signedDirections E.period _).mpr ⟨i,Or.inr rfl⟩
  obtain ⟨K,hK,hKn,_,v,w,hvw,hv,hw⟩ := two_period_region_from_first_boundary
    θ S hS D (recenter R t) (isEnvelope_recenter hRe t)
    (shift t x) (shift t p) (shift_mem_languageHull hx t)
    (shift_mem_languageHull (languageHull_trans hx hpHull) t) (agreeOn_recenter hRa t)
    u hu hnu hzero hout hray' hf hheight' (hp.shift t) hmax'
    (finite_long_exhaustion_recenter hex' t ht)
  exact ⟨shift t x,shift_mem_languageHull hx t,
    fun h => hnot ((isPeriodic_shift_iff x t).mp h),K,hK,hKn,v,w,hvw,hv,hw⟩

end
end NivatTrial.ColleCaseOneConclusion
