import NivatTrial.ColleCaseOneSeedRegion
import NivatTrial.ColleDecompositionHull

/-! The actual fixed Case 1 agreement region. The finite wedge seeds feed
the directed union coding theorem, retaining the original aperiodic point
rather than replacing it by an orbit limit. -/

namespace NivatTrial.ColleCaseOneFixedRegion

open NivatTrial.Geometry NivatTrial.LatticePolygon NivatTrial.RegionGeometry
open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.ExternalInputs
open NivatTrial.OneSidedRecurrence NivatTrial.ColleCaseOne
open NivatTrial.ColleCaseOneSeedRegion NivatTrial.ColleFixedAgreementRegion
open NivatTrial.ColleDecompositionHull NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleMaximalAgreementLimit NivatTrial.ColleZonotopeEnvelope
open scoped Classical
noncomputable section

theorem height_unbounded_of_transverse_ray (R : Set Lattice)
    (u k a : Lattice) (huk : 0 < det u k)
    (hray : ∀ j : ℕ, a+j•k ∈ R) :
    ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z := by
  intro N
  obtain ⟨j,hj⟩ := exists_nat_gt (N-det u a)
  refine ⟨a+j•k,hray j,?_⟩
  rw [det_add_right,det_nsmul_right]
  have hj' : (N-det u a:ℤ) < j := hj
  have hnonneg : (0:ℤ) ≤ j := by positivity
  nlinarith

theorem exists_fixed_agreement_region {M n : ℕ}
    (hn : 2 ≤ n) (θ x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) n)
    (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (i : Fin n) (k : Lattice) (c : ℤ)
    (hk : k ∈ signedDirections E.period)
    (huk : 0 < det (E.period i) k)
    (hxp : AgreeOn x p (wedge (E.period i) k c)) :
    ∃ W : Finset Lattice, ∃ a : Lattice, ∃ b : ℤ,
      ∃ R : Set Lattice,
      W.Nonempty ∧ IsLatticeConvex W ∧
      IsEnvelope (signedDirections E.period) (W : Set Lattice) ∧
      LongFaces (signedDirections E.period) (W : Set Lattice) ∧
      a ∈ W ∧ det (E.period i) a = b ∧ 0 ≤ b ∧
      R = agreementRegion (signedDirections E.period) x p W
        (bottomHalfPlane (E.period i) b) ∧
      (W : Set Lattice) ⊆ R ∧
      R ⊆ bottomHalfPlane (E.period i) b ∧
      IsEnvelope (signedDirections E.period) R ∧
      LongFaces (signedDirections E.period) R ∧
      AgreeOn x p R ∧
      FiniteExtensionMaximal (signedDirections E.period) x p R
        (bottomHalfPlane (E.period i) b) ∧
      (∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
        ∃ T : Finset Lattice, W ⊆ T ∧ F ⊆ T ∧ (T : Set Lattice) ⊆ R ∧
          IsEnvelope (signedDirections E.period) (T : Set Lattice) ∧
          LongFaces (signedDirections E.period) (T : Set Lattice)) ∧
      (∀ j : ℕ, a+j•E.period i ∈ R) ∧
      (∀ j : ℕ, a+j•k ∈ R) ∧
      (∀ N : ℤ, ∃ z ∈ R, N ≤ det (E.period i) z) := by
  let u := E.period i
  let D := signedDirections E.period
  have hu : u ∈ D := (mem_signedDirections E.period _).mpr ⟨i,Or.inl rfl⟩
  have hnu : -u ∈ D := (mem_signedDirections E.period _).mpr ⟨i,Or.inr rfl⟩
  have hnk : -k ∈ D := by
    obtain ⟨j,hj | hj⟩ := (mem_signedDirections E.period k).mp hk
    · exact (mem_signedDirections E.period _).mpr ⟨j,Or.inr (by simp [hj])⟩
    · exact (mem_signedDirections E.period _).mpr ⟨j,Or.inl (by simp [hj])⟩
  obtain ⟨W,a,b,hW,hWc,hWe,hWf,hWsub,ha,hab,hb,hRW,hrayu,hrayk⟩ :=
    exists_seed_rays_in_agreementRegion hn E.period E.independent x p u k c
      huk hu hnu hk hnk hxp
  let Q := bottomHalfPlane u b
  let R := agreementRegion D x p W Q
  have hWQ : (W : Set Lattice) ⊆ Q := by
    intro z hz
    obtain ⟨T,hT,hzT⟩ := hRW hz
    exact hT.2.1 hzT
  have hWa : AgreeOn x p (W : Set Lattice) :=
    fun z hz => hxp z (hWsub hz)
  have hQ : IsEnvelope D Q := bottomHalfPlane_isEnvelope D u hu b
  have hdir : ∀ d ∈ Finset.univ.toList.map E.period, d ∈ D ∧ -d ∈ D :=
    period_list_signed E
  have hprop := agreementRegion_properties θ integerCode (integerCode_injective M)
    (Finset.univ.toList.map E.period) (period_list_nonzero E)
    (period_list_pairwise E) (actual_product_recurrence E)
    x p hx hp D hdir u k (ne_of_gt huk) hu hnu hk hnk Q hQ W hW hWe hWf
      hWQ hWa
  obtain ⟨hWR,hRQ,hRe,hRf,hRa,hRmax,hRexhaust⟩ := hprop
  refine ⟨W,a,b,R,hW,hWc,hWe,hWf,ha,hab,hb,rfl,hWR,hRQ,hRe,hRf,hRa,
    hRmax,hRexhaust,hrayu,hrayk,?_⟩
  exact height_unbounded_of_transverse_ray R u k a huk hrayk

end
end NivatTrial.ColleCaseOneFixedRegion
