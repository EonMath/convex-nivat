import NivatTrial.ColleCaseOneWedgeSeed
import NivatTrial.ColleFixedAgreementRegion

/-! A fixed long-faced wedge seed yields two actual rays in the directed
agreement region. The compared configurations remain fixed throughout. -/

namespace NivatTrial.ColleCaseOneSeedRegion

open NivatTrial.Geometry NivatTrial.LatticePolygon NivatTrial.RegionGeometry
open NivatTrial.ColleCaseOne NivatTrial.ColleCaseOneWedgeSeed
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces NivatTrial.ColleDirectedAgreement
open NivatTrial.ColleFixedAgreementRegion NivatTrial.ColleZonotopeEnvelope
open NivatTrial.Nonexpansive
open scoped Classical
noncomputable section

def bottomHalfPlane (u : Lattice) (b : ℤ) : Set Lattice :=
  {z | b ≤ det u z}

theorem bottomHalfPlane_isEnvelope (D : Finset Lattice) (u : Lattice)
    (hu : u ∈ D) (b : ℤ) :
    IsEnvelope D (bottomHalfPlane u b) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz
  exact hz u hu b (fun w hw => hw)

theorem seed_rays_in_agreementRegion {A : Type*}
    (D W : Finset Lattice) (x p : Lattice → A)
    (u k a : Lattice) (c b : ℤ)
    (huk : 0 < det u k) (hu : u ∈ D) (hnu : -u ∈ D)
    (hk : k ∈ D) (hnk : -k ∈ D)
    (hW : W.Nonempty)
    (hWe : IsEnvelope D (W : Set Lattice))
    (hWf : LongFaces D (W : Set Lattice))
    (hWsub : (W : Set Lattice) ⊆ wedge u k c)
    (hWbottom : ∀ z ∈ W, b ≤ det u z)
    (ha : a ∈ W) (hxp : AgreeOn x p (wedge u k c)) :
    let Q := bottomHalfPlane u b
    let R := agreementRegion D x p W Q
    (W : Set Lattice) ⊆ R ∧
      (∀ n : ℕ, a+n•u ∈ R) ∧
      (∀ n : ℕ, a+n•k ∈ R) := by
  let Q := bottomHalfPlane u b
  let R := agreementRegion D x p W Q
  have hbase : AgreementCandidate D x p W Q W := by
    refine ⟨Finset.Subset.rfl,?_,hWe,hWf,?_⟩
    · intro z hz
      exact hWbottom z hz
    · intro z hz
      exact hxp z (hWsub hz)
  refine ⟨candidate_subset_agreementRegion hbase,?_,?_⟩
  · intro n
    obtain ⟨T,hWT,hshift,_,_,hTe,hTf,hTw,hTb⟩ :=
      exists_forward_seed_window D W u k u c b huk hu hnu hk hnk hW
        hWf hWsub hWbottom (wedge_forward_first huk c)
        (by rw [det_self]) n
    have hTa : AgreeOn x p (T : Set Lattice) :=
      fun z hz => hxp z (hTw hz)
    have hTcand : AgreementCandidate D x p W Q T := by
      exact ⟨hWT,(fun z hz => hTb z hz),hTe,hTf,hTa⟩
    exact candidate_subset_agreementRegion hTcand (hshift a ha)
  · intro n
    obtain ⟨T,hWT,hshift,_,_,hTe,hTf,hTw,hTb⟩ :=
      exists_forward_seed_window D W u k k c b huk hu hnu hk hnk hW
        hWf hWsub hWbottom (wedge_forward_second huk c)
        (le_of_lt huk) n
    have hTa : AgreeOn x p (T : Set Lattice) :=
      fun z hz => hxp z (hTw hz)
    have hTcand : AgreementCandidate D x p W Q T := by
      exact ⟨hWT,(fun z hz => hTb z hz),hTe,hTf,hTa⟩
    exact candidate_subset_agreementRegion hTcand (hshift a ha)

theorem exists_seed_rays_in_agreementRegion {A : Type*} {n : ℕ}
    (hn : 2 ≤ n) (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (x p : Lattice → A) (u k : Lattice) (c : ℤ)
    (huk : 0 < det u k)
    (hu : u ∈ signedDirections v) (hnu : -u ∈ signedDirections v)
    (hk : k ∈ signedDirections v) (hnk : -k ∈ signedDirections v)
    (hxp : AgreeOn x p (wedge u k c)) :
    ∃ W : Finset Lattice, ∃ a : Lattice, ∃ b : ℤ,
      W.Nonempty ∧ IsLatticeConvex W ∧
      IsEnvelope (signedDirections v) (W : Set Lattice) ∧
      LongFaces (signedDirections v) (W : Set Lattice) ∧
      (W : Set Lattice) ⊆ wedge u k c ∧
      a ∈ W ∧ det u a = b ∧ 0 ≤ b ∧
      let R := agreementRegion (signedDirections v) x p W (bottomHalfPlane u b)
      (W : Set Lattice) ⊆ R ∧
        (∀ j : ℕ, a+j•u ∈ R) ∧
        (∀ j : ℕ, a+j•k ∈ R) := by
  obtain ⟨W,hW,hWc,hWe,hWf,hWsub⟩ :=
    exists_long_seed_in_wedge hn v hpair u k huk c
  obtain ⟨a,ha,hab⟩ := lowerSupport_attained W hW u
  let b := lowerSupport W u
  have hWbottom : ∀ z ∈ W, b ≤ det u z :=
    fun z hz => lowerSupport_le hz u
  have hb : 0 ≤ b := by
    change 0 ≤ lowerSupport W u
    rw [← hab]
    exact (hWsub ha).1
  obtain ⟨hRW,hrayu,hrayk⟩ := seed_rays_in_agreementRegion
    (signedDirections v) W x p u k a c b huk hu hnu hk hnk hW hWe hWf
      hWsub hWbottom ha hxp
  exact ⟨W,a,b,hW,hWc,hWe,hWf,hWsub,ha,hab,hb,hRW,hrayu,hrayk⟩

end
end NivatTrial.ColleCaseOneSeedRegion
