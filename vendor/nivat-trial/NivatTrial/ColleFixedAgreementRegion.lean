import NivatTrial.ColleDirectedAgreement

/-! The fixed-configuration maximal region has a finite long-window
exhaustion and actual finite-extension maximality, both proved by coding. -/

namespace NivatTrial.ColleFixedAgreementRegion

open NivatTrial.Geometry NivatTrial.LatticePolygon NivatTrial.RegionGeometry
open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.OneSidedRecurrence
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces NivatTrial.ColleDirectedAgreement
open NivatTrial.ColleMaximalAgreementLimit
open scoped Classical
noncomputable section

def agreementRegion {A : Type*} (D : Finset Lattice) (x p : Lattice → A)
    (B : Finset Lattice) (Q : Set Lattice) : Set Lattice :=
  windowUnion (AgreementCandidate D x p B Q)

theorem candidate_subset_agreementRegion {A : Type*}
    {D B T : Finset Lattice} {x p : Lattice → A} {Q : Set Lattice}
    (hT : AgreementCandidate D x p B Q T) :
    (T : Set Lattice) ⊆ agreementRegion D x p B Q := fun _ hz => ⟨T,hT,hz⟩

theorem agreementRegion_properties {A : Type*}
    (θ : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ d ∈ hs, d≠0)
    (hind : hs.Pairwise (fun d e => det d e≠0))
    (hann : iteratedIncrement hs (encode code θ)=0)
    (x p : Lattice → A) (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (D : Finset Lattice) (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (a b : Lattice) (hab : det a b≠0)
    (ha : a ∈ D) (hna : -a ∈ D) (hb : b ∈ D) (hnb : -b ∈ D)
    (Q : Set Lattice) (hQ : IsEnvelope D Q)
    (B : Finset Lattice) (hB : B.Nonempty)
    (hBe : IsEnvelope D (B : Set Lattice)) (hBf : LongFaces D (B : Set Lattice))
    (hBQ : (B : Set Lattice) ⊆ Q) (hBa : AgreeOn x p (B : Set Lattice)) :
    let R := agreementRegion D x p B Q
    (B : Set Lattice) ⊆ R ∧ R ⊆ Q ∧ IsEnvelope D R ∧ LongFaces D R ∧
      AgreeOn x p R ∧ FiniteExtensionMaximal D x p R Q ∧
      ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
        ∃ T : Finset Lattice, B ⊆ T ∧ F ⊆ T ∧ (T : Set Lattice) ⊆ R ∧
          IsEnvelope D (T : Set Lattice) ∧ LongFaces D (T : Set Lattice) := by
  let C := AgreementCandidate D x p B Q
  have hBC : C B := ⟨Finset.Subset.rfl,hBQ,hBe,hBf,hBa⟩
  have hmerge : ∀ T S, C T → C S → ∃ U, C U ∧ T ⊆ U ∧ S ⊆ U := by
    intro T S hT hS
    obtain ⟨U,hTU,hSU,hUQ,hUe,hUf,hUa⟩ := finite_agreement_merge θ code hcode
      hs hne hind hann x p hx hp D hdirs a b hab ha hna hb hnb Q hQ T S B
      (latticeConvex_finset_of_region _ hT.2.2.1.latticeConvex)
      (latticeConvex_finset_of_region _ hS.2.2.1.latticeConvex)
      hT.2.2.2.1 hS.2.2.2.1 hT.2.1 hS.2.1 hT.2.2.2.2 hS.2.2.2.2
      hB (latticeConvex_finset_of_region _ hBe.latticeConvex) hBf hT.1 hS.1
    exact ⟨U,⟨hT.1.trans hTU,hUQ,hUe,hUf,hUa⟩,hTU,hSU⟩
  have hcover (F : Finset Lattice)
      (hF : (F : Set Lattice) ⊆ agreementRegion D x p B Q) :
      ∃ T, C T ∧ F ⊆ T := finite_subset_windowUnion C ⟨B,hBC⟩ hmerge F hF
  refine ⟨candidate_subset_agreementRegion hBC,?_,?_,?_,?_,?_,?_⟩
  · rintro z ⟨T,hT,hz⟩
    exact hT.2.1 hz
  · exact windowUnion_isEnvelope D C ⟨B,hBC⟩ hmerge (fun T hT => hT.2.2.1)
  · exact windowUnion_longFaces D C (fun T hT => hT.2.2.2.1)
  · rintro z ⟨T,hT,hz⟩
    exact hT.2.2.2.2 z hz
  · intro S W hSc hSf hW hWc hWf hWS hWR hSQ hSa
    obtain ⟨T,hT,hWT⟩ := hcover W hWR
    obtain ⟨U,hTU,hSU,hUQ,hUe,hUf,hUa⟩ := finite_agreement_merge θ code hcode
      hs hne hind hann x p hx hp D hdirs a b hab ha hna hb hnb Q hQ T S W
      (latticeConvex_finset_of_region _ hT.2.2.1.latticeConvex) hSc
      hT.2.2.2.1 hSf hT.2.1 hSQ hT.2.2.2.2 hSa hW hWc hWf hWT hWS
    have hUC : C U := ⟨hT.1.trans hTU,hUQ,hUe,hUf,hUa⟩
    exact fun z hz => candidate_subset_agreementRegion hUC (hSU hz)
  · intro F hF
    obtain ⟨T,hT,hFT⟩ := hcover F hF
    exact ⟨T,hT.1,hFT,candidate_subset_agreementRegion hT,hT.2.2.1,hT.2.2.2.1⟩

end
end NivatTrial.ColleFixedAgreementRegion
