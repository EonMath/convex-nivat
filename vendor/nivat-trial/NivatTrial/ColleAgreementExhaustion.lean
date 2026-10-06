import NivatTrial.ColleZonotopeEnvelope
import NivatTrial.ColleGrowingEnvelopes

/-! Construct finite maximal agreement windows from the actual local
half-strip failure hypothesis of Colle's Lemma 3.5. The prescribed bottom
face is maintained while arbitrary finite samples are absorbed. -/

namespace NivatTrial.ColleAgreementExhaustion

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces NivatTrial.ColleFiniteEnvelope
open NivatTrial.ColleZonotopeEnvelope
open scoped Classical
noncomputable section

theorem exists_maximal_agreement_window_with_samples
    {A : Type*} {n : ℕ} (hn : 2 ≤ n) (θ p : Lattice → A)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0) (i : Fin n)
    (hpatch : ∀ B₀ : Finset Lattice,
      IsEnvelope (signedDirections v) (B₀ : Set Lattice) →
      LongFaces (signedDirections v) (B₀ : Set Lattice) →
      lowerSupport B₀ (v i) = 0 →
      ∃ B : Finset Lattice, ∃ x ∈ languageHull θ,
        B₀ ⊆ B ∧ IsEnvelope (signedDirections v) (B : Set Lattice) ∧
        LongFaces (signedDirections v) (B : Set Lattice) ∧
        lowerSupport B (v i) = 0 ∧ AgreeOn x p (B : Set Lattice) ∧
        ∃ z ∈ halfStrip B (v i), x z ≠ p z)
    (F : Finset Lattice) (hF : ∀ z ∈ F, 0 ≤ det (v i) z) :
    ∃ B T : Finset Lattice, ∃ x ∈ languageHull θ,
      F ⊆ B ∧ B ⊆ T ∧ (T : Set Lattice) ⊆ halfStrip B (v i) ∧
      IsEnvelope (signedDirections v) (T : Set Lattice) ∧
      LongFaces (signedDirections v) (T : Set Lattice) ∧
      AgreeOn x p (T : Set Lattice) ∧
      (∀ z ∈ T, 0 ≤ det (v i) z) ∧
      ∀ R : Set Lattice, (T : Set Lattice) ⊆ R → R ⊆ halfStrip B (v i) →
        IsEnvelope (signedDirections v) R → LongFaces (signedDirections v) R →
        AgreeOn x p R → R = (T : Set Lattice) := by
  obtain ⟨B₀,hFB₀,_,hB₀env,hB₀faces,hB₀level⟩ :=
    exists_finite_long_envelope_on_face hn v hpair i F hF
  obtain ⟨B,x,hx,hB₀B,hBenv,hBfaces,hBlevel,hBp,hbad⟩ :=
    hpatch B₀ hB₀env hB₀faces hB₀level
  obtain ⟨T,hBT,hTstrip,_,hTenv,hTfaces,hTp,hmax⟩ :=
    exists_finite_maximal_long_agreement (signedDirections v) B (v i) x p
      hBenv hBfaces hBp hbad
  refine ⟨B,T,x,hx,hFB₀.trans hB₀B,hBT,hTstrip,hTenv,hTfaces,hTp,?_,hmax⟩
  intro z hz
  obtain ⟨b,hb,m,rfl⟩ := hTstrip hz
  have hbound := lowerSupport_le hb (v i)
  rw [hBlevel] at hbound
  simpa only [det_add_right,det_nsmul_right,det_self,mul_zero,add_zero] using hbound

end
end NivatTrial.ColleAgreementExhaustion
