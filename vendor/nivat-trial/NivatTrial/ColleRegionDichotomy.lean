import NivatTrial.ColleAgreementExhaustion

/-! The actual two-case split of Colle's regional construction. A periodic
reference in the language hull either agrees with an original translate on
one whole half-strip, or arbitrarily large fixed-face windows have a real
defect farther along that same half-strip. -/

namespace NivatTrial.ColleRegionDichotomy

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces NivatTrial.ColleFiniteEnvelope
open NivatTrial.ColleZonotopeEnvelope
open scoped Classical
noncomputable section

theorem halfStrip_agreement_or_arbitrarily_large_defects
    {A : Type*} {n : ℕ} (hn : 2 ≤ n) (θ p : Lattice → A)
    (hp : p ∈ languageHull θ) (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0) (i : Fin n) :
    (∃ B : Finset Lattice, ∃ t : Lattice, 0 ∈ B ∧
      IsEnvelope (signedDirections v) (B : Set Lattice) ∧
      LongFaces (signedDirections v) (B : Set Lattice) ∧
      lowerSupport B (v i) = 0 ∧ AgreeOn (shift t θ) p (halfStrip B (v i))) ∨
    (∀ F : Finset Lattice, (∀ z ∈ F, 0 ≤ det (v i) z) →
      ∃ B : Finset Lattice, ∃ t : Lattice, F ⊆ B ∧ 0 ∈ B ∧
        IsEnvelope (signedDirections v) (B : Set Lattice) ∧
        LongFaces (signedDirections v) (B : Set Lattice) ∧
        lowerSupport B (v i) = 0 ∧ AgreeOn (shift t θ) p (B : Set Lattice) ∧
        ∃ z ∈ halfStrip B (v i), shift t θ z ≠ p z) := by
  by_cases hcase : ∃ B : Finset Lattice, ∃ t : Lattice, 0 ∈ B ∧
      IsEnvelope (signedDirections v) (B : Set Lattice) ∧
      LongFaces (signedDirections v) (B : Set Lattice) ∧
      lowerSupport B (v i) = 0 ∧ AgreeOn (shift t θ) p (halfStrip B (v i))
  · exact Or.inl hcase
  · right
    intro F hF
    have hF0 : ∀ z ∈ insert 0 F, 0 ≤ det (v i) z := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp
      · exact hF z hz
    obtain ⟨B,hFB,_,hBenv,hBfaces,hBlevel⟩ :=
      exists_finite_long_envelope_on_face hn v hpair i (insert 0 F) hF0
    have hzero : 0 ∈ B := hFB (Finset.mem_insert_self 0 F)
    obtain ⟨t,ht⟩ := hp B
    refine ⟨B,t,(Finset.subset_insert 0 F).trans hFB,hzero,hBenv,hBfaces,hBlevel,ht,?_⟩
    by_contra hbad
    apply hcase
    refine ⟨B,t,hzero,hBenv,hBfaces,hBlevel,?_⟩
    intro z hz
    by_contra he
    exact hbad ⟨z,hz,he⟩

end
end NivatTrial.ColleRegionDichotomy
