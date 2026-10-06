import NivatTrial.ColleAgreementExhaustion
import NivatTrial.ColleAdjacentDirections
import NivatTrial.ColleHalfStripEnvelope

/-! The Case 2 sample windows with maximality and their actual ambient
half-strips retained. These are the inputs to defect-preserving extraction. -/

namespace NivatTrial.ColleCaseTwoWindows

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.RegionGeometry NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleZonotopeEnvelope NivatTrial.ColleFiniteEnvelope
open NivatTrial.ColleHalfStripEnvelope NivatTrial.ColleAgreementExhaustion
open NivatTrial.ColleAdjacentDirections
open scoped Classical
noncomputable section

theorem halfStrip_eq_of_intermediate (B T : Finset Lattice) (u : Lattice)
    (hBT : B ⊆ T) (hTstrip : (T : Set Lattice) ⊆ halfStrip B u) :
    halfStrip T u = halfStrip B u := by
  apply Set.Subset.antisymm
  · exact halfStrip_subset_of_forward hTstrip (halfStrip_forward B u)
  · exact halfStrip_subset_of_forward
      (fun _ hb => base_subset_halfStrip T u (hBT hb)) (halfStrip_forward T u)

theorem exists_case_two_maximal_sequence {A : Type*} {n : ℕ} (hn : 2 ≤ n)
    (θ p : Lattice → A) (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0) (i : Fin n)
    (hpatch : ∀ B₀ : Finset Lattice,
      IsEnvelope (signedDirections v) (B₀ : Set Lattice) →
      LongFaces (signedDirections v) (B₀ : Set Lattice) →
      lowerSupport B₀ (v i) = 0 →
      ∃ B : Finset Lattice, ∃ x ∈ languageHull θ,
        B₀ ⊆ B ∧ IsEnvelope (signedDirections v) (B : Set Lattice) ∧
        LongFaces (signedDirections v) (B : Set Lattice) ∧
        lowerSupport B (v i) = 0 ∧ AgreeOn x p (B : Set Lattice) ∧
        ∃ z ∈ halfStrip B (v i), x z ≠ p z) :
    ∃ k : Lattice, (∃ j : Fin n, k = v j ∨ k = -v j) ∧
      0 < det (v i) k ∧
      ∃ T : ℕ → Finset Lattice, ∃ x : ℕ → Lattice → A,
        (∀ N, x N ∈ languageHull θ) ∧
        (∀ N, IsEnvelope (signedDirections v) (T N : Set Lattice)) ∧
        (∀ N, LongFaces (signedDirections v) (T N : Set Lattice)) ∧
        (∀ N, 0 ∈ T N) ∧ (∀ N, N•(v i) ∈ T N) ∧ (∀ N, N•k ∈ T N) ∧
        (∀ N, ∀ z ∈ T N, 0 ≤ det (v i) z) ∧
        (∀ N, AgreeOn (x N) p (T N : Set Lattice)) ∧
        (∀ N, IsEnvelope (signedDirections v) (halfStrip (T N) (v i))) ∧
        (∀ N, ForwardInvariant (halfStrip (T N) (v i)) (v i)) ∧
        ∀ N, ∀ R : Set Lattice, (T N : Set Lattice) ⊆ R →
          R ⊆ halfStrip (T N) (v i) → IsEnvelope (signedDirections v) R →
          LongFaces (signedDirections v) R → AgreeOn (x N) p R → R = (T N : Set Lattice) := by
  obtain ⟨j,k,hk,huk,_⟩ := exists_adjacent_to_component hn v hpair i
  have hu0 : v i ≠ 0 := by intro he; simp [he,det] at huk
  have hu : v i ∈ signedDirections v := (mem_signedDirections v _).mpr ⟨i,Or.inl rfl⟩
  have hnu : -v i ∈ signedDirections v := (mem_signedDirections v _).mpr ⟨i,Or.inr rfl⟩
  let F : ℕ → Finset Lattice := fun N => {0,N•(v i),N•k}
  have hF (N : ℕ) : ∀ z ∈ F N, 0 ≤ det (v i) z := by
    intro z hz
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simp
    · simp only [det_nsmul_right,det_self,mul_zero,le_refl]
    · rw [det_nsmul_right]
      exact mul_nonneg (by positivity) huk.le
  have hchoice (N : ℕ) : ∃ T : Finset Lattice, ∃ x ∈ languageHull θ,
      IsEnvelope (signedDirections v) (T : Set Lattice) ∧
      LongFaces (signedDirections v) (T : Set Lattice) ∧
      0 ∈ T ∧ N•(v i) ∈ T ∧ N•k ∈ T ∧
      (∀ z ∈ T, 0 ≤ det (v i) z) ∧ AgreeOn x p (T : Set Lattice) ∧
      IsEnvelope (signedDirections v) (halfStrip T (v i)) ∧
      ForwardInvariant (halfStrip T (v i)) (v i) ∧
      ∀ R : Set Lattice, (T : Set Lattice) ⊆ R → R ⊆ halfStrip T (v i) →
        IsEnvelope (signedDirections v) R → LongFaces (signedDirections v) R →
        AgreeOn x p R → R = (T : Set Lattice) := by
    obtain ⟨B,T,x,hx,hFB,hBT,hTstrip,hTe,hTf,hagree,hhalf,hmax⟩ :=
      exists_maximal_agreement_window_with_samples hn θ p v hpair i hpatch (F N) (hF N)
    have hFT : F N ⊆ T := hFB.trans hBT
    have hzero : 0 ∈ T := hFT (by simp [F])
    have heq := halfStrip_eq_of_intermediate B T (v i) hBT hTstrip
    refine ⟨T,x,hx,hTe,hTf,hzero,hFT (by simp [F]),hFT (by simp [F]),
      hhalf,hagree,halfStrip_isEnvelope (signedDirections v) T (v i) ⟨0,hzero⟩
        hTe hTf hu0 hu hnu,halfStrip_forward T (v i),?_⟩
    intro R hTR hRQ hRe hRf hRp
    exact hmax R hTR (by rwa [heq] at hRQ) hRe hRf hRp
  choose T x hx hTe hTf hzero hback hheight hhalf hagree hQe hQf hmax using hchoice
  exact ⟨k,⟨j,hk⟩,huk,T,x,hx,hTe,hTf,hzero,hback,hheight,hhalf,hagree,hQe,hQf,hmax⟩

end
end NivatTrial.ColleCaseTwoWindows
