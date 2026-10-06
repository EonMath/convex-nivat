import NivatTrial.ColleEnvelopeTranslation

/-! Expanding an envelope by the hull of one forward translate preserves
all exposed edge-length bounds. When the permitted half-strip is itself an
envelope, this gives a genuine admissible competitor to a maximal agreement
window and therefore forces a new boundary disagreement. -/

namespace NivatTrial.ColleEnvelopeExpansion

open NivatTrial.Geometry NivatTrial.RegionGeometry NivatTrial.Nonexpansive
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation
open scoped Classical
noncomputable section

theorem longFaces_union {D : Finset Lattice} {R S : Set Lattice}
    (hR : LongFaces D R) (hS : LongFaces D S) : LongFaces D (R ∪ S) := by
  intro d hd z hz hmin
  rcases hz with hzR | hzS
  · obtain ⟨w,hw,hwd,he⟩ := hR d hd z hzR (fun w hw => hmin w (Or.inl hw))
    exact ⟨w,Or.inl hw,Or.inl hwd,he⟩
  · obtain ⟨w,hw,hwd,he⟩ := hS d hd z hzS (fun w hw => hmin w (Or.inr hw))
    exact ⟨w,Or.inr hw,Or.inr hwd,he⟩

def stepExpansion (D : Finset Lattice) (R : Set Lattice) (u : Lattice) : Set Lattice :=
  supportHull D (R ∪ recenter R (-u))

theorem subset_stepExpansion (D : Finset Lattice) (R : Set Lattice) (u : Lattice) :
    R ⊆ stepExpansion D R u := fun _ hz => subset_supportHull D _ (Or.inl hz)

theorem translate_mem_stepExpansion (D : Finset Lattice) (R : Set Lattice)
    (u : Lattice) {z : Lattice} (hz : z ∈ R) : z+u ∈ stepExpansion D R u := by
  apply subset_supportHull D _
  right
  simpa [recenter] using hz

theorem stepExpansion_longFaces {D : Finset Lattice} {R : Set Lattice}
    (hR : LongFaces D R) (u : Lattice) : LongFaces D (stepExpansion D R u) :=
  (longFaces_union hR (longFaces_recenter hR (-u))).supportHull

theorem stepExpansion_subset {D : Finset Lattice} {R Q : Set Lattice}
    (hQ : IsEnvelope D Q) (hRQ : R ⊆ Q) (u : Lattice)
    (hu : ForwardInvariant Q u) : stepExpansion D R u ⊆ Q := by
  intro z hz
  rw [← hQ]
  apply supportHull_mono D ?_ hz
  intro w hw
  rcases hw with hw | hw
  · exact hRQ hw
  · have hh := hu (w-u) (hRQ hw)
    simpa using hh

theorem defect_in_stepExpansion {A : Type*}
    (D : Finset Lattice) (R Q : Set Lattice) (u : Lattice)
    (x p : Lattice → A) (hQ : IsEnvelope D Q) (hRQ : R ⊆ Q)
    (hu : ForwardInvariant Q u) (hfaces : LongFaces D R) (hxp : AgreeOn x p R)
    (hmax : ∀ S : Set Lattice, R ⊆ S → S ⊆ Q → IsEnvelope D S →
      LongFaces D S → AgreeOn x p S → S = R)
    (hnew : ∃ z ∈ R, z+u ∉ R) :
    ∃ z ∈ stepExpansion D R u, z ∈ Q ∧ z ∉ R ∧ x z ≠ p z := by
  have hsub := stepExpansion_subset hQ hRQ u hu
  have hbad : ∃ z ∈ stepExpansion D R u, x z ≠ p z := by
    by_contra hn
    have hagree : AgreeOn x p (stepExpansion D R u) := by
      intro z hz
      by_contra he
      exact hn ⟨z,hz,he⟩
    have he := hmax _ (subset_stepExpansion D R u) hsub
      (supportHull_idempotent D _) (stepExpansion_longFaces hfaces u) hagree
    obtain ⟨z,hz,hnot⟩ := hnew
    exact hnot (he ▸ translate_mem_stepExpansion D R u hz)
  obtain ⟨z,hz,hbad⟩ := hbad
  exact ⟨z,hz,hsub hz,fun hm => hbad (hxp z hm),hbad⟩

end
end NivatTrial.ColleEnvelopeExpansion
