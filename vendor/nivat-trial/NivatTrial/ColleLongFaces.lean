import NivatTrial.ColleFiniteEnvelope

/-! Minimum lengths of actual exposed faces. Each allowed direction d has
two points separated by d on every attained supporting face. For a convex
lattice region the whole segment between these points is present. These
length conditions survive chain unions and directional envelope closure. -/

namespace NivatTrial.ColleLongFaces

open NivatTrial.Geometry NivatTrial.Nonexpansive NivatTrial.RegionGeometry
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleFiniteEnvelope
open scoped Classical
noncomputable section

def LongFaces (D : Finset Lattice) (R : Set Lattice) : Prop :=
  ∀ d ∈ D, ∀ z ∈ R, (∀ w ∈ R, det d z ≤ det d w) →
    ∃ w ∈ R, w+d ∈ R ∧ det d w = det d z

theorem LongFaces.sUnion (D : Finset Lattice) (c : Set (Set Lattice))
    (hc : ∀ R ∈ c, LongFaces D R) : LongFaces D (⋃₀ c) := by
  intro d hd z hz hmin
  obtain ⟨R,hR,hzR⟩ := Set.mem_sUnion.mp hz
  have hsub : R ⊆ ⋃₀ c := fun w hw => Set.mem_sUnion.mpr ⟨R,hR,hw⟩
  obtain ⟨w,hw,hwd,he⟩ := hc R hR d hd z hzR (fun w hw => hmin w (hsub hw))
  exact ⟨w,hsub hw,hsub hwd,he⟩

theorem LongFaces.supportHull {D : Finset Lattice} {R : Set Lattice}
    (hR : LongFaces D R) : LongFaces D (supportHull D R) := by
  intro d hd z hz hmin
  obtain ⟨w,hw,hle⟩ := (mem_supportHull_iff D R z).mp hz d hd
  have hsub := subset_supportHull D R
  have heq : det d w = det d z := le_antisymm hle (hmin w (hsub hw))
  obtain ⟨v,hv,hvd,hve⟩ := hR d hd w hw (by
    intro v hv
    rw [heq]
    exact hmin v (hsub hv))
  exact ⟨v,hsub hv,hsub hvd,hve.trans heq⟩

theorem LongFaces.finite_envelope {D B : Finset Lattice}
    (hB : B.Nonempty) (hfaces : LongFaces D (B : Set Lattice)) :
    LongFaces D (envelope D (lowerSupport B)) := by
  rw [← supportHull_finset D B hB]
  exact hfaces.supportHull

theorem exists_maximal_long_agreement {A : Type*}
    (D : Finset Lattice) (x y : Lattice → A) (B Q : Set Lattice)
    (hB : IsEnvelope D B) (hfaces : LongFaces D B)
    (hBQ : B ⊆ Q) (hagree : AgreeOn x y B) :
    ∃ R : Set Lattice, B ⊆ R ∧ R ⊆ Q ∧ IsEnvelope D R ∧
      LongFaces D R ∧ AgreeOn x y R ∧
      ∀ T : Set Lattice, R ⊆ T → T ⊆ Q → IsEnvelope D T →
        LongFaces D T → AgreeOn x y T → T = R := by
  let C : Set (Set Lattice) := {R | B ⊆ R ∧ R ⊆ Q ∧
    IsEnvelope D R ∧ LongFaces D R ∧ AgreeOn x y R}
  have hBC : B ∈ C := ⟨Set.Subset.rfl,hBQ,hB,hfaces,hagree⟩
  have hchain (c : Set (Set Lattice)) (hc : c ⊆ C)
      (hlinear : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
      ∃ R ∈ C, ∀ T ∈ c, T ⊆ R := by
    refine ⟨⋃₀ c,?_,fun T hT z hz => Set.mem_sUnion.mpr ⟨T,hT,hz⟩⟩
    refine ⟨?_,?_,isEnvelope_sUnion_chain D c hlinear hne (fun T hT => (hc hT).2.2.1),
      LongFaces.sUnion D c (fun T hT => (hc hT).2.2.2.1),?_⟩
    · obtain ⟨T,hT⟩ := hne
      intro z hz
      exact Set.mem_sUnion.mpr ⟨T,hT,(hc hT).1 hz⟩
    · rintro z ⟨T,hT,hz⟩
      exact (hc hT).2.1 hz
    · rintro z ⟨T,hT,hz⟩
      exact (hc hT).2.2.2.2 z hz
  obtain ⟨R,hBR,hmax⟩ := zorn_subset_nonempty C hchain B hBC
  have hR := hmax.prop
  refine ⟨R,hBR,hR.2.1,hR.2.2.1,hR.2.2.2.1,hR.2.2.2.2,?_⟩
  intro T hRT hTQ hTenv hTfaces hTxy
  exact (hmax.eq_of_subset ⟨hBR.trans hRT,hTQ,hTenv,hTfaces,hTxy⟩ hRT).symm

/-- Maximality now includes the actual lower bounds on all exposed edge
lengths, while the half-strip defect still proves that the result is finite. -/
theorem exists_finite_maximal_long_agreement {A : Type*}
    (D B : Finset Lattice) (u : Lattice) (x y : Lattice → A)
    (hB : IsEnvelope D (B : Set Lattice)) (hfaces : LongFaces D (B : Set Lattice))
    (hagree : AgreeOn x y (B : Set Lattice))
    (hbad : ∃ z ∈ halfStrip B u, x z ≠ y z) :
    ∃ T : Finset Lattice, B ⊆ T ∧ (T : Set Lattice) ⊆ halfStrip B u ∧
      NivatTrial.LatticePolygon.IsLatticeConvex T ∧ IsEnvelope D (T : Set Lattice) ∧
      LongFaces D (T : Set Lattice) ∧ AgreeOn x y (T : Set Lattice) ∧
      ∀ R : Set Lattice, (T : Set Lattice) ⊆ R → R ⊆ halfStrip B u →
        IsEnvelope D R → LongFaces D R → AgreeOn x y R → R = (T : Set Lattice) := by
  obtain ⟨R,hBR,hRQ,hR,hRfaces,hxy,hmax⟩ := exists_maximal_long_agreement
    D x y (B : Set Lattice) (halfStrip B u) hB hfaces (base_subset_halfStrip B u) hagree
  have hf := agreement_envelope_finite D B u x y hbad R hR hBR hRQ hxy
  let T := hf.toFinset
  have hT : (T : Set Lattice) = R := hf.coe_toFinset
  refine ⟨T,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    have hzR := hBR hz
    rwa [← hT] at hzR
  · rwa [hT]
  · apply latticeConvex_finset_of_region T
    rw [hT]
    exact hR.latticeConvex
  · rwa [hT]
  · rwa [hT]
  · rwa [hT]
  · simpa only [hT] using hmax

end
end NivatTrial.ColleLongFaces
