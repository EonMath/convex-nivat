import NivatTrial.ColleMaximalEnvelope

/-! A proper agreement envelope inside a half-strip is finite. Any infinite
envelope in that strip is invariant in the forward strip direction; if it
contains the base, it contains the entire half-strip. -/

namespace NivatTrial.ColleFiniteEnvelope

open NivatTrial.Geometry NivatTrial.RegionGeometry NivatTrial.Nonexpansive
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open scoped Classical
noncomputable section

def halfStrip (B : Finset Lattice) (u : Lattice) : Set Lattice :=
  {z | ∃ b ∈ B, ∃ n : ℕ, z = b+n•u}

theorem base_subset_halfStrip (B : Finset Lattice) (u : Lattice) :
    (B : Set Lattice) ⊆ halfStrip B u :=
  fun b hb => ⟨b,hb,0,by simp⟩

theorem halfStrip_subset_of_forward {B : Finset Lattice} {u : Lattice}
    {R : Set Lattice} (hBR : (B : Set Lattice) ⊆ R) (hR : ForwardInvariant R u) :
    halfStrip B u ⊆ R := by
  rintro z ⟨b,hb,n,rfl⟩
  exact hR.nsmul n b (hBR hb)

/-- A half-plane facing against the strip direction cuts off only finitely
many of its lattice points. -/
theorem finite_halfStrip_cut (B : Finset Lattice) (u d : Lattice)
    (hd : det d u < 0) (t : ℤ) :
    {z ∈ halfStrip B u | t ≤ det d z}.Finite := by
  let C : Finset Lattice := B.biUnion (fun b =>
    (Finset.range ((det d b-t).natAbs+1)).image (fun n => b+n•u))
  apply C.finite_toSet.subset
  rintro z ⟨⟨b,hb,n,rfl⟩,hz⟩
  rw [det_add_right,det_nsmul_right] at hz
  have hdn : det d u ≤ -1 := by omega
  have hnnonneg : (0:ℤ) ≤ n := by omega
  have hmul : (n:ℤ) * det d u ≤ -(n:ℤ) := by nlinarith
  have hnb : (n:ℤ) ≤ det d b-t := by omega
  have habs : det d b-t ≤ ((det d b-t).natAbs:ℤ) := Int.le_natAbs
  have hn : n < (det d b-t).natAbs+1 := by omega
  exact Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩⟩

theorem forward_of_infinite_envelope (D B : Finset Lattice) (u : Lattice)
    (R : Set Lattice) (hR : IsEnvelope D R) (hsub : R ⊆ halfStrip B u)
    (hinfinite : R.Infinite) : ForwardInvariant R u := by
  intro z hz
  rw [← hR]
  intro d hd t ht
  have hdu : 0 ≤ det d u := by
    by_contra hn
    have hfinite := finite_halfStrip_cut B u d (lt_of_not_ge hn) t
    have hrfinite : R.Finite := hfinite.subset (fun w hw => ⟨hsub hw,ht w hw⟩)
    exact hinfinite hrfinite
  rw [det_add_right]
  exact (ht z hz).trans (le_add_of_nonneg_right hdu)

theorem infinite_envelope_eq_halfStrip (D B : Finset Lattice) (u : Lattice)
    (R : Set Lattice) (hR : IsEnvelope D R)
    (hBR : (B : Set Lattice) ⊆ R) (hRQ : R ⊆ halfStrip B u)
    (hinfinite : R.Infinite) : R = halfStrip B u := by
  apply Set.Subset.antisymm hRQ
  exact halfStrip_subset_of_forward hBR
    (forward_of_infinite_envelope D B u R hR hRQ hinfinite)

/-- The defect is part of the actual configuration. It excludes the
infinite-envelope case without a separate boundedness assumption. -/
theorem agreement_envelope_finite {A : Type*}
    (D B : Finset Lattice) (u : Lattice) (x y : Lattice → A)
    (hbad : ∃ z ∈ halfStrip B u, x z ≠ y z)
    (R : Set Lattice) (hR : IsEnvelope D R)
    (hBR : (B : Set Lattice) ⊆ R) (hRQ : R ⊆ halfStrip B u)
    (hagree : AgreeOn x y R) : R.Finite := by
  by_contra hi
  have hinfinite : R.Infinite := hi
  have heq := infinite_envelope_eq_halfStrip D B u R hR hBR hRQ hinfinite
  obtain ⟨z,hz,hne⟩ := hbad
  exact hne (hagree z (heq.symm ▸ hz))

theorem exists_finite_maximal_agreement {A : Type*}
    (D B : Finset Lattice) (u : Lattice) (x y : Lattice → A)
    (hB : IsEnvelope D (B : Set Lattice)) (hagree : AgreeOn x y (B : Set Lattice))
    (hbad : ∃ z ∈ halfStrip B u, x z ≠ y z) :
    ∃ T : Finset Lattice, B ⊆ T ∧ (T : Set Lattice) ⊆ halfStrip B u ∧
      NivatTrial.LatticePolygon.IsLatticeConvex T ∧ IsEnvelope D (T : Set Lattice) ∧
      AgreeOn x y (T : Set Lattice) ∧
      ∀ R : Set Lattice, (T : Set Lattice) ⊆ R → R ⊆ halfStrip B u →
        IsEnvelope D R → AgreeOn x y R → R = (T : Set Lattice) := by
  obtain ⟨R,hBR,hRQ,hR,hxy,hmax⟩ := exists_maximal_agreement_envelope
    D x y (B : Set Lattice) (halfStrip B u) hB (base_subset_halfStrip B u) hagree
  have hf := agreement_envelope_finite D B u x y hbad R hR hBR hRQ hxy
  let T := hf.toFinset
  have hT : (T : Set Lattice) = R := hf.coe_toFinset
  refine ⟨T,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    have hzR := hBR hz
    rwa [← hT] at hzR
  · rwa [hT]
  · apply latticeConvex_finset_of_region T
    rw [hT]
    exact hR.latticeConvex
  · rwa [hT]
  · rwa [hT]
  · simpa only [hT] using hmax

end
end NivatTrial.ColleFiniteEnvelope
