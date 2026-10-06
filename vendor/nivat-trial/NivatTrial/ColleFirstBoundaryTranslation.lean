import NivatTrial.ColleFirstBoundaryMinimum
import NivatTrial.ColleFiniteMaximalTranslation

/-! A bottom support at an arbitrary integer height can be centered at
an actual boundary point without changing the underlying configuration. -/

namespace NivatTrial.ColleFirstBoundaryTranslation

open NivatTrial.Geometry NivatTrial.RegionGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleEnvelopeTranslation
open NivatTrial.ColleMaximalTranslation NivatTrial.ColleFirstBoundaryMinimum
open scoped Classical
noncomputable section

theorem exists_recentered_first_boundary_at_height
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u k a : Lattice) (huk : 0 < det u k) (b : ℤ)
    (ha : a ∈ R) (ha0 : det u a = b)
    (hray : ∀ n : ℕ, a+n•u ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hproper : ∃ z : Lattice, b ≤ det u z ∧ z ∉ R) :
    ∃ c : Lattice, det u c = b ∧ c ∈ R ∧
      0 ∈ recenter R c ∧ -u ∉ recenter R c ∧
      (∀ n : ℕ, n•u ∈ recenter R c) ∧
      ForwardInvariant (recenter R c) u ∧
      ∀ N : ℤ, ∃ z ∈ recenter R c, N ≤ det u z := by
  let R₀ := recenter R a
  have hzero : (0 : Lattice) ∈ R₀ := by simpa [R₀,recenter] using ha
  have hray₀ (n : ℕ) : (0 : Lattice)+n•u ∈ R₀ := by
    simpa [R₀,recenter,add_comm] using hray n
  have hheight₀ : ∀ N : ℤ, ∃ z ∈ R₀, N ≤ det u z := by
    intro N
    obtain ⟨z,hz,hNz⟩ := hheight (N+b)
    refine ⟨z-a,by simpa [R₀,recenter] using hz,?_⟩
    rw [det_sub_right,ha0]
    omega
  have hproper₀ : ∃ z : Lattice, 0 ≤ det u z ∧ z ∉ R₀ := by
    obtain ⟨z,hz,hout⟩ := hproper
    refine ⟨z-a,?_,?_⟩
    · rw [det_sub_right,ha0]
      omega
    · simpa [R₀,recenter] using hout
  obtain ⟨w,hw0,hzero',hout,hray',hf,hh⟩ := exists_recentered_first_boundary
    D R₀ (isEnvelope_recenter hR a) u k 0 huk hzero
      (by simp [det]) hray₀ hheight₀ hproper₀
  have he : recenter R₀ w = recenter R (a+w) := recenter_recenter R a w
  have hc : a+w ∈ R := by
    rw [he] at hzero'
    simpa [recenter] using hzero'
  refine ⟨a+w,by rw [det_add_right,ha0,hw0,add_zero],hc,?_,?_,?_,?_,?_⟩
  · simpa only [he] using hzero'
  · simpa only [he] using hout
  · simpa only [he] using hray'
  · simpa only [he] using hf
  · simpa only [he] using hh

theorem recenter_bottomHalfPlane (u c : Lattice) (b : ℤ) (hc : det u c=b) :
    recenter {z : Lattice | b≤det u z} c = {z : Lattice | 0≤det u z} := by
  ext z
  change b≤det u (z+c) ↔ 0≤det u z
  rw [det_add_right,hc]
  omega

end
end NivatTrial.ColleFirstBoundaryTranslation
