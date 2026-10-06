import NivatTrial.ColleEnvelopeTranslation
import NivatTrial.SupportGeometry
import NivatTrial.PeriodicDifference

/-! Centre a finite convex envelope at the last point of its bottom face.
A long original bottom segment becomes a growing backward ray, while the
next forward point stays outside. Transverse heights are unchanged. -/

namespace NivatTrial.ColleBoundaryRecenter

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.PeriodicDifference NivatTrial.ColleEnvelopeTranslation
open scoped Classical
noncomputable section

theorem backward_segment_mem (T : Finset Lattice) (hT : IsLatticeConvex T)
    (hzero : 0 ∈ T) (u k c : Lattice) (huk : 0 < det u k)
    (hc : c ∈ T) (huc : det u c = 0) (n : ℕ)
    (hbound : (n:ℤ)*det u k ≤ det c k) : c-n•u ∈ T := by
  by_cases hn : n = 0
  · simpa [hn] using hc
  have hnpos : (0:ℤ) < n := by omega
  have hck : 0 < det c k := lt_of_lt_of_le (mul_pos hnpos huk) hbound
  have hckR : (0:ℝ) < det c k := by exact_mod_cast hck
  have hukR : (0:ℝ) < det u k := by exact_mod_cast huk
  have hboundR : (n:ℝ)*(det u k:ℝ) ≤ (det c k:ℝ) := by exact_mod_cast hbound
  have hcRel : (det u k : ℝ) • embed c = (det c k : ℝ) • embed u := by
    have he := congrArg embed (cramer_identity u k c)
    simpa only [embed_zsmul,embed_add,huc,Int.cast_zero,zero_smul,add_zero] using he
  have huRel : embed u = ((det u k:ℝ)/(det c k:ℝ)) • embed c := by
    calc
      embed u = (det c k:ℝ)⁻¹ • ((det c k:ℝ) • embed u) := by
        rw [smul_smul,inv_mul_cancel₀ (ne_of_gt hckR),one_smul]
      _ = (det c k:ℝ)⁻¹ • ((det u k:ℝ) • embed c) := by rw [hcRel]
      _ = ((det u k:ℝ)/(det c k:ℝ)) • embed c := by rw [smul_smul]; congr 1; ring
  let a : ℝ := (n:ℝ)*(det u k:ℝ)/(det c k:ℝ)
  have ha0 : 0 ≤ a := div_nonneg (mul_nonneg (by positivity) hukR.le) hckR.le
  have ha1 : a ≤ 1 := (div_le_one hckR).mpr hboundR
  have hm := (windowHull_convex T) (mem_windowHull_of_mem T hzero)
    (mem_windowHull_of_mem T hc) ha0 (by linarith : 0 ≤ 1-a) (by ring : a+(1-a)=1)
  apply (hT (c-n•u)).mp
  have heq : a • embed (0:Lattice)+(1-a) • embed c = embed (c-n•u) := by
    rw [embed_zero,smul_zero,zero_add,embed_sub,embed_nsmul,huRel,smul_smul]
    dsimp [a]
    rw [sub_smul,one_smul]
    congr 2
    ring
  rwa [heq] at hm

theorem exists_last_boundary_point (T : Finset Lattice) (hzero : 0 ∈ T)
    (u k : Lattice) (huk : 0 < det u k) :
    ∃ c ∈ T, det u c = 0 ∧ c+u ∉ T ∧
      ∀ z ∈ T, det u z = 0 → det z k ≤ det c k := by
  let B := T.filter (fun z => det u z = 0)
  have hB : B.Nonempty := ⟨0,by simp [B,hzero]⟩
  obtain ⟨c,hc,hmax⟩ := B.exists_max_image (fun z => det z k) hB
  have hcT := (Finset.mem_filter.mp hc).1
  have huc := (Finset.mem_filter.mp hc).2
  refine ⟨c,hcT,huc,?_,fun z hz he => hmax z (Finset.mem_filter.mpr ⟨hz,he⟩)⟩
  intro hcu
  have hmem : c+u ∈ B := Finset.mem_filter.mpr ⟨hcu,by simp [huc]⟩
  have hh := hmax (c+u) hmem
  have he : det (c+u) k = det c k+det u k := by simp [det]; ring
  rw [he] at hh
  omega

theorem recenter_with_growing_backward_segment
    (T : Finset Lattice) (hT : IsLatticeConvex T) (hzero : 0 ∈ T)
    (u k : Lattice) (huk : 0 < det u k) (N : ℕ) (hN : N•u ∈ T) :
    ∃ c ∈ T, det u c = 0 ∧
      0 ∈ recenterWindow T c ∧ u ∉ recenterWindow T c ∧
      (∀ n ≤ N, -(n•u) ∈ recenterWindow T c) ∧
      ∀ z, det u (z-c) = det u z := by
  obtain ⟨c,hc,huc,hcu,hmax⟩ := exists_last_boundary_point T hzero u k huk
  refine ⟨c,hc,huc,by simpa using hc,by simpa [add_comm] using hcu,?_,?_⟩
  · intro n hn
    rw [mem_recenterWindow]
    have hb := hmax (N•u) hN (by simp only [det_nsmul_right,det_self,mul_zero])
    have hnN : (n:ℤ) ≤ N := by exact_mod_cast hn
    have he : det (N•u) k = (N:ℤ)*det u k := by simp [det,nsmul_eq_mul]; ring
    rw [he] at hb
    have hnB : (n:ℤ)*det u k ≤ det c k := (mul_le_mul_of_nonneg_right hnN huk.le).trans hb
    simpa [sub_eq_add_neg,add_comm] using backward_segment_mem T hT hzero u k c huk hc huc n hnB
  · intro z
    simp [huc]

end
end NivatTrial.ColleBoundaryRecenter
