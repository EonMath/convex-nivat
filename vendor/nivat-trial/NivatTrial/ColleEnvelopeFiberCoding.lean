import NivatTrial.ColleZonotopePlacement

/-! A long-faced lattice-convex window meets every translation residue at
each of its transverse levels. Two intersecting windows consequently meet
every such residue throughout the union of their transverse intervals. -/

namespace NivatTrial.ColleEnvelopeFiberCoding

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.ColleGenerating NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleLongFaces NivatTrial.ColleHalfStripEnvelope
open NivatTrial.ColleZonotopePlacement
open scoped Classical
noncomputable section

theorem segment_at_supported_level (T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hfaces : LongFaces {u,-u} (T : Set Lattice))
    (z : Lattice) (hlo : lowerSupport T u ≤ det u z)
    (hhi : lowerSupport T (-u) ≤ det (-u) z) :
    ∃ q : ℝ×ℝ, q ∈ windowHull T ∧ q+embed u ∈ windowHull T ∧
      linearScore (embed u) q = linearScore (embed u) (embed z) := by
  obtain ⟨a,ha,hea⟩ := lowerSupport_attained T hT u
  obtain ⟨b,hb,heb⟩ := lowerSupport_attained T hT (-u)
  obtain ⟨qa,hqa,hqau,hqae⟩ := segment_in_windowHull T u hT hfaces a ha
  obtain ⟨qb,hqb,hqbu,hqbe⟩ := segment_in_windowHull T u hT hfaces b hb
  apply segment_at_height (windowHull_convex T) u qa qb (embed z) hqa hqau hqb hqbu
  · rw [hqae,linearScore_embed_det,linearScore_embed_det,hea]
    exact_mod_cast hlo
  · rw [hqbe,linearScore_embed_det,linearScore_embed_det]
    rw [det_neg_left] at heb hhi
    exact_mod_cast (show det u z ≤ det u b by omega)

theorem residue_meets_window_of_support_bounds (T : Finset Lattice) (u : Lattice)
    (hu : u ≠ 0) (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (hfaces : LongFaces {u,-u} (T : Set Lattice))
    (z : Lattice) (hlo : lowerSupport T u ≤ det u z)
    (hhi : lowerSupport T (-u) ≤ det (-u) z) :
    ∃ n : ℤ, z+n•u ∈ T := by
  obtain ⟨q,hq,hqu,hqz⟩ := segment_at_supported_level T u hT hfaces z hlo hhi
  obtain ⟨t,ht⟩ := exists_real_parallel u hu (embed z) q hqz.symm
  let n : ℤ := -⌊t⌋
  have hs : 0 ≤ t-(⌊t⌋:ℤ) := by linarith [Int.floor_le t]
  have hs1 : t-(⌊t⌋:ℤ) ≤ 1 := by linarith [Int.lt_floor_add_one t]
  have hh := (windowHull_convex T).add_smul_mem hq hqu (t:=t-(⌊t⌋:ℤ)) ⟨hs,hs1⟩
  refine ⟨n,(hconv (z+n•u)).mp ?_⟩
  have he : embed (z+n•u) = q+(t-(⌊t⌋:ℤ))•embed u := by
    rw [embed_add,embed_zsmul,ht]
    dsimp [n]
    simp only [Int.fract,Int.cast_neg,neg_smul,sub_eq_add_neg,add_smul]
    abel
  rw [he]
  exact hh

/-- An actual common point makes the two transverse intervals overlap.
This supplies the lattice-line meeting step in product-factor induction. -/
theorem residue_meets_union_of_support_bounds (T S : Finset Lattice) (u : Lattice)
    (hu : u ≠ 0) (hT : IsLatticeConvex T) (hS : IsLatticeConvex S)
    (hTf : LongFaces {u,-u} (T : Set Lattice))
    (hSf : LongFaces {u,-u} (S : Set Lattice))
    (hmeet : ∃ w, w ∈ T ∧ w ∈ S)
    (z : Lattice)
    (hlo : min (lowerSupport T u) (lowerSupport S u) ≤ det u z)
    (hhi : min (lowerSupport T (-u)) (lowerSupport S (-u)) ≤ det (-u) z) :
    ∃ n : ℤ, z+n•u ∈ T ∪ S := by
  obtain ⟨w,hwT,hwS⟩ := hmeet
  have hwTlo := lowerSupport_le hwT u
  have hwThi := lowerSupport_le hwT (-u)
  have hwSlo := lowerSupport_le hwS u
  have hwShi := lowerSupport_le hwS (-u)
  have hcase : (lowerSupport T u ≤ det u z ∧ lowerSupport T (-u) ≤ det (-u) z) ∨
      (lowerSupport S u ≤ det u z ∧ lowerSupport S (-u) ≤ det (-u) z) := by
    rw [det_neg_left] at hwThi hwShi hhi ⊢
    omega
  rcases hcase with ⟨hl,hh⟩ | ⟨hl,hh⟩
  · obtain ⟨n,hn⟩ := residue_meets_window_of_support_bounds T u hu ⟨w,hwT⟩ hT hTf z hl hh
    exact ⟨n,Finset.mem_union_left S hn⟩
  · obtain ⟨n,hn⟩ := residue_meets_window_of_support_bounds S u hu ⟨w,hwS⟩ hS hSf z hl hh
    exact ⟨n,Finset.mem_union_right T hn⟩

end
end NivatTrial.ColleEnvelopeFiberCoding
