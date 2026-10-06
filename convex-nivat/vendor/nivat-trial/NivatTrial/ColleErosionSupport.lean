import NivatTrial.ColleZonotopePlacement

/-! Exact support levels after removing one directional segment.  This is
the geometric input for induction on the factors of an annihilator. -/

namespace NivatTrial.ColleErosionSupport

open NivatTrial.Geometry NivatTrial.LatticePolygon
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleLongFaces
open NivatTrial.ColleZonotopePlacement
open scoped Classical
noncomputable section

theorem lowerSupport_stepErosion (T : Finset Lattice) (u d : Lattice)
    (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (hfaces : LongFaces {u,-u} (T : Set Lattice))
    (hdu : det d u ≠ 0) :
    lowerSupport (stepErosion T u) d = lowerSupport T d + max 0 (-det d u) := by
  have hE := stepErosion_nonempty T u hT hfaces
  obtain ⟨w, hw, hwe⟩ := lowerSupport_attained T hT d
  have hwmin : ∀ z ∈ T, det d w ≤ det d z := by
    intro z hz
    rw [hwe]
    exact lowerSupport_le hz d
  rcases lt_or_gt_of_ne hdu with hneg | hpos
  · have hnfaces : LongFaces {-u,-(-u)} (T : Set Lattice) := by
      simpa [Finset.pair_comm] using hfaces
    have hwu : w-u ∈ T := by
      simpa [sub_eq_add_neg] using support_inward_step T (-u) d w hT hconv
        hnfaces hw hwmin (by rw [det_neg_right]; omega)
    have hwE : w-u ∈ stepErosion T u := by simp [hwu, hw]
    have hupper := lowerSupport_le hwE d
    obtain ⟨z, hz, hze⟩ := lowerSupport_attained (stepErosion T u) hE d
    have hlower := lowerSupport_le ((mem_stepErosion T u z).mp hz).2 d
    rw [det_sub_right, hwe] at hupper
    rw [det_add_right, hze] at hlower
    rw [max_eq_right (by omega : 0 ≤ -det d u)]
    omega
  · have hwu := support_inward_step T u d w hT hconv hfaces hw hwmin hpos
    have hwE : w ∈ stepErosion T u := by simp [hw, hwu]
    have hupper := lowerSupport_le hwE d
    obtain ⟨z, hz, hze⟩ := lowerSupport_attained (stepErosion T u) hE d
    have hlower := lowerSupport_le ((mem_stepErosion T u z).mp hz).1 d
    rw [hwe] at hupper
    rw [hze] at hlower
    rw [max_eq_left (by omega : -det d u ≤ 0), add_zero]
    omega

/-- The remaining faces survive together; the direction being removed is
the only pair for which no long-face claim is made. -/
theorem stepErosion_remaining_faces (T : Finset Lattice) (u : Lattice)
    (hs : List Lattice) (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (hfaces : ∀ v ∈ u::hs, LongFaces {v,-v} (T : Set Lattice))
    (hind : ∀ v ∈ hs, det u v ≠ 0) :
    ∀ v ∈ hs, LongFaces {v,-v} (stepErosion T u : Set Lattice) := by
  intro v hv
  apply stepErosion_longFaces {v,-v} T u hT hconv (hfaces u (by simp))
    (hfaces v (by simp [hv]))
  intro d hd
  have hvu : det v u ≠ 0 := by
    rw [det_swap]
    exact neg_ne_zero.mpr (hind v hv)
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact hvu
  · rw [Finset.mem_singleton.mp hd, det_neg_left]
    exact neg_ne_zero.mpr hvu

end
end NivatTrial.ColleErosionSupport
