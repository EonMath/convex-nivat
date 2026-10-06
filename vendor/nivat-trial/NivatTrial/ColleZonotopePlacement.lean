import NivatTrial.ColleHalfStripEnvelope
import NivatTrial.ColleZonotopeEnvelope
import NivatTrial.BalancedWindows
import NivatTrial.IncrementSupport

/-! Long faces permit the placement of the actual subset-sum window.
The proof erodes the lattice-convex window by one segment at a time.
Faces transverse to that segment retain their original lengths. -/

namespace NivatTrial.ColleZonotopePlacement

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.ColleGenerating NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleLongFaces NivatTrial.ColleHalfStripEnvelope
open NivatTrial.ColleZonotopeEnvelope NivatTrial.BalancedWindows
open NivatTrial.IncrementSupport
open scoped Classical
noncomputable section

abbrev Plane := ℝ × ℝ

/-- A support inequality at the lattice sites holds on their real hull. -/
theorem support_le_on_hull (T : Finset Lattice) (d w : Lattice)
    (hmin : ∀ z ∈ T, det d w ≤ det d z) :
    ∀ q ∈ windowHull T, (det d w : ℝ) ≤ linearScore (embed d) q := by
  have hsub : embed '' (T : Set Lattice) ⊆
      {q : Plane | (det d w : ℝ) ≤ linearScore (embed d) q} := by
    rintro q ⟨z, hz, rfl⟩
    rw [Set.mem_ofPred_eq, linearScore_embed_det]
    exact_mod_cast hmin z hz
  exact convexHull_min hsub
    (convex_halfSpace_ge (linearScore (embed d)).isLinear (det d w : ℝ))

/-- The two u-parallel extreme faces interpolate to a segment of length u
at the transverse level of every point of T. -/
theorem segment_in_windowHull (T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hfaces : LongFaces {u,-u} (T : Set Lattice))
    (z : Lattice) (hz : z ∈ T) :
    ∃ q : Plane, q ∈ windowHull T ∧ q + embed u ∈ windowHull T ∧
      linearScore (embed u) q = linearScore (embed u) (embed z) := by
  obtain ⟨a, ha, hea⟩ := lowerSupport_attained T hT u
  obtain ⟨a', ha', hau, hea'⟩ := hfaces u (by simp) a ha (fun w hw =>
    by rw [hea]; exact lowerSupport_le hw u)
  obtain ⟨b, hb, heb⟩ := lowerSupport_attained T hT (-u)
  obtain ⟨b', hb', hbu, heb'⟩ := hfaces (-u) (by simp) b hb (fun w hw =>
    by rw [heb]; exact lowerSupport_le hw (-u))
  have haeq : det u a' = lowerSupport T u := hea'.trans hea
  have hbeq : det (-u) (b'-u) = lowerSupport T (-u) := by
    rw [det_sub_right, det_neg_left u u, det_self, neg_zero, sub_zero]
    exact heb'.trans heb
  apply segment_at_height (windowHull_convex T) u (embed a') (embed (b'-u))
    (embed z) (mem_windowHull_of_mem T ha')
  · simpa only [embed_add] using mem_windowHull_of_mem T hau
  · exact mem_windowHull_of_mem T (by simpa [sub_eq_add_neg] using hbu)
  · simpa only [← embed_add, sub_add_cancel] using mem_windowHull_of_mem T hb'
  · rw [linearScore_embed_det, linearScore_embed_det, haeq]
    exact_mod_cast lowerSupport_le hz u
  · have hz' := lowerSupport_le hz (-u)
    rw [det_neg_left] at hbeq hz'
    rw [linearScore_embed_det, linearScore_embed_det]
    exact_mod_cast (show det u z ≤ det u (b'-u) by omega)

/-- A positive inward step from a transverse supporting face stays in T. -/
theorem support_inward_step (T : Finset Lattice) (u d w : Lattice)
    (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (hfaces : LongFaces {u,-u} (T : Set Lattice))
    (hw : w ∈ T) (hmin : ∀ z ∈ T, det d w ≤ det d z)
    (hdu : 0 < det d u) : w+u ∈ T := by
  obtain ⟨q, hq, hqu, hqw⟩ := segment_in_windowHull T u hT hfaces w hw
  have hu0 : u ≠ 0 := by
    intro hu0
    simp [hu0] at hdu
  obtain ⟨s, hs⟩ := exists_real_parallel u hu0 q (embed w) hqw
  have hminq := support_le_on_hull T d w hmin q hq
  have hdu' : (0 : ℝ) < (det d u : ℝ) := by exact_mod_cast hdu
  have hs0 : 0 ≤ s := by
    rw [hs, map_add, map_smul, smul_eq_mul, linearScore_embed_det,
      linearScore_embed_det] at hminq
    nlinarith
  have hfar : embed w + (s+1) • embed u ∈ windowHull T := by
    convert hqu using 1
    rw [hs]
    module
  have hspos : 0 < s+1 := by linarith
  have hh := (windowHull_convex T).add_smul_mem (mem_windowHull_of_mem T hw) hfar
    (t := 1/(s+1)) ⟨by positivity, (div_le_one hspos).mpr (by linarith)⟩
  apply (hconv (w+u)).mp
  rw [embed_add]
  simpa only [smul_smul, one_div_mul_cancel (ne_of_gt hspos), one_smul] using hh

def stepErosion (T : Finset Lattice) (u : Lattice) : Finset Lattice :=
  T.filter (fun z => z+u ∈ T)

@[simp] theorem mem_stepErosion (T : Finset Lattice) (u z : Lattice) :
    z ∈ stepErosion T u ↔ z ∈ T ∧ z+u ∈ T := Finset.mem_filter

theorem stepErosion_nonempty (T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hfaces : LongFaces {u,-u} (T : Set Lattice)) :
    (stepErosion T u).Nonempty := by
  obtain ⟨a, ha, hea⟩ := lowerSupport_attained T hT u
  obtain ⟨w, hw, hwu, _⟩ := hfaces u (by simp) a ha (fun z hz =>
    by rw [hea]; exact lowerSupport_le hz u)
  exact ⟨w, (mem_stepErosion T u w).mpr ⟨hw, hwu⟩⟩

theorem stepErosion_latticeConvex (T : Finset Lattice) (u : Lattice)
    (hconv : IsLatticeConvex T) : IsLatticeConvex (stepErosion T u) := by
  unfold stepErosion
  convert latticeConvex_filter hconv (fun z => z+u ∈ T)
    ((fun x : Plane => embed u+x) ⁻¹' windowHull T)
    ((windowHull_convex T).translate_preimage_right (embed u)) ?_ using 1
  · ext z
    simp only [Finset.mem_filter]
  · intro z
    change z+u ∈ T ↔ embed u+embed z ∈ windowHull T
    rw [← embed_add, add_comm u z]
    exact (hconv (z+u)).symm

/-- Erosion preserves every long face whose direction is transverse to u.
For positive determinant it is the old face; for negative determinant it
is the old face translated by -u. -/
theorem stepErosion_longFaces (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (huFaces : LongFaces {u,-u} (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hind : ∀ d ∈ D, det d u ≠ 0) :
    LongFaces D (stepErosion T u : Set Lattice) := by
  intro d hd z hz hmin
  obtain ⟨a, ha, hea⟩ := lowerSupport_attained T hT d
  obtain ⟨w, hw, hwd, hwe⟩ := hfaces d hd a ha (fun v hv =>
    by rw [hea]; exact lowerSupport_le hv d)
  change w ∈ T at hw
  change w+d ∈ T at hwd
  have hweq : det d w = lowerSupport T d := hwe.trans hea
  have hwdeq : det d (w+d) = lowerSupport T d := by simp [hweq]
  have hwmin : ∀ v ∈ T, det d w ≤ det d v := by
    intro v hv
    rw [hweq]
    exact lowerSupport_le hv d
  have hwdmin : ∀ v ∈ T, det d (w+d) ≤ det d v := by
    intro v hv
    rw [hwdeq]
    exact lowerSupport_le hv d
  rcases lt_or_gt_of_ne (hind d hd) with hdu | hdu
  · have hnegFaces : LongFaces {-u,-(-u)} (T : Set Lattice) := by
      simpa [Finset.pair_comm] using huFaces
    have hneg : 0 < det d (-u) := by rw [det_neg_right]; omega
    have hwu : w-u ∈ T := by
      simpa [sub_eq_add_neg] using support_inward_step T (-u) d w hT hconv
        hnegFaces hw hwmin hneg
    have hwdu : w+d-u ∈ T := by
      simpa [sub_eq_add_neg] using support_inward_step T (-u) d (w+d) hT hconv
        hnegFaces hwd hwdmin hneg
    have hwe : w-u ∈ stepErosion T u := by simp [hwu, hw]
    have hwde : (w-u)+d ∈ stepErosion T u := by
      apply (mem_stepErosion T u _).mpr
      constructor
      · convert hwdu using 1
        abel
      · convert hwd using 1
        abel
    refine ⟨w-u, hwe, hwde, ?_⟩
    apply le_antisymm
    · have hzt := (mem_stepErosion T u z).mp hz
      have hh := lowerSupport_le hzt.2 d
      rw [det_sub_right, hweq]
      rw [det_add_right] at hh
      omega
    · exact hmin (w-u) hwe
  · have hwu := support_inward_step T u d w hT hconv huFaces hw hwmin hdu
    have hwdu := support_inward_step T u d (w+d) hT hconv huFaces hwd hwdmin hdu
    have hwe : w ∈ stepErosion T u := by simp [hw, hwu]
    have hwde : w+d ∈ stepErosion T u := by simp [hwd, hwdu]
    refine ⟨w, hwe, hwde, ?_⟩
    apply le_antisymm
    · exact hwmin z ((mem_stepErosion T u z).mp hz).1
    · exact hmin w hwe

/-- Repeated erosion places all actual subset sums at one integer anchor. -/
theorem exists_offsets_placement (hs : List Lattice) (T : Finset Lattice)
    (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (hfaces : ∀ u ∈ hs, LongFaces {u,-u} (T : Set Lattice))
    (hind : hs.Pairwise (fun u v => det u v ≠ 0)) :
    ∃ a : Lattice, ∀ e ∈ offsets hs, a+e ∈ T := by
  induction hs generalizing T with
  | nil =>
    obtain ⟨a, ha⟩ := hT
    exact ⟨a, by simpa [offsets] using ha⟩
  | cons u hs ih =>
    have huFaces := hfaces u (by simp)
    have hE := stepErosion_nonempty T u hT huFaces
    have hEconv := stepErosion_latticeConvex T u hconv
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hind
    have hEfaces : ∀ v ∈ hs, LongFaces {v,-v} (stepErosion T u : Set Lattice) := by
      intro v hv
      apply stepErosion_longFaces {v,-v} T u hT hconv huFaces
        (hfaces v (by simp [hv]))
      intro d hd
      have hvu : det v u ≠ 0 := by
        rw [det_swap]
        exact neg_ne_zero.mpr (hhead v hv)
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hvu
      · have he : d = -v := Finset.mem_singleton.mp hd
        rw [he, det_neg_left]
        exact neg_ne_zero.mpr hvu
    obtain ⟨a, ha⟩ := ih (stepErosion T u) hE hEconv hEfaces htail
    refine ⟨a, ?_⟩
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact ((mem_stepErosion T u (a+e)).mp (ha e he)).1
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      have hh := ((mem_stepErosion T u (a+f)).mp (ha f hf)).2
      convert hh using 1
      abel

/-- Indexed form for the annihilator's actual offset window. -/
theorem exists_indexed_offsets_placement {n : ℕ} (v : Fin n → Lattice)
    (T : Finset Lattice) (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (hfaces : LongFaces (signedDirections v) (T : Set Lattice))
    (hind : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0) :
    ∃ a : Lattice, ∀ e ∈ offsets (Finset.univ.toList.map v), a+e ∈ T := by
  apply exists_offsets_placement _ T hT hconv
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    intro d hd
    apply hfaces d
    rw [mem_signedDirections]
    refine ⟨i, ?_⟩
    rcases Finset.mem_insert.mp hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr (Finset.mem_singleton.mp hd)
  · rw [List.pairwise_map]
    exact (Finset.nodup_toList (Finset.univ : Finset (Fin n))).pairwise_of_forall_ne
      (fun i _ j _ hij => hind i j hij)

end
end NivatTrial.ColleZonotopePlacement
