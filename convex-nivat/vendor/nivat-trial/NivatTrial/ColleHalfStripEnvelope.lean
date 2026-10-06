import NivatTrial.ColleLongFaces

/-! A genuine discrete half-strip is an envelope when its two supporting
faces parallel to the translation contain a complete translation segment.
The direction need not be primitive: a segment of length u supplies all
residue classes modulo translation by u. -/

namespace NivatTrial.ColleHalfStripEnvelope

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.RegionGeometry
open NivatTrial.LatticePolygon NivatTrial.ColleGenerating
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleFiniteEnvelope NivatTrial.ColleLongFaces
open scoped Classical
noncomputable section

abbrev Plane := ℝ × ℝ

def realEnvelope (D : Finset Lattice) (b : Lattice → ℤ) : Set Plane :=
  {x | ∀ d ∈ D, (b d : ℝ) ≤ linearScore (embed d) x}

theorem realEnvelope_convex (D : Finset Lattice) (b : Lattice → ℤ) :
    Convex ℝ (realEnvelope D b) := by
  intro x hx y hy a c ha hc hac d hd
  have hx' := hx d hd
  have hy' := hy d hd
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    (b d : ℝ) = a * (b d : ℝ) + c * (b d : ℝ) := by
      rw [← add_mul, hac, one_mul]
    _ ≤ a * linearScore (embed d) x + c * linearScore (embed d) y :=
      add_le_add (mul_le_mul_of_nonneg_left hx' ha)
        (mul_le_mul_of_nonneg_left hy' hc)

theorem embed_mem_realEnvelope (D : Finset Lattice) (b : Lattice → ℤ)
    (z : Lattice) : embed z ∈ realEnvelope D b ↔ z ∈ envelope D b := by
  simp only [realEnvelope, Set.mem_ofPred_eq, mem_envelope,
    linearScore_embed_det, Int.cast_le]

/-- Equal transverse coordinates lie on the same real line parallel to u. -/
theorem exists_real_parallel (u : Lattice) (hu : u ≠ 0) (x y : Plane)
    (h : linearScore (embed u) x = linearScore (embed u) y) :
    ∃ t : ℝ, x = y + t • embed u := by
  change (u.1 : ℝ) * x.2 - (u.2 : ℝ) * x.1 =
    (u.1 : ℝ) * y.2 - (u.2 : ℝ) * y.1 at h
  by_cases hx : u.1 = 0
  · have hy : u.2 ≠ 0 := by
      intro hy
      exact hu (Prod.ext hx hy)
    have hy' : (u.2 : ℝ) ≠ 0 := by exact_mod_cast hy
    have he : x.1 = y.1 := by
      simp only [hx, Int.cast_zero, zero_mul, zero_sub] at h
      exact mul_left_cancel₀ hy' (neg_injective h)
    refine ⟨(x.2-y.2)/(u.2:ℝ), ?_⟩
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, embed]
    · simp [hx, he]
    · field_simp
      ring
  · have hx' : (u.1 : ℝ) ≠ 0 := by exact_mod_cast hx
    refine ⟨(x.1-y.1)/(u.1:ℝ), ?_⟩
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, embed]
    · field_simp
      ring
    · apply (mul_left_cancel₀ hx')
      field_simp
      nlinarith

/-- Interpolating parallel translation segments preserves their length. -/
theorem segment_at_height {C : Set Plane} (hC : Convex ℝ C)
    (u : Lattice) (a b z : Plane)
    (ha : a ∈ C) (hau : a + embed u ∈ C)
    (hb : b ∈ C) (hbu : b + embed u ∈ C)
    (haz : linearScore (embed u) a ≤ linearScore (embed u) z)
    (hzb : linearScore (embed u) z ≤ linearScore (embed u) b) :
    ∃ q : Plane, q ∈ C ∧ q + embed u ∈ C ∧
      linearScore (embed u) q = linearScore (embed u) z := by
  let f := linearScore (embed u)
  by_cases he : f a = f b
  · exact ⟨a, ha, hau, by dsimp [f] at he; linarith⟩
  have hab : f a < f b := lt_of_le_of_ne (haz.trans hzb) he
  let s : ℝ := (f z-f a)/(f b-f a)
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr haz) (sub_pos.mpr hab).le
  have hs1 : s ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith)
  let q := (1-s) • a + s • b
  have hq : q ∈ C := hC ha hb (by linarith) hs (by ring)
  have hqu : q + embed u ∈ C := by
    have hh := hC hau hbu (show 0 ≤ 1-s by linarith) hs (by ring : 1-s+s=1)
    convert hh using 1
    simp only [q, smul_add, sub_smul, one_smul]
    module
  refine ⟨q, hq, hqu, ?_⟩
  change f q = f z
  simp only [q, map_add, map_smul, smul_eq_mul]
  dsimp [s]
  field_simp
  ring

/-- The half-strip always satisfies every support inequality that faces
forwards or is parallel to the translation. -/
theorem halfStrip_subset_forward_support (D T : Finset Lattice) (u : Lattice) :
    halfStrip T u ⊆ {z | ∀ d ∈ D, 0 ≤ det d u → lowerSupport T d ≤ det d z} := by
  rintro z ⟨b, hb, n, rfl⟩ d hd hdu
  rw [det_add_right, det_nsmul_right]
  exact (lowerSupport_le hb d).trans
    (le_add_of_nonneg_right (mul_nonneg (by positivity) hdu))

/-- The long faces at ±u give a full real translation segment at every
transverse level retained by the forward support inequalities. -/
theorem exists_segment_in_realEnvelope (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hfaces : LongFaces D (T : Set Lattice))
    (hu : u ∈ D) (hnu : -u ∈ D) (z : Lattice)
    (hz : ∀ d ∈ D, 0 ≤ det d u → lowerSupport T d ≤ det d z) :
    ∃ q : Plane, q ∈ realEnvelope D (lowerSupport T) ∧
      q + embed u ∈ realEnvelope D (lowerSupport T) ∧
      linearScore (embed u) q = linearScore (embed u) (embed z) := by
  obtain ⟨a, ha, hea⟩ := lowerSupport_attained T hT u
  obtain ⟨a', ha', hau, hea'⟩ := hfaces u hu a ha (fun w hw =>
    by rw [hea]; exact lowerSupport_le hw u)
  obtain ⟨b, hb, heb⟩ := lowerSupport_attained T hT (-u)
  obtain ⟨b', hb', hbu, heb'⟩ := hfaces (-u) hnu b hb (fun w hw =>
    by rw [heb]; exact lowerSupport_le hw (-u))
  have hin (w : Lattice) (hw : w ∈ T) :
      embed w ∈ realEnvelope D (lowerSupport T) :=
    (embed_mem_realEnvelope D _ w).mpr (subset_envelope D T hw)
  have haeq : det u a' = lowerSupport T u := hea'.trans hea
  have hbeq : det (-u) (b'-u) = lowerSupport T (-u) := by
    rw [det_sub_right, det_neg_left u u, det_self, neg_zero, sub_zero]
    exact heb'.trans heb
  apply segment_at_height (realEnvelope_convex D _) u (embed a') (embed (b'-u))
    (embed z) (hin _ ha')
  · simpa only [embed_add] using hin _ hau
  · exact hin _ (by simpa [sub_eq_add_neg] using hbu)
  · simpa only [← embed_add, sub_add_cancel] using hin _ hb'
  · rw [linearScore_embed_det, linearScore_embed_det, haeq]
    exact_mod_cast hz u hu (by simp)
  · have hz' := hz (-u) hnu (by rw [det_neg_left, det_self]; omega)
    rw [det_neg_left] at hbeq hz'
    rw [linearScore_embed_det, linearScore_embed_det]
    exact_mod_cast (show det u z ≤ det u (b'-u) by omega)

/-- Dropping precisely the inequalities which face backwards gives the
actual union of the integer translates; no primitive-direction premise is
needed. -/
theorem halfStrip_eq_forward_support (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D) :
    halfStrip T u =
      {z | ∀ d ∈ D, 0 ≤ det d u → lowerSupport T d ≤ det d z} := by
  apply Set.Subset.antisymm (halfStrip_subset_forward_support D T u)
  intro z hz
  obtain ⟨q, hq, hqu, hqz⟩ := exists_segment_in_realEnvelope D T u hT hfaces hu hnu z hz
  obtain ⟨t, ht⟩ := exists_real_parallel u hu0 (embed z) q hqz.symm
  have hmem (w : Lattice) (hw : embed w ∈ realEnvelope D (lowerSupport T)) : w ∈ T := by
    change w ∈ (T : Set Lattice)
    rw [hclosed.eq_finite_envelope hT]
    exact (embed_mem_realEnvelope D _ w).mp hw
  by_cases htn : 0 ≤ t
  · let n : ℕ := (⌊t⌋ : ℤ).toNat
    have hn : (n : ℝ) = (⌊t⌋ : ℤ) := by
      dsimp [n]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.floor_nonneg.mpr htn)]
    have hs : 0 ≤ t-(n:ℝ) := by rw [hn]; linarith [Int.floor_le t]
    have hs1 : t-(n:ℝ) ≤ 1 := by rw [hn]; linarith [Int.lt_floor_add_one t]
    have hh := (realEnvelope_convex D (lowerSupport T)).add_smul_mem hq hqu
      (t := t-(n:ℝ)) ⟨hs, hs1⟩
    have he : embed (z-n•u) = q+(t-(n:ℝ))•embed u := by
      rw [embed_sub, embed_nsmul, ht]
      module
    have hb : z-n•u ∈ T := hmem _ (by rw [he]; exact hh)
    exact ⟨z-n•u, hb, n, by abel⟩
  · have hzmem : embed z ∈ realEnvelope D (lowerSupport T) := by
      intro d hd
      by_cases hdu : 0 ≤ det d u
      · rw [linearScore_embed_det]
        exact_mod_cast hz d hd hdu
      · have hdun : (det d u : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (lt_of_not_ge hdu)
        have hq' := hq d hd
        rw [ht, map_add, map_smul, smul_eq_mul, linearScore_embed_det]
        exact hq'.trans (le_add_of_nonneg_right (mul_nonneg_of_nonpos_of_nonpos
          (le_of_lt (lt_of_not_ge htn)) hdun))
    exact base_subset_halfStrip T u (hmem z hzmem)

/-- The half-strip is closed under the original finite-direction envelope
operator, although the backwards support levels have disappeared. -/
theorem halfStrip_isEnvelope (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D) :
    IsEnvelope D (halfStrip T u) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz
  rw [halfStrip_eq_forward_support D T u hT hclosed hfaces hu0 hu hnu]
  intro d hd hdu
  exact hz d hd (lowerSupport T d) (fun w hw =>
    halfStrip_subset_forward_support D T u hw d hd hdu)

theorem halfStrip_latticeConvex (D T : Finset Lattice) (u : Lattice)
    (hT : T.Nonempty) (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu0 : u ≠ 0) (hu : u ∈ D) (hnu : -u ∈ D) :
    LatticeConvexRegion (halfStrip T u) :=
  (halfStrip_isEnvelope D T u hT hclosed hfaces hu0 hu hnu).latticeConvex

theorem halfStrip_forward (T : Finset Lattice) (u : Lattice) :
    ForwardInvariant (halfStrip T u) u := by
  rintro z ⟨b, hb, n, rfl⟩
  refine ⟨b, hb, n+1, ?_⟩
  rw [add_nsmul, one_nsmul]
  abel

/-- Every exposed face of the half-strip contains an old long face of T. -/
theorem halfStrip_longFaces (D T : Finset Lattice) (u : Lattice)
    (hfaces : LongFaces D (T : Set Lattice)) : LongFaces D (halfStrip T u) := by
  intro d hd z hz hmin
  have hdu : 0 ≤ det d u := by
    have hh := hmin (z+u) (halfStrip_forward T u z hz)
    rw [det_add_right] at hh
    omega
  obtain ⟨b, hb, n, rfl⟩ := hz
  have hbeq : det d b = det d (b+n•u) := by
    have hh := hmin b (base_subset_halfStrip T u hb)
    rw [det_add_right, det_nsmul_right] at hh ⊢
    have hm : 0 ≤ (n:ℤ) * det d u := mul_nonneg (by positivity) hdu
    omega
  obtain ⟨w, hw, hwd, hwe⟩ := hfaces d hd b hb (by
    intro v hv
    rw [hbeq]
    exact hmin v (base_subset_halfStrip T u hv))
  exact ⟨w, base_subset_halfStrip T u hw, base_subset_halfStrip T u hwd, hwe.trans hbeq⟩

end
end NivatTrial.ColleHalfStripEnvelope
