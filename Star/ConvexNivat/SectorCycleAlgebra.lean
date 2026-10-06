import ConvexNivat.SectorDefinitions

namespace ConvexNivat
noncomputable section

def sectorBaseIndex {p : ℕ} (star : StarData p) : Fin star.m :=
  ⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos 1) star.two_le⟩

def sectorBaseDirection {p : ℕ} (star : StarData p) : Lattice :=
  (star.component (sectorBaseIndex star)).direction

def sectorComplement {p : ℕ} (star : StarData p) : Lattice :=
  Classical.choose (primitive_height_surjective (sectorBaseDirection star)
    (star.component (sectorBaseIndex star)).primitive 1)

def sectorSlice {p : ℕ} (star : StarData p) (t : ℝ) : RealPlane :=
  embed (sectorComplement star) + t • embed (sectorBaseDirection star)

abbrev SectorRest {p : ℕ} (star : StarData p) :=
  {j : Fin star.m // j ≠ sectorBaseIndex star}

def sectorSliceA {p : ℕ} (star : StarData p) (j : Fin star.m) : ℝ :=
  (det (star.component j).direction (sectorComplement star) : ℝ)

def sectorSliceB {p : ℕ} (star : StarData p) (j : Fin star.m) : ℝ :=
  (det (star.component j).direction (sectorBaseDirection star) : ℝ)

def sectorBreakpoint {p : ℕ} (star : StarData p) (j : SectorRest star) : ℝ :=
  -sectorSliceA star j.val / sectorSliceB star j.val

theorem sector_height_algebra :
    (∀ (v : Lattice) (x y : RealPlane),
      realHeight v (x + y) = realHeight v x + realHeight v y) ∧
    (∀ (v : Lattice) (c : ℝ) (x : RealPlane),
      realHeight v (c • x) = c * realHeight v x) ∧
    (∀ v w : Lattice, realHeight v (embed w) = (det v w : ℝ)) ∧
    (∀ v₀ u : Lattice, det v₀ u = 1 → ∀ x : RealPlane,
      x = (-realHeight u x) • embed v₀ + realHeight v₀ x • embed u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros v x y
    simp only [realHeight, Prod.fst_add, Prod.snd_add]
    ring
  · intros v c x
    change (v.1 : ℝ) * (c * x.2) - (v.2 : ℝ) * (c * x.1) =
      c * ((v.1 : ℝ) * x.2 - (v.2 : ℝ) * x.1)
    ring
  · intros v w
    simp [realHeight, embed, det]
  · intros v u h x
    have hc : (v.1 : ℝ) * (u.2 : ℝ) - (v.2 : ℝ) * (u.1 : ℝ) = 1 := by
      exact_mod_cast h
    apply Prod.ext <;> simp [realHeight, embed]
    · nlinarith [congrArg (fun q : ℝ => q * x.1) hc]
    · nlinarith [congrArg (fun q : ℝ => q * x.2) hc]

theorem sector_slice_complement {p : ℕ} (star : StarData p) :
    det (sectorBaseDirection star) (sectorComplement star) = 1 ∧
      ∀ t : ℝ, realHeight (sectorBaseDirection star) (sectorSlice star t) = 1 := by
  have h : det (sectorBaseDirection star) (sectorComplement star) = 1 :=
    Classical.choose_spec (primitive_height_surjective (sectorBaseDirection star)
      (star.component (sectorBaseIndex star)).primitive 1)
  refine ⟨h, ?_⟩
  intro t
  rw [sectorSlice, sector_height_algebra.1, sector_height_algebra.2.1,
    sector_height_algebra.2.2.1, sector_height_algebra.2.2.1, h]
  simp [det, mul_comm]

theorem sector_slice_factors {p : ℕ} (star : StarData p) :
    ∀ j : SectorRest star,
      sectorSliceB star j.val ≠ 0 ∧
      (∀ t : ℝ,
        realHeight (star.component j.val).direction (sectorSlice star t) =
          sectorSliceA star j.val + sectorSliceB star j.val * t ∧
        realHeight (star.component j.val).direction (sectorSlice star t) =
          sectorSliceB star j.val * (t - sectorBreakpoint star j)) ∧
      sectorSlice star (sectorBreakpoint star j) =
        (1 / (det (sectorBaseDirection star) (star.component j.val).direction : ℝ)) •
          embed (star.component j.val).direction := by
  intro j
  have hB : sectorSliceB star j.val ≠ 0 := by
    have h := star.pairwise_nonparallel j.val (sectorBaseIndex star) j.property
    change det (star.component j.val).direction (sectorBaseDirection star) ≠ 0 at h
    unfold sectorSliceB
    exact_mod_cast h
  have hdet := (sector_slice_complement star).1
  refine ⟨hB, ?_, ?_⟩
  · intro t
    have ha : realHeight (star.component j.val).direction (sectorSlice star t) =
        sectorSliceA star j.val + sectorSliceB star j.val * t := by
      rw [sectorSlice, sector_height_algebra.1, sector_height_algebra.2.1,
        sector_height_algebra.2.2.1, sector_height_algebra.2.2.1]
      simp only [sectorSliceA, sectorSliceB]
      ring
    refine ⟨ha, ?_⟩
    rw [ha, sectorBreakpoint]
    field_simp
    <;> ring
  · have hC : (det (sectorBaseDirection star) (star.component j.val).direction : ℝ) ≠ 0 := by
      have h := star.pairwise_nonparallel (sectorBaseIndex star) j.val (Ne.symm j.property)
      exact_mod_cast h
    have hc : ((sectorBaseDirection star).1 : ℝ) * ((sectorComplement star).2 : ℝ) -
        ((sectorBaseDirection star).2 : ℝ) * ((sectorComplement star).1 : ℝ) = 1 := by
      exact_mod_cast hdet
    have hCB : (det (sectorBaseDirection star) (star.component j.val).direction : ℝ) =
        -sectorSliceB star j.val := by
      simp [sectorSliceB, det]
      ring
    rw [hCB]
    apply Prod.ext
    · change ((sectorComplement star).1 : ℝ) +
        (-sectorSliceA star j.val / sectorSliceB star j.val) *
          ((sectorBaseDirection star).1 : ℝ) =
        (1 / -sectorSliceB star j.val) * ((star.component j.val).direction.1 : ℝ)
      field_simp [hB]
      simp only [sectorSliceA, sectorSliceB, det, Int.cast_sub, Int.cast_mul]
      nlinarith [congrArg (fun q : ℝ => q * (star.component j.val).direction.1) hc]
    · change ((sectorComplement star).2 : ℝ) +
        (-sectorSliceA star j.val / sectorSliceB star j.val) *
          ((sectorBaseDirection star).2 : ℝ) =
        (1 / -sectorSliceB star j.val) * ((star.component j.val).direction.2 : ℝ)
      field_simp [hB]
      simp only [sectorSliceA, sectorSliceB, det, Int.cast_sub, Int.cast_mul]
      nlinarith [congrArg (fun q : ℝ => q * (star.component j.val).direction.2) hc]

theorem sector_breakpoint_injective {p : ℕ} (star : StarData p) :
    (∀ j k : SectorRest star,
      sectorSliceA star j.val * sectorSliceB star k.val -
          sectorSliceA star k.val * sectorSliceB star j.val =
        -(det (star.component j.val).direction (star.component k.val).direction : ℝ)) ∧
      Function.Injective (sectorBreakpoint star) := by
  have hid (j k : SectorRest star) :
      sectorSliceA star j.val * sectorSliceB star k.val -
          sectorSliceA star k.val * sectorSliceB star j.val =
        -(det (star.component j.val).direction (star.component k.val).direction : ℝ) := by
    have hdet := (sector_slice_complement star).1
    have hc : ((sectorBaseDirection star).1 : ℝ) * ((sectorComplement star).2 : ℝ) -
        ((sectorBaseDirection star).2 : ℝ) * ((sectorComplement star).1 : ℝ) = 1 := by
      exact_mod_cast hdet
    simp [sectorSliceA, sectorSliceB, det]
    nlinarith [congrArg (fun q : ℝ => q *
      ((star.component j.val).direction.1 * (star.component k.val).direction.2 -
        (star.component j.val).direction.2 * (star.component k.val).direction.1)) hc]
  refine ⟨hid, ?_⟩
  intro j k he
  by_contra hne
  have hB := (sector_slice_factors star j).1
  have hBk := (sector_slice_factors star k).1
  have hh := hid j k
  have hz : (det (star.component j.val).direction (star.component k.val).direction : ℝ) ≠ 0 := by
    have h := star.pairwise_nonparallel j.val k.val (fun h => hne (Subtype.ext h))
    exact_mod_cast h
  dsimp [sectorBreakpoint] at he
  have he' := (div_eq_div_iff hB hBk).mp he
  clear he
  apply hz
  nlinarith

end
end ConvexNivat
