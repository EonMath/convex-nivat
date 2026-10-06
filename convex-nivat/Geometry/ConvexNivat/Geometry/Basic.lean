import ConvexNivat.Geometry.Definitions

/-! Standalone geometric obligations, separated from integer decomposition. -/

namespace ConvexNivat

open scoped BigOperators Pointwise

theorem embed_injective : Function.Injective embed := by
  intro a b h
  apply Prod.ext
  · exact_mod_cast (show (a.1 : ℝ) = (b.1 : ℝ) from congrArg Prod.fst h)
  · exact_mod_cast (show (a.2 : ℝ) = (b.2 : ℝ) from congrArg Prod.snd h)

theorem embed_zero : embed (0 : Lattice) = 0 := by
  simp [embed]

theorem embed_add (a b : Lattice) : embed (a + b) = embed a + embed b := by
  ext <;> simp [embed]

theorem embed_sub (a b : Lattice) : embed (a - b) = embed a - embed b := by
  ext <;> simp [embed]

theorem embed_nsmul (n : ℕ) (a : Lattice) :
    embed (n • a) = (n : ℝ) • embed a := by
  ext <;> simp [embed, nsmul_eq_mul]

theorem window_mem_hull (S : Finset Lattice) {z : Lattice} (hz : z ∈ S) :
    embed z ∈ windowHull S := by
  exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

theorem windowHull_convex (S : Finset Lattice) : Convex ℝ (windowHull S) := by
  exact convex_convexHull ℝ _

theorem windowHull_compact (S : Finset Lattice) : IsCompact (windowHull S) := by
  exact ((S.finite_toSet).image embed).isCompact_convexHull ℝ

theorem latticePoints_windowHull {S : Finset Lattice} (hS : LatticeConvex S) :
    latticePoints (windowHull S) = (S : Set Lattice) := by
  ext z
  exact hS z

theorem latticePoints_translate (r : Lattice) (P : Set RealPlane) :
    latticePoints (latticeTranslate r P) = (fun q => r + q) '' latticePoints P := by
  ext z
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨z - r, ?_, by simp⟩
    change embed (z - r) ∈ P
    have he : embed (z - r) = x := by
      rw [embed_sub, ← h]
      exact add_sub_cancel_left (embed r) x
    rwa [he]
  · rintro ⟨q, hq, rfl⟩
    exact ⟨embed q, hq, (embed_add r q).symm⟩

theorem mem_erosion_iff_translate_subset (P : Set RealPlane) (S : Finset Lattice)
    (r : Lattice) :
    r ∈ erosion P S ↔ latticeTranslate r P ⊆ windowHull S := by
  constructor
  · intro hr x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hr y hy
  · intro hr x hx
    exact hr ⟨x, hx, rfl⟩

/-- Remark 2.6, first sentence, independent of any zonotope theorem. -/
theorem erosion_latticePoints_subset {P : Set RealPlane} {S : Finset Lattice}
    (hS : LatticeConvex S) {r : Lattice} (hr : r ∈ erosion P S) :
    latticePoints (latticeTranslate r P) ⊆ (S : Set Lattice) := by
  intro q hq
  exact (hS q).mp ((mem_erosion_iff_translate_subset P S r).mp hr hq)

theorem erosion_placement {P : Set RealPlane} {S : Finset Lattice}
    (hS : LatticeConvex S) {r q : Lattice} (hr : r ∈ erosion P S)
    (hq : q ∈ latticePoints P) : r + q ∈ S := by
  apply (hS (r + q)).mp
  rw [embed_add]
  exact hr (embed q) hq

theorem erosion_subset_window {P : Set RealPlane} {S : Finset Lattice}
    (hS : LatticeConvex S) (hzero : (0 : RealPlane) ∈ P) :
    erosion P S ⊆ (S : Set Lattice) := by
  intro r hr
  exact (hS r).mp (by simpa using hr 0 hzero)

theorem erosion_finite {P : Set RealPlane} {S : Finset Lattice}
    (hS : LatticeConvex S) (hzero : (0 : RealPlane) ∈ P) :
    (erosion P S).Finite := by
  exact S.finite_toSet.subset (erosion_subset_window hS hzero)

theorem erosion_ncard_le {P : Set RealPlane} {S : Finset Lattice}
    (hS : LatticeConvex S) (hzero : (0 : RealPlane) ∈ P) :
    (erosion P S).ncard ≤ S.card := by
  simpa using Set.ncard_le_ncard (erosion_subset_window hS hzero) S.finite_toSet

/-- A body with interior cannot fit in a window hull with empty interior. -/
theorem erosion_eq_empty_of_empty_interior {P : Set RealPlane} {S : Finset Lattice}
    (hP : (interior P).Nonempty) (hS : interior (windowHull S) = ∅) :
    erosion P S = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  rcases hP with ⟨x, hx⟩
  have hi : embed r + x ∈ interior (latticeTranslate r P) := by
    exact (isOpenMap_add_left (embed r)).image_interior_subset P ⟨x, hx, rfl⟩
  have hh := interior_mono ((mem_erosion_iff_translate_subset P S r).mp hr) hi
  rwa [hS] at hh

/-- Lemma 7.1. Both sites lie in the actual window; membership of the pair in
the zonotope is supplied separately by Corollary 6.2. -/
theorem lemma7_1 {m : ℕ} (Z : IntegralZonotope m) {S : Finset Lattice}
    (hS : LatticeConvex S) {q d r : Lattice}
    (hq : q ∈ latticePoints Z.carrier)
    (hqd : q + d ∈ latticePoints Z.carrier)
    (hr : r ∈ erosion Z.carrier S) : r + q ∈ S ∧ r + q + d ∈ S := by
  constructor
  · exact erosion_placement hS hr hq
  · simpa [add_assoc] using erosion_placement hS hr hqd

end ConvexNivat
