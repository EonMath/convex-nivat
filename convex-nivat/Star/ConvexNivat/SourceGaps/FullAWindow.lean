import ConvexNivat.Geometry.ZonotopeBasic
import ConvexNivat.CoreLattice

namespace ConvexNivat

theorem integralZonotope_window_exists {m : ℕ} (Z : IntegralZonotope m) :
    ∃ S : Finset Lattice, S.Nonempty ∧ LatticeConvex S ∧
      (erosion Z.carrier S).Nonempty := by
  classical
  let B := Z.subsetSums.sup (fun z => max z.1.natAbs z.2.natAbs)
  let n := 2 * B + 1
  let r : Lattice := ((B : ℤ) + 1, (B : ℤ) + 1)
  refine ⟨rectangle n n, rectangle_nonempty n n (by omega) (by omega),
    rectangle_latticeConvex n n, r, ?_⟩
  have hsubset : embed '' (Z.subsetSums : Set Lattice) ⊆
      (fun x : RealPlane => embed r + x) ⁻¹' windowHull (rectangle n n) := by
    rintro _ ⟨z, hz, rfl⟩
    have hB : max z.1.natAbs z.2.natAbs ≤ B :=
      Finset.le_sup (f := fun z : Lattice => max z.1.natAbs z.2.natAbs) hz
    have h₁ : (z.1.natAbs : ℤ) ≤ (B : ℤ) := by
      exact_mod_cast (le_max_left z.1.natAbs z.2.natAbs).trans hB
    have h₂ : (z.2.natAbs : ℤ) ≤ (B : ℤ) := by
      exact_mod_cast (le_max_right z.1.natAbs z.2.natAbs).trans hB
    have h₁pos : z.1 ≤ (z.1.natAbs : ℤ) := Int.le_natAbs
    have h₂pos : z.2 ≤ (z.2.natAbs : ℤ) := Int.le_natAbs
    have h₁neg : -z.1 ≤ (z.1.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -z.1))
    have h₂neg : -z.2 ≤ (z.2.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -z.2))
    have hzrect : r + z ∈ rectangle n n := by
      simp only [rectangle, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_Icc, Prod.fst_add, Prod.snd_add]
      dsimp [r, n]
      omega
    have hembed : embed (r + z) = embed r + embed z := by
      ext <;> simp [embed]
    change embed r + embed z ∈ windowHull (rectangle n n)
    rw [← hembed]
    exact subset_convexHull ℝ _ ⟨r + z, hzrect, rfl⟩
  have hconv : Convex ℝ (windowHull (rectangle n n)) := convex_convexHull ℝ _
  have hhull := convexHull_min (𝕜 := ℝ) hsubset
    (hconv.translate_preimage_right (embed r))
  intro x hx
  apply hhull
  change x ∈ windowHull Z.subsetSums
  rwa [← Z.carrier_eq_hull_subsetSums]

end ConvexNivat
