import ConvexNivat.Core
import Mathlib

namespace ConvexNivat

theorem primitive_ne_zero (v : Lattice) (hv : Primitive v) : v ≠ 0 := by
  intro h
  subst v
  simp [Primitive] at hv

/-- Source §0.1: the determinant form of a primitive vector is surjective. -/
theorem primitive_height_surjective (v : Lattice) (hv : Primitive v) :
    Function.Surjective (height v) := by
  have hgcd : Int.gcd v.1 v.2 = 1 := hv
  have hbez : v.1 * Int.gcdA v.1 v.2 + v.2 * Int.gcdB v.1 v.2 = 1 := by
    simpa [hgcd] using (Int.gcd_eq_gcd_ab v.1 v.2).symm
  intro t
  refine ⟨(-t * Int.gcdB v.1 v.2, t * Int.gcdA v.1 v.2), ?_⟩
  calc
    height v (-t * Int.gcdB v.1 v.2, t * Int.gcdA v.1 v.2) =
        t * (v.1 * Int.gcdA v.1 v.2 + v.2 * Int.gcdB v.1 v.2) := by
      simp only [height, det]
      ring
    _ = t := by rw [hbez, mul_one]

theorem nonparallel_ne_zero_left (h k : Lattice) (hInd : Nonparallel h k) :
    h ≠ 0 := by
  intro hz
  subst h
  simp [Nonparallel, det] at hInd

theorem nonparallel_ne_zero_right (h k : Lattice) (hInd : Nonparallel h k) :
    k ≠ 0 := by
  intro hz
  subst k
  simp [Nonparallel, det] at hInd

theorem height_add (u z w : Lattice) : height u (z + w) = height u z + height u w := by
  simp only [height, det, Prod.fst_add, Prod.snd_add]
  ring

theorem height_zsmul (u z : Lattice) (n : ℤ) : height u (n • z) = n * height u z := by
  change u.1 * (n * z.2) - u.2 * (n * z.1) = n * (u.1 * z.2 - u.2 * z.1)
  ring

theorem height_self (u : Lattice) : height u u = 0 := by
  simp only [height, det]
  ring

theorem rectangle_card (n k : ℕ) : (rectangle n k).card = n * k := by
  simp [rectangle, Finset.card_product, Int.card_Icc]

theorem rectangle_nonempty (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (rectangle n k).Nonempty := by
  refine ⟨(1, 1), ?_⟩
  simp only [rectangle, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨le_rfl, by exact_mod_cast hn⟩, ⟨le_rfl, by exact_mod_cast hk⟩⟩

theorem rectangle_latticeConvex (n k : ℕ) : LatticeConvex (rectangle n k) := by
  have hsubset : embed '' (rectangle n k : Set Lattice) ⊆
      Set.Icc (1 : ℝ) (n : ℝ) ×ˢ Set.Icc (1 : ℝ) (k : ℝ) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [rectangle, Finset.mem_coe, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc] at hz
    change (1 ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ (n : ℝ)) ∧
      (1 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ (k : ℝ))
    exact ⟨⟨by exact_mod_cast hz.1.1, by exact_mod_cast hz.1.2⟩,
      ⟨by exact_mod_cast hz.2.1, by exact_mod_cast hz.2.2⟩⟩
  have hhull := convexHull_min (𝕜 := ℝ) hsubset
    ((convex_Icc (𝕜 := ℝ) (1 : ℝ) (n : ℝ)).prod
      (convex_Icc (𝕜 := ℝ) (1 : ℝ) (k : ℝ)))
  intro z
  constructor
  · intro hz
    have hbounds := hhull hz
    change (1 ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ (n : ℝ)) ∧
      (1 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ (k : ℝ)) at hbounds
    simp only [rectangle, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by exact_mod_cast hbounds.1.1, by exact_mod_cast hbounds.1.2⟩,
      ⟨by exact_mod_cast hbounds.2.1, by exact_mod_cast hbounds.2.2⟩⟩
  · intro hz
    exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

end ConvexNivat
