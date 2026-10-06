import NivatTrial.ColleEnvelopeRays
import NivatTrial.LatticeCoordinates

/-! Entry along a nonprimitive horizontal lattice direction is uniform on
each finite height band. A finite row of residue representatives is first
placed in the region; forward invariance fills the entire left half-strip. -/

namespace NivatTrial.ColleBoundaryStripGeometry

open NivatTrial.Geometry NivatTrial.RegionGeometry
open NivatTrial.LatticeCoordinates
open Filter
open scoped Classical

noncomputable section

/-- Once a block of width `c` is in a region, forward invariance under the
left translation by `c` places every site farther to its left. -/
theorem left_band_of_block (R : Set Lattice) (e : Lattice ≃+ Lattice)
    (c b H L : ℤ) (hc : 0 < c)
    (hforward : ForwardInvariant R (e (-c,0)))
    (hblock : ∀ x y : ℤ, b ≤ y → y ≤ H → L-c < x → x ≤ L → e (x,y) ∈ R) :
    ∀ x y : ℤ, b ≤ y → y ≤ H → x ≤ L → e (x,y) ∈ R := by
  let P : ℕ → Prop := fun n => ∀ x y : ℤ,
    b ≤ y → y ≤ H → x ≤ L → (L-x).toNat = n → e (x,y) ∈ R
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hby hyH hx hgap
      by_cases hnear : L-c < x
      · exact hblock x y hby hyH hnear hx
      · have hx' : x+c ≤ L := by omega
        have hlt : (L-(x+c)).toNat < n := by
          rw [← hgap]
          omega
        have hin : e (x+c,y) ∈ R := ih _ hlt (x+c) y hby hyH hx' rfl
        have heq : (x,y) = (x+c,y)+(-c,0) := by
          ext <;> simp
        rw [heq,map_add]
        exact hforward _ hin
  intro x y hby hyH hx
  exact hP _ x y hby hyH hx rfl

/-- Pointwise eventual entry plus one nonprimitive left translation yields
uniform inclusion of a whole left half-strip of any fixed finite height.
No convexity assumption is used in this finite-residue step. -/
theorem eventual_entry_implies_left_band
    (R : Set Lattice) (e : Lattice ≃+ Lattice)
    (c : ℤ) (hc : 0 < c) (b : ℤ)
    (hentry : ∀ z : Lattice, b ≤ (e.symm z).2 →
      ∀ᶠ n : ℕ in atTop, z+n•e (-c,0) ∈ R)
    (hforward : ForwardInvariant R (e (-c,0)))
    (H : ℤ) (_hbH : b ≤ H) :
    ∃ L : ℤ, ∀ z : Lattice,
      b ≤ z.2 → z.2 ≤ H → z.1 ≤ L → e z ∈ R := by
  let B : Finset Lattice := (Finset.Icc 0 (c-1)).product (Finset.Icc b H)
  have hentryB (z : B) :
      ∀ᶠ n : ℕ in atTop, e (z.val+n•((-c,0) : Lattice)) ∈ R := by
    have hz : b ≤ z.val.2 := by
      have hmem := (Finset.mem_product.mp z.property).2
      exact (Finset.mem_Icc.mp hmem).1
    have hh := hentry (e z.val) (by simpa using hz)
    simpa only [map_add,map_nsmul] using hh
  have hall : ∀ᶠ n : ℕ in atTop,
      ∀ z : B, e (z.val+n•((-c,0) : Lattice)) ∈ R :=
    Filter.eventually_all.mpr hentryB
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  let L : ℤ := c-1-(N:ℤ)*c
  have hblock : ∀ x y : ℤ, b ≤ y → y ≤ H → L-c < x → x ≤ L →
      e (x,y) ∈ R := by
    intro x y hby hyH hxlow hxhigh
    let r : ℤ := x+(N:ℤ)*c
    have hrlo : 0 ≤ r := by dsimp [r,L] at *; omega
    have hrhi : r ≤ c-1 := by dsimp [r,L] at *; omega
    have hmem : (r,y) ∈ B := by
      change (r,y) ∈ (Finset.Icc 0 (c-1)).product (Finset.Icc b H)
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hrlo,hrhi⟩,
        Finset.mem_Icc.mpr ⟨hby,hyH⟩⟩
    have hpoint := hN N (le_refl N) ⟨(r,y),hmem⟩
    have heq : (r,y)+N•((-c,0) : Lattice) = (x,y) := by
      ext <;> simp [r,Prod.smul_mk]
    rwa [heq] at hpoint
  refine ⟨L,?_⟩
  intro z hby hyH hx
  exact left_band_of_block R e c b H L hc hforward hblock
    z.1 z.2 hby hyH hx

end
end NivatTrial.ColleBoundaryStripGeometry
