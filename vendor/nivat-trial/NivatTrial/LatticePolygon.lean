import NivatTrial.Zonotope

/-! Lattice-convex windows and placement of the two sites from Lemma 6.1.
The set of permitted translates is the actual zonotope erosion of the convex
hull, rather than an additional finite set supplied as a hypothesis. -/

namespace NivatTrial.LatticePolygon

open NivatTrial.Zonotope
open scoped BigOperators Pointwise

noncomputable section

def windowHull (S : Finset Lattice) : Set Plane :=
  convexHull ℝ (embed '' (S : Set Lattice))

def IsLatticeConvex (S : Finset Lattice) : Prop :=
  ∀ z : Lattice, embed z ∈ windowHull S ↔ z ∈ S

theorem mem_windowHull_of_mem (S : Finset Lattice) {z : Lattice} (hz : z ∈ S) :
    embed z ∈ windowHull S := by
  exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

theorem isLatticeConvex_iff (S : Finset Lattice) :
    IsLatticeConvex S ↔ ∀ z : Lattice, embed z ∈ windowHull S → z ∈ S := by
  constructor
  · intro h z
    exact (h z).mp
  · intro h z
    exact ⟨h z, mem_windowHull_of_mem S⟩

/-- This is precisely `S = Conv(S) ∩ ℤ²`, written using the lattice embedding. -/
theorem isLatticeConvex_iff_preimage (S : Finset Lattice) :
    IsLatticeConvex S ↔ embed ⁻¹' windowHull S = (S : Set Lattice) := by
  constructor
  · intro h
    exact Set.ext h
  · intro h z
    exact Set.ext_iff.mp h z

theorem windowHull_convex (S : Finset Lattice) : Convex ℝ (windowHull S) :=
  convex_convexHull ℝ _

/-- The integer anchors `r` for which `r + Z` lies in the window hull. -/
def placementSet (Z : Set Plane) (S : Finset Lattice) : Set Lattice :=
  {r | ∀ x ∈ Z, embed r + x ∈ windowHull S}

@[simp] theorem mem_placementSet (Z : Set Plane) (S : Finset Lattice) (r : Lattice) :
    r ∈ placementSet Z S ↔ ∀ x ∈ Z, embed r + x ∈ windowHull S := Iff.rfl

theorem placementSet_anti {Z W : Set Plane} (hZW : Z ⊆ W) (S : Finset Lattice) :
    placementSet W S ⊆ placementSet Z S := by
  intro r hr x hx
  exact hr x (hZW hx)

theorem placementSet_subset_window {Z : Set Plane} (hZ : (0 : Plane) ∈ Z)
    (S : Finset Lattice) (hS : IsLatticeConvex S) :
    placementSet Z S ⊆ (S : Set Lattice) := by
  intro r hr
  apply (hS r).mp
  simpa using hr 0 hZ

theorem placementSet_finite {Z : Set Plane} (hZ : (0 : Plane) ∈ Z)
    (S : Finset Lattice) (hS : IsLatticeConvex S) :
    (placementSet Z S).Finite :=
  S.finite_toSet.subset (placementSet_subset_window hZ S hS)

/-- The actual finite set `R_Z(S)` from §§2 and 7 of the paper. -/
def placementFinset {ι : Type*} [Fintype ι] (g : ι → Lattice)
    (S : Finset Lattice) (hS : IsLatticeConvex S) : Finset Lattice :=
  (placementSet_finite (zero_mem g) S hS).toFinset

@[simp] theorem mem_placementFinset {ι : Type*} [Fintype ι] (g : ι → Lattice)
    (S : Finset Lattice) (hS : IsLatticeConvex S) (r : Lattice) :
    r ∈ placementFinset g S hS ↔ r ∈ placementSet (zonotope g) S := by
  simp [placementFinset]

theorem placementFinset_subset {ι : Type*} [Fintype ι] (g : ι → Lattice)
    (S : Finset Lattice) (hS : IsLatticeConvex S) : placementFinset g S hS ⊆ S := by
  intro r hr
  exact placementSet_subset_window (zero_mem g) S hS
    ((mem_placementFinset g S hS r).mp hr)

/-- Lemma 7.1, for an arbitrary lattice site of the zonotope. -/
theorem site_mem_window (Z : Set Plane) (S : Finset Lattice)
    (hS : IsLatticeConvex S) (r q : Lattice)
    (hr : r ∈ placementSet Z S) (hq : embed q ∈ Z) : r + q ∈ S := by
  apply (hS (r + q)).mp
  rw [embed_add]
  exact hr (embed q) hq

theorem placement_sites {ι : Type*} [Fintype ι] (g : ι → Lattice)
    (S : Finset Lattice) (hS : IsLatticeConvex S) (q : Lattice)
    (hq : embed q ∈ zonotope g) :
    ∀ r : placementFinset g S hS, (r : Lattice) + q ∈ S := by
  intro r
  exact site_mem_window (zonotope g) S hS r q
    ((mem_placementFinset g S hS r).mp r.property) hq

/-- Corollary 6.2, including the paper's `q` and `q+d` formulation. -/
theorem witness_pair {ι : Type*} [Fintype ι] (g : ι → Lattice) (d : Lattice)
    (hd : embed d ∈ zonotope g - zonotope g) :
    ∃ q : Lattice, embed q ∈ zonotope g ∧ embed (q + d) ∈ zonotope g := by
  obtain ⟨q₀, q₁, h₀, h₁, hdq⟩ := diff_points g d hd
  refine ⟨q₀, h₀, ?_⟩
  have hq : q₀ + d = q₁ := by rw [hdq]; abel
  simpa only [hq] using h₁

/-- The output directly supplies both position hypotheses of
`complexity_of_bounded_factorization_and_witness`. -/
theorem witness_placements {ι : Type*} [Fintype ι] (g : ι → Lattice)
    (S : Finset Lattice) (hS : IsLatticeConvex S) (d : Lattice)
    (hd : embed d ∈ zonotope g - zonotope g) :
    ∃ q₀ q₁ : Lattice, d = q₁ - q₀ ∧
      (∀ r : placementFinset g S hS, (r : Lattice) + q₀ ∈ S) ∧
      (∀ r : placementFinset g S hS, (r : Lattice) + q₁ ∈ S) := by
  obtain ⟨q₀, q₁, h₀, h₁, hdq⟩ := diff_points g d hd
  exact ⟨q₀, q₁, hdq, placement_sites g S hS q₀ h₀, placement_sites g S hS q₁ h₁⟩

end

end NivatTrial.LatticePolygon
