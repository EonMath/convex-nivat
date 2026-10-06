import NivatTrial.ColleParallelogramGeometry
import NivatTrial.ColleSlantedBlock
import NivatTrial.HorizontalCoordinates

/-! The parallelogram anchors extracted from the actual support edge.
No separate placement or parallelogram hypothesis is required. -/

namespace NivatTrial.ColleParallelogramWindow

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.ColleGenerating NivatTrial.ColleAmbiguity
open NivatTrial.ColleEnvelopeGeometry NivatTrial.BalancedWindows
open NivatTrial.ColleDirectionalPropagation NivatTrial.ColleSlantedBlock
open NivatTrial.ColleParallelogramGeometry
open scoped Classical
noncomputable section

/-- A primitive support direction lists its edge as a full consecutive run. -/
theorem supportEdge_run_primitive (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (k : Lattice)
    (hprim : Int.gcd k.1 k.2 = 1) :
    ∃ a : Lattice, supportEdge S (embed k) =
      (Finset.range (supportEdge S (embed k)).card).image
        (fun j : ℕ => a + (j : ℤ) • k) := by
  obtain ⟨v,hv⟩ := exists_unimodular_complement k hprim
  have hv' : NivatTrial.Divisibility.det k v = 1 := hv
  let e := NivatTrial.Divisibility.basisEquiv k v hv'
  have he1 : e (1,0) = k := NivatTrial.Divisibility.basisEquiv_first k v hv'
  have he2 : e (0,1) = v := NivatTrial.Divisibility.basisEquiv_second k v hv'
  have hdual : dualNormal e (embed k) = (1,0) := by
    unfold dualNormal
    rw [he1,he2]
    change (linearScore (embed k) (embed v), -linearScore (embed k) (embed k)) = (1,0)
    rw [linearScore_embed_det,linearScore_embed_det,hv,det_self]
    norm_num
  obtain ⟨a,ha⟩ := supportEdge_run_in_basis e S (embed k) hconv hS hdual
  exact ⟨a,by simpa only [he1] using ha⟩

/-- The real support edge itself supplies both end points and its exact
length in the primitive direction. -/
theorem supportEdge_endpoints (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (k : Lattice)
    (hprim : Int.gcd k.1 k.2 = 1)
    (hedge : 2 ≤ (supportEdge S (embed k)).card) :
    ∃ a : Lattice, a ∈ S ∧
      a+((supportEdge S (embed k)).card-1)•k ∈ S ∧
      ∀ z ∈ S, det k a ≤ det k z := by
  obtain ⟨a,ha⟩ := supportEdge_run_primitive S hS hconv k hprim
  have hfirst : a ∈ supportEdge S (embed k) := by
    rw [ha]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
  have hlast : a+((supportEdge S (embed k)).card-1)•k ∈ supportEdge S (embed k) := by
    rw [ha]
    refine Finset.mem_image.mpr ⟨(supportEdge S (embed k)).card-1,
      Finset.mem_range.mpr (by omega), ?_⟩
    rw [natCast_zsmul, ← ha]
  refine ⟨a,supportEdge_subset S (embed k) hfirst,
    supportEdge_subset S (embed k) hlast,?_⟩
  intro z hz
  have hh := (Finset.mem_filter.mp hfirst).2 z hz
  change linearScore (embed k) (embed a) ≤ linearScore (embed k) (embed z) at hh
  rw [linearScore_embed_det,linearScore_embed_det] at hh
  exact_mod_cast hh

/-- Genuine support-face geometry provides one finite family of anchors
with both the semi-ambiguity run length and every high horizontal seed block. -/
theorem exists_cellAnchors_of_support_edge (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (k : Lattice)
    (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2) (L : ℕ)
    (hbot : L < (bottomEdge S).card) (htop : L < (topEdge S).card)
    (hedge : 2 ≤ (supportEdge S (embed k)).card) :
    ∃ a : Lattice,
      (∀ w ∈ cellAnchors S a k L,
        ∀ j : Fin ((supportEdge S (embed k)).card-1),
          w+(j.val : ℤ)•k ∈ supportBase S (embed k)) ∧
      (∀ (N : ℕ) (t : ℤ), a.2+(N : ℤ)*k.2 ≤ t →
        ∃ l n : ℤ, (N : ℤ) ≤ n ∧ ∀ j : Fin L,
          ∃ w ∈ cellAnchors S a k L, (l+(j : ℤ),t) = w+n•k) := by
  obtain ⟨a,ha,hb,hmin⟩ := supportEdge_endpoints S hS hconv k hprim hedge
  have hm : 0 < (supportEdge S (embed k)).card-1 := by omega
  refine ⟨a,?_,?_⟩
  · intro w hw j
    have hwcell := (Finset.mem_filter.mp hw).2
    simpa only [natCast_zsmul] using firstCell_run_mem_supportBase S hS hconv
      a k _ L hm hk hbot htop ha hb hmin w hwcell j.val j.isLt
  · intro N t ht
    exact cellAnchors_cover_high_rows S hS hconv a k _ L hm hk hbot htop
      ha hb hmin N t ht

/-- The shorter first-direction edge determines the claimed seed width. -/
theorem exists_min_edge_cellAnchors (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : IsLatticeConvex S) (k : Lattice)
    (hprim : Int.gcd k.1 k.2 = 1) (hk : 0 < k.2)
    (hedge : 2 ≤ (supportEdge S (embed k)).card) :
    let L := min (bottomEdge S).card (topEdge S).card-1
    ∃ a : Lattice,
      (∀ w ∈ cellAnchors S a k L,
        ∀ j : Fin ((supportEdge S (embed k)).card-1),
          w+(j.val : ℤ)•k ∈ supportBase S (embed k)) ∧
      (∀ (N : ℕ) (t : ℤ), a.2+(N : ℤ)*k.2 ≤ t →
        ∃ l n : ℤ, (N : ℤ) ≤ n ∧ ∀ j : Fin L,
          ∃ w ∈ cellAnchors S a k L, (l+(j : ℤ),t) = w+n•k) := by
  have hb := Finset.card_pos.mpr (bottomEdge_nonempty hS)
  have ht := Finset.card_pos.mpr (topEdge_nonempty hS)
  apply exists_cellAnchors_of_support_edge S hS hconv k hprim hk _
  · omega
  · omega
  · exact hedge

end
end NivatTrial.ColleParallelogramWindow
