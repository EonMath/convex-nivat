import ConvexNivat.Colle.Shared.RegionCore

namespace ConvexNivat.Colle
open Set Topology
noncomputable section

private theorem anchor_compact {v w : Lattice} (P : Region v w) :
    IsCompact (regionAnchorCell P) := by
  have hHull : IsCompact (regionVertexHull P) :=
    (Set.finite_range _).isCompact_convexHull ℝ
  let f : RealPlane × (ℝ × ℝ) → RealPlane :=
    fun q => q.1 - q.2.1 • embed v + q.2.2 • embed w
  have hf : Continuous f := by fun_prop
  have heq : regionAnchorCell P =
      f '' (regionVertexHull P ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    ext x
    constructor
    · rintro ⟨y, hy, a, b, ha, ha1, hb, hb1, rfl⟩
      exact ⟨(y, a, b), ⟨hy, ⟨ha, ha1⟩, ⟨hb, hb1⟩⟩, rfl⟩
    · rintro ⟨⟨y, a, b⟩, ⟨hy, ⟨ha, ha1⟩, ⟨hb, hb1⟩⟩, rfl⟩
      exact ⟨y, hy, a, b, ha, ha1, hb, hb1, rfl⟩
  rw [heq]
  exact (hHull.prod (isCompact_Icc.prod isCompact_Icc)).image hf

private theorem anchor_lattice_finite {v w : Lattice} (P : Region v w) :
    (embed ⁻¹' regionAnchorCell P).Finite := by
  have hembed : IsClosedEmbedding embed :=
    Int.isClosedEmbedding_coe_real.prodMap Int.isClosedEmbedding_coe_real
  exact (hembed.isCompact_preimage (anchor_compact P)).finite_of_discrete

private theorem anchor_subset_carrier {v w : Lattice} (P : Region v w) :
    regionAnchorCell P ⊆ P.carrier := by
  intro x hx
  obtain ⟨y, hy, a, b, ha, ha1, hb, hb1, rfl⟩ := hx
  rw [(region_halfplane_representation P).2.1]
  refine ⟨y, hy, a • embed (-v) + b • embed w, ⟨a, b, ha, hb, rfl⟩, ?_⟩
  have hneg : embed (-v) = -embed v := by simp [embed]
  rw [hneg]
  module

/-- RC04: the finite anchor cell includes all non-unimodular residues. -/
theorem integer_recession_finite_anchor {v w : Lattice} (P : Region v w) :
    ∃ G : Finset Lattice, (G : Set Lattice) ⊆ P.lattice ∧
      (G : Set Lattice) = embed ⁻¹' regionAnchorCell P ∧
      P.lattice = {z | ∃ g ∈ G, ∃ a b : ℕ,
        z = g - (a : ℤ) • v + (b : ℤ) • w} := by
  classical
  let G := (anchor_lattice_finite P).toFinset
  have hG : ∀ z : Lattice, z ∈ G ↔ embed z ∈ regionAnchorCell P := by
    intro z
    exact Set.Finite.mem_toFinset _
  have hsub : (G : Set Lattice) ⊆ P.lattice := by
    intro z hz
    exact anchor_subset_carrier P ((hG z).mp hz)
  refine ⟨G, hsub, ?_, ?_⟩
  · ext z
    exact hG z
  · ext z
    constructor
    · intro hz
      have hzc : embed z ∈ P.carrier := hz
      rw [(region_halfplane_representation P).2.1] at hzc
      obtain ⟨y, hy, d, ⟨a, b, ha, hb, rfl⟩, hz⟩ := hzc
      let n : ℕ := ⌊a⌋₊
      let m : ℕ := ⌊b⌋₊
      let g : Lattice := z + (n : ℤ) • v - (m : ℤ) • w
      have hg : g ∈ G := by
        apply (hG g).mpr
        refine ⟨y, hy, a - (n : ℝ), b - (m : ℝ), ?_, ?_, ?_, ?_, ?_⟩
        · exact sub_nonneg.mpr (Nat.floor_le ha)
        · have := Nat.lt_floor_add_one a
          dsimp [n]
          linarith
        · exact sub_nonneg.mpr (Nat.floor_le hb)
        · have := Nat.lt_floor_add_one b
          dsimp [m]
          linarith
        · have hgemb : embed g = embed z + (n : ℝ) • embed v - (m : ℝ) • embed w := by
            simp [g, embed, smul_eq_mul]
          rw [hgemb, hz]
          have hneg : embed (-v) = -embed v := by simp [embed]
          rw [hneg]
          module
      exact ⟨g, hg, n, m, by dsimp [g]; abel⟩
    · rintro ⟨g, hg, n, m, rfl⟩
      have hgc : embed g ∈ P.carrier := hsub hg
      have hd : -(n : ℝ) • embed v + (m : ℝ) • embed w ∈ recessionCone P.carrier := by
        rw [(region_halfplane_representation P).2.2.1]
        refine ⟨(n : ℝ), (m : ℝ), Nat.cast_nonneg n, Nat.cast_nonneg m, ?_⟩
        simp [embed, neg_smul]
      have h := hd (embed g) hgc
      change embed (g - (n : ℤ) • v + (m : ℤ) • w) ∈ P.carrier
      have heq : embed (g - (n : ℤ) • v + (m : ℤ) • w) =
          embed g + (-(n : ℝ) • embed v + (m : ℝ) • embed w) := by
        ext <;> simp [embed, smul_eq_mul] <;> ring
      exact heq.symm ▸ h

end
end ConvexNivat.Colle
