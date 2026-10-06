import ConvexNivat.SectorDefinitions

namespace ConvexNivat
noncomputable section

theorem sector_closure_weak_signs {p : ℕ} (star : StarData p)
    (ε : SectorSigns star) (hε : RealisedSector star ε) (x : RealPlane) :
    x ∈ closure (sectorCone star ε) ↔
      ∀ j : Fin star.m,
        (ε j = .left → realHeight (star.component j).direction x ≤ 0) ∧
        (ε j = .right → 0 ≤ realHeight (star.component j).direction x) := by
  constructor
  · intro hx j
    have hc : Continuous (realHeight (star.component j).direction) := by
      unfold realHeight
      fun_prop
    constructor
    · intro he
      apply closure_minimal (t := {x | realHeight (star.component j).direction x ≤ 0})
        ?_ (isClosed_le hc continuous_const) hx
      intro y hy
      exact le_of_lt (by simpa only [sectorCone, Set.mem_ofPred_eq, he] using hy j)
    · intro he
      apply closure_minimal (t := {x | 0 ≤ realHeight (star.component j).direction x})
        ?_ (isClosed_le continuous_const hc) hx
      intro y hy
      exact le_of_lt (by simpa only [sectorCone, Set.mem_ofPred_eq, he] using hy j)
  · intro hx
    obtain ⟨y, hy⟩ := hε
    have hs : openSegment ℝ x y ⊆ sectorCone star ε := by
      rintro z ⟨a, b, ha, hb, hab, rfl⟩
      intro j
      have he : realHeight (star.component j).direction (a • x + b • y) =
          a * realHeight (star.component j).direction x +
            b * realHeight (star.component j).direction y := by
        dsimp [realHeight]
        change (↑(star.component j).direction.1 * (a * x.2 + b * y.2) -
          ↑(star.component j).direction.2 * (a * x.1 + b * y.1)) = _
        ring
      rw [he]
      have hyj := hy j
      cases hj : ε j with
      | left =>
        have hxx := (hx j).1 hj
        simp only [hj] at hyj
        exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le hxx)
          (mul_neg_of_pos_of_neg hb hyj)
      | right =>
        have hxx := (hx j).2 hj
        simp only [hj] at hyj
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le hxx) (mul_pos hb hyj)
    exact closure_mono hs (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

end
end ConvexNivat
