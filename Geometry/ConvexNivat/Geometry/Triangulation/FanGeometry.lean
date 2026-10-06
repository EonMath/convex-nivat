import ConvexNivat.Geometry.Triangulation.Definitions
import ConvexNivat.Geometry.Basic

namespace ConvexNivat.PolygonTriangulation

private theorem det_expand (u v w : RealPlane) :
    realDet (v-u) (w-u) = realDet v w + realDet u v - realDet u w := by
  simp [realDet]
  ring

private theorem det_skew (u v : RealPlane) : realDet u v = -realDet v u := by
  simp [realDet]
  ring

private theorem det_coordinates (u v x : RealPlane) (h : realDet u v ≠ 0) :
    x = (realDet x v / realDet u v) • u + (realDet u x / realDet u v) • v := by
  apply Prod.ext
  · change x.1 = (realDet x v / realDet u v) * u.1 + (realDet u x / realDet u v) * v.1
    field_simp [h]
    simp only [realDet]
    ring
  · change x.2 = (realDet x v / realDet u v) * u.2 + (realDet u x / realDet u v) * v.2
    field_simp [h]
    simp only [realDet]
    ring

private theorem two_weights_hull (u v : RealPlane) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) :
    a • u + b • v ∈ convexHull ℝ ({0,u,v} : Set RealPlane) := by
  have hu : u ∈ convexHull ℝ ({0,u,v} : Set RealPlane) := subset_convexHull ℝ _ (by simp)
  have hv : v ∈ convexHull ℝ ({0,u,v} : Set RealPlane) := subset_convexHull ℝ _ (by simp)
  have hz : (0 : RealPlane) ∈ convexHull ℝ ({0,u,v} : Set RealPlane) := subset_convexHull ℝ _ (by simp)
  have hs : 0 < a+b := add_pos ha hb
  have hnorm := (convex_convexHull ℝ ({0,u,v} : Set RealPlane)) hu hv
    (le_of_lt (div_pos ha hs)) (le_of_lt (div_pos hb hs))
    (show a/(a+b)+b/(a+b)=1 by rw [← add_div, div_self (ne_of_gt hs)])
  have hh := (convex_convexHull ℝ ({0,u,v} : Set RealPlane)) hz hnorm
    (show 0 ≤ 1-(a+b) by linarith) hs.le (by ring : 1-(a+b)+(a+b)=1)
  simpa only [smul_zero, zero_add, smul_add, smul_smul,
    mul_div_cancel₀ _ (ne_of_gt hs)] using hh

/-- PT22: explicit radial coefficients exhibit the forbidden generator in a hull. -/
theorem four_point_radial_obstruction (l k : RealPlane →ₗ[ℝ] ℝ)
    (hdet : ∀ x y, realDet x y = l x * k y - k x * l y)
    (u v w : RealPlane) (hu : 0 < l u) (hv : 0 < l v) (hw : 0 < l w) :
    ((k w / l w < k u / l u ∧ k u / l u < k v / l v) →
      realDet (v - u) (w - u) < 0 →
      0 < realDet u v / realDet w v ∧
      0 < realDet w u / realDet w v ∧
      realDet u v / realDet w v + realDet w u / realDet w v < 1 ∧
      u = (realDet u v / realDet w v) • w +
          (realDet w u / realDet w v) • v ∧
      u ∈ convexHull ℝ ({0, w, v} : Set RealPlane)) ∧
    ((k u / l u < k v / l v ∧ k v / l v < k w / l w) →
      realDet (v - u) (w - u) < 0 →
      0 < realDet v w / realDet u w ∧
      0 < realDet u v / realDet u w ∧
      realDet v w / realDet u w + realDet u v / realDet u w < 1 ∧
      v = (realDet v w / realDet u w) • u +
          (realDet u v / realDet u w) • w ∧
      v ∈ convexHull ℝ ({0, u, w} : Set RealPlane)) := by
  have hpos : ∀ a b, 0 < l a → 0 < l b → k a / l a < k b / l b →
      0 < realDet a b := by
    intro a b ha hb hs
    rw [hdet]
    have hh := (div_lt_div_iff₀ ha hb).1 hs
    linarith
  constructor
  · intro hs hn
    have huv := hpos u v hu hv hs.2
    have hwu := hpos w u hw hu hs.1
    have hwv := hpos w v hw hv (lt_trans hs.1 hs.2)
    have ha := div_pos huv hwv
    have hb := div_pos hwu hwv
    have hsum : realDet u v / realDet w v + realDet w u / realDet w v < 1 := by
      rw [← add_div, div_lt_one hwv]
      rw [det_expand] at hn
      rw [det_skew v w, det_skew u w] at hn
      linarith
    have he := det_coordinates w v u (ne_of_gt hwv)
    exact ⟨ha,hb,hsum,he,he ▸ two_weights_hull w v _ _ ha hb hsum⟩
  · intro hs hn
    have huv := hpos u v hu hv hs.1
    have hvw := hpos v w hv hw hs.2
    have huw := hpos u w hu hw (lt_trans hs.1 hs.2)
    have ha := div_pos hvw huw
    have hb := div_pos huv huw
    have hsum : realDet v w / realDet u w + realDet u v / realDet u w < 1 := by
      rw [← add_div, div_lt_one huw]
      rw [det_expand] at hn
      linarith
    have he := det_coordinates u w v (ne_of_gt huw)
    exact ⟨ha,hb,hsum,he,he ▸ two_weights_hull u w _ _ ha hb hsum⟩

/-- PT24: actual adjacent triples give nondegenerate contained cells and all vertices. -/
theorem fan_cells_nondegenerate_and_contained (Q : Finset Lattice)
    (p : Lattice) (N : ℕ) (hp : p ∈ Q) (c : RadialChain Q p N) :
    ND (fan c) ∧ Contained (windowHull Q) (fan c) ∧
    (∀ i : Fin (c.length + 1), (fanCell c i).vertices ⊆ Q) ∧
    V (fan c) = Q := by
  classical
  have hpoint (i : Fin (c.length+2)) : c.point i ∈ Q := by
    have hh : c.point i ∈ (Q.erase p : Set Lattice) := c.range_eq ▸ Set.mem_range_self i
    exact Finset.mem_of_mem_erase hh
  have hsub (i : Fin (c.length+1)) : (fanCell c i).vertices ⊆ Q := by
    intro q hq
    simp only [fanCell, LatticeTriangle.vertices, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hp
    · exact hpoint _
    · exact hpoint _
  refine ⟨?_, ?_, hsub, ?_⟩
  · intro T hT
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    exact ne_of_gt (c.determinants i.castSucc i.succ Fin.castSucc_lt_succ)
  · intro T hT
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    exact convexHull_mono (Set.image_mono (hsub i))
  · apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨T,hT,hq⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
      exact hsub i hq
    · intro q hq
      by_cases hqp : q = p
      · subst q
        apply Finset.mem_biUnion.mpr
        exact ⟨fanCell c 0, Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,
          by simp [fanCell,LatticeTriangle.vertices]⟩
      · have hr : q ∈ Set.range c.point := by rw [c.range_eq]; exact Finset.mem_erase.mpr ⟨hqp,hq⟩
        obtain ⟨j,rfl⟩ := hr
        by_cases hj : j.val < c.length+1
        · let i : Fin (c.length+1) := ⟨j.val,hj⟩
          have he : i.castSucc = j := Fin.ext rfl
          apply Finset.mem_biUnion.mpr
          exact ⟨fanCell c i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
            by simp [fanCell,LatticeTriangle.vertices,he]⟩
        · let i : Fin (c.length+1) := ⟨c.length,by omega⟩
          have he : i.succ = j := Fin.ext (by dsimp [i]; omega)
          apply Finset.mem_biUnion.mpr
          exact ⟨fanCell c i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
            by simp [fanCell,LatticeTriangle.vertices,he]⟩

end ConvexNivat.PolygonTriangulation
