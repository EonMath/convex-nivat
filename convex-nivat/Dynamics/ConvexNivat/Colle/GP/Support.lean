import ConvexNivat.Colle.GP.Normalisation
import ConvexNivat.ReductionRows

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

private theorem gp_vertex_strict_min (S : Finset Lattice) (hc : LatticeConvex S)
    (a : Lattice) (ha : a ∈ S) (f : RealPlane → ℝ) (hf : IsLinearMap ℝ f)
    (hmin : ∀ z ∈ S.erase a, f (embed a) < f (embed z)) : WindowVertex S a := by
  refine ⟨ha, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    have hsub : windowHull (S.erase a) ⊆ windowHull S :=
      convexHull_mono (Set.image_mono (Finset.erase_subset a S))
    have hbound : windowHull (S.erase a) ⊆ {x | f (embed a) < f x} := by
      apply convexHull_min _ (convex_halfSpace_gt hf _)
      rintro _ ⟨q, hq, rfl⟩
      exact hmin q hq
    refine Finset.mem_erase.mpr ⟨?_, (hc z).mp (hsub hz)⟩
    intro heq
    have hlt := hbound hz
    simpa [heq] using hlt
  · intro hz
    exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

private theorem gp_support_min (S : Finset Lattice) (hS : S.Nonempty) (v : Lattice) :
    supportRow S v = S.filter (fun z => det v z = rowMinimum v S hS) := by
  ext z
  simp only [supportRow, supportFace, Finset.mem_filter, normal_height]
  constructor
  · rintro ⟨hz, hmin⟩
    refine ⟨hz, le_antisymm ?_ (Finset.inf'_le _ hz)⟩
    apply Finset.le_inf'
    intro q hq
    exact_mod_cast hmin q hq
  · rintro ⟨hz, hheight⟩
    refine ⟨hz, fun q hq => ?_⟩
    rw [hheight]
    exact_mod_cast (Finset.inf'_le (det v) hq)

private theorem gp_support_nonempty (S : Finset Lattice) (hS : S.Nonempty) (v : Lattice) :
    (supportRow S v).Nonempty := by
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image (det v) hS
  refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
  intro q hq
  simp only [normal_height]
  exact_mod_cast hmin q hq

theorem oneSided_generating_support_at_least_two (ξ : Configuration ℤ)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) (v : Lattice)
    (hv : Primitive v) (hn : OneSidedNonexpansive ξ (normal v)) :
    2 ≤ (supportRow S v).card := by
  classical
  by_contra hcard
  have hnonempty := gp_support_nonempty S hS.1 v
  have hcard1 : (supportRow S v).card = 1 := by
    have := Finset.card_pos.mpr hnonempty
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
  have haf : a ∈ supportRow S v := by rw [ha]; simp
  have haS := (Finset.mem_filter.mp haf).1
  have hmin : ∀ q ∈ S, det v a ≤ det v q := by
    intro q hq
    have hh := (Finset.mem_filter.mp haf).2 q hq
    simp only [normal_height] at hh
    exact_mod_cast hh
  have hstrict : ∀ q ∈ S.erase a, det v a < det v q := by
    intro q hq
    have hqS := Finset.mem_of_mem_erase hq
    apply lt_of_le_of_ne (hmin q hqS)
    intro heq
    have hqf : q ∈ supportRow S v := by
      apply Finset.mem_filter.mpr
      refine ⟨hqS, fun r hr => ?_⟩
      rw [normal_height, normal_height, ← heq]
      exact_mod_cast hmin r hr
    rw [ha] at hqf
    exact (Finset.mem_erase.mp hq).1 (Finset.mem_singleton.mp hqf)
  have havertex : WindowVertex S a := by
    apply gp_vertex_strict_min S hS.2.1 a haS (fun x => realDet (embed v) x)
    · constructor
      · intro x y; simp [realDet]; ring
      · intro c x; simp [realDet]; ring
    · intro q hq
      simpa [realDet, embed, det] using (show (det v a : ℝ) < det v q by exact_mod_cast hstrict q hq)
  obtain ⟨_, x, hx, y, hy, hxy, hagree⟩ := hn
  have hagree' : AgreesOn x y (upperHalf v 0) := by
    intro z hz
    apply hagree z
    change 0 ≤ realDot (embed z) (normal v)
    rw [normal_height]
    exact_mod_cast hz
  obtain ⟨b, _, ⟨z, hzb, hz⟩, hupper, _⟩ :=
    highest_exterior_disagreement_normalisation ξ x y hx hy hxy v hv hagree'
  apply hz
  have hgenerated := hS.2.2 a havertex x hx y hy (z - a)
  have hlocal : ∀ q ∈ S.erase a, x (q + (z - a)) = y (q + (z - a)) := by
    intro q hq
    apply hupper
    have hs := hstrict q hq
    change b + 1 ≤ det v (q + (z - a))
    have heq : det v (q + (z - a)) = det v q + det v z - det v a := by
      simp [det]; ring
    rw [heq, hzb]
    omega
  have hfinal := hgenerated hlocal
  simpa [add_assoc] using hfinal

private theorem gp_vertex_secondary (S : Finset Lattice) (hc : LatticeConvex S)
    (v u a : Lattice) (ha : a ∈ supportRow S v)
    (htie : ∀ q ∈ S.erase a, det v q = det v a → det u a < det u q) :
    WindowVertex S a := by
  classical
  let M : ℕ := 1 + ∑ q ∈ S, (det u q - det u a).natAbs
  let f : RealPlane → ℝ := fun x => (M : ℝ) * realDet (embed v) x + realDet (embed u) x
  have hf : IsLinearMap ℝ f := by
    constructor <;> intro x y <;> simp [f, realDet] <;> ring
  have heval : ∀ z, f (embed z) = (M : ℝ) * (det v z : ℝ) + (det u z : ℝ) := by
    intro z
    simp [f, realDet, embed, det]
  apply gp_vertex_strict_min S hc a (Finset.mem_filter.mp ha).1 f hf
  intro q hq
  have hqS : q ∈ S := Finset.mem_of_mem_erase hq
  have hle : det v a ≤ det v q := by
    have h := (Finset.mem_filter.mp ha).2 q hqS
    rw [normal_height, normal_height] at h
    exact_mod_cast h
  have hpos : 0 < (M : ℤ) * (det v q - det v a) + (det u q - det u a) := by
    by_cases he : det v q = det v a
    · have hh := htie q hq he
      rw [he, sub_self, mul_zero, zero_add]
      omega
    · have hgap : (1 : ℤ) ≤ det v q - det v a := by omega
      have hsum : (det u q - det u a).natAbs ≤ ∑ r ∈ S, (det u r - det u a).natAbs :=
        Finset.single_le_sum (f := fun r : Lattice => (det u r - det u a).natAbs)
          (fun _ _ => Nat.zero_le _) hqS
      have hM : (det u q - det u a).natAbs < M := by dsimp [M]; omega
      have hMc : ((det u q - det u a).natAbs : ℤ) < M := by exact_mod_cast hM
      have hneg := Int.le_natAbs (a := -(det u q - det u a))
      simp only [Int.natAbs_neg] at hneg
      have hmul := mul_le_mul_of_nonneg_left hgap (Int.natCast_nonneg M)
      nlinarith
  have hreal : 0 < (M : ℝ) * ((det v q : ℝ) - det v a) + ((det u q : ℝ) - det u a) := by
    exact_mod_cast hpos
  rw [heval, heval]
  nlinarith

/-- GP09: only the actual supporting-row endpoints are asserted to be vertices. -/
theorem minimum_support_row_generated_endpoints (S : Finset Lattice)
    (hS : S.Nonempty) (hconvex : LatticeConvex S) (v : Lattice)
    (hv : Primitive v) (hq : 2 ≤ (supportRow S v).card) :
    ∃ a b : Lattice, BoundaryRun S v a b ∧
      b = a + (((supportRow S v).card - 1 : ℕ) : ℤ) • v ∧
      WindowVertex S a ∧ WindowVertex S b := by
  classical
  obtain ⟨u, hu⟩ := primitive_height_surjective v hv (-1)
  change det v u = -1 at hu
  have huv : det u v = 1 := by
    have hh : det u v = -det v u := by simp [det]; ring
    rw [hh, hu]; norm_num
  obtain ⟨a, ha, hrun⟩ := row_is_consecutive v hv S hconvex (rowMinimum v S hS)
    (by rw [← gp_support_min S hS v]; exact gp_support_nonempty S hS v)
  have hrun' : ∀ z, z ∈ supportRow S v ↔ ∃ j : ℕ, j < (supportRow S v).card ∧
      z = a + (j : ℤ) • v := by
    intro z
    simpa only [gp_support_min S hS v, Finset.mem_filter] using hrun z
  have hamem : a ∈ supportRow S v := (hrun' a).mpr ⟨0, by omega, by simp⟩
  let b := a + (((supportRow S v).card - 1 : ℕ) : ℤ) • v
  have hbmem : b ∈ supportRow S v := (hrun' b).mpr ⟨_, by omega, rfl⟩
  have hcoord : ∀ j : ℤ, det u (a + j • v) = det u a + j := by
    intro j
    change height u (a + j • v) = det u a + j
    rw [height_add, height_zsmul]
    change det u a + j * det u v = det u a + j
    rw [huv, mul_one]
  have honrow : ∀ c ∈ supportRow S v, ∀ q ∈ S, det v q = det v c → q ∈ supportRow S v := by
    intro c hc q hq heq
    apply Finset.mem_filter.mpr
    refine ⟨hq, fun r hr => ?_⟩
    rw [normal_height, normal_height, heq]
    simpa only [normal_height] using (Finset.mem_filter.mp hc).2 r hr
  refine ⟨a, b, ⟨hrun', rfl⟩, rfl, ?_, ?_⟩
  · apply gp_vertex_secondary S hconvex v u a hamem
    intro q hq heq
    obtain ⟨j, hj, hja⟩ := (hrun' q).mp (honrow a hamem q (Finset.mem_of_mem_erase hq) heq)
    have hj0 : j ≠ 0 := by
      intro hj0
      exact (Finset.mem_erase.mp hq).1 (by simpa [hj0] using hja)
    rw [hja, hcoord]
    omega
  · apply gp_vertex_secondary S hconvex v (-u) b hbmem
    intro q hq heq
    obtain ⟨j, hj, hja⟩ := (hrun' q).mp (honrow b hbmem q (Finset.mem_of_mem_erase hq) heq)
    have hjne : j ≠ (supportRow S v).card - 1 := by
      intro hjne
      exact (Finset.mem_erase.mp hq).1 (by simpa [b, hjne] using hja)
    have hneg : ∀ z, det (-u) z = -det u z := by intro z; simp [det]; ring
    rw [hneg, hneg, hja, hcoord]
    rw [hcoord]
    omega

end
end ConvexNivat.Colle
