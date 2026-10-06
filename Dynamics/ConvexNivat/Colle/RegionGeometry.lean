import ConvexNivat.Colle.Definitions

namespace ConvexNivat.Colle
open Filter Topology

private theorem closed_convex_ray_add (C : Set RealPlane) (hc : IsClosed C)
    (hv : Convex ℝ C) (p u x : RealPlane) (hx : x ∈ C)
    (hray : ∀ t : ℝ, 0 ≤ t → p + t • u ∈ C) (t : ℝ) (ht : 0 ≤ t) :
    x + t • u ∈ C := by
  let f : ℕ → RealPlane := fun n =>
    x + t • u + (1 / ((n : ℝ) + 1)) • (p - x)
  have hmem : ∀ n, f n ∈ C := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have ha : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_one hden).mpr
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      linarith
    have h := hv hx (hray (((n : ℝ) + 1) * t) (mul_nonneg hden.le ht)) ha hb
      (by ring : 1 - 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) = 1)
    convert h using 1
    ext <;> simp only [f, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;>
      field_simp <;> ring
  have hlim : Tendsto f atTop (𝓝 (x + t • u)) := by
    have hzero := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (p - x)
    simpa [f] using tendsto_const_nhds.add hzero
  exact hc.mem_of_tendsto hlim (Eventually.of_forall hmem)

private theorem first_ray_mem {v w : Lattice} (P : Region v w) (t : ℝ)
    (ht : 0 ≤ t) : embed P.firstAnchor - t • embed v ∈ P.carrier := by
  apply P.closed.closure_eq ▸ (frontier_subset_closure (s := P.carrier) ?_)
  rw [P.boundary_eq]
  exact Or.inl (Or.inl ⟨t, ht, rfl⟩)

private theorem second_ray_mem {v w : Lattice} (P : Region v w) (t : ℝ)
    (ht : 0 ≤ t) : embed P.secondAnchor + t • embed w ∈ P.carrier := by
  apply P.closed.closure_eq ▸ (frontier_subset_closure (s := P.carrier) ?_)
  rw [P.boundary_eq]
  exact Or.inl (Or.inr ⟨t, ht, rfl⟩)

private theorem lattice_forward_first {v w : Lattice} (P : Region v w) (a : ℕ) :
    ForwardInvariant P.lattice ((-(a : ℤ)) • v) := by
  intro z hz
  have h := closed_convex_ray_add P.carrier P.closed P.convex
    (embed P.firstAnchor) (-embed v) (embed z) hz
    (fun t ht => by simpa [smul_neg, sub_eq_add_neg] using first_ray_mem P t ht)
    (a : ℝ) (Nat.cast_nonneg a)
  simpa [Region.lattice, embed, smul_eq_mul] using h

private theorem lattice_forward_second {v w : Lattice} (P : Region v w) (a : ℕ) :
    ForwardInvariant P.lattice ((a : ℤ) • w) := by
  intro z hz
  have h := closed_convex_ray_add P.carrier P.closed P.convex
    (embed P.secondAnchor) (embed w) (embed z) hz
    (second_ray_mem P) (a : ℝ) (Nat.cast_nonneg a)
  simpa [Region.lattice, embed, smul_eq_mul] using h

private theorem overlap_neg (x : Configuration ℤ) (U : Set Lattice) (h : Lattice)
    (hp : OverlapHasPeriod x U h) : OverlapHasPeriod x U (-h) := by
  intro z hz hzh
  simpa [add_assoc] using (hp (z + -h) hzh (by simpa [add_assoc] using hz)).symm

private theorem predecessor_turn {v w : Lattice} (P : Region v w) :
    0 < det P.predecessor w := by
  unfold Region.predecessor
  split
  · apply P.second_turn
    dsimp
    omega
  · exact P.turn_positive

private theorem predecessor_support {v w : Lattice} (P : Region v w)
    (g : Lattice) (hg : g ∈ P.lattice) :
    0 ≤ det P.predecessor (g - P.secondAnchor) := by
  unfold Region.predecessor
  split
  · rename_i hcount
    let i : Fin P.boundedCount :=
      ⟨P.boundedCount - 1, Nat.sub_lt hcount Nat.zero_lt_one⟩
    have hanchor : P.vertex i.succ = P.secondAnchor := by
      congr 1
      apply Fin.ext
      dsimp [i]
      omega
    obtain ⟨k, hk, heq⟩ := P.bounded_length i
    have hs := P.bounded_support i (embed g) hg
    have hs' : 0 ≤ det (P.boundedDirection i) (g - P.vertex i.castSucc) := by
      dsimp [realDet, embed] at hs
      simp only [det, Prod.fst_sub, Prod.snd_sub]
      exact_mod_cast hs
    rw [hanchor] at heq
    have hdet : det (P.boundedDirection i) (g - P.secondAnchor) =
        det (P.boundedDirection i) (g - P.vertex i.castSucc) := by
      have heq' : P.secondAnchor = P.vertex i.castSucc + k • P.boundedDirection i :=
        by simpa [add_comm] using (sub_eq_iff_eq_add.mp heq)
      rw [heq']
      simp [det, smul_eq_mul]
      ring
    change 0 ≤ det (P.boundedDirection i) (g - P.secondAnchor)
    rwa [hdet]
  · rename_i hcount
    have hcount' : P.boundedCount = 0 := by omega
    have hanchor : P.firstAnchor = P.secondAnchor := by
      unfold Region.firstAnchor Region.secondAnchor
      congr 1
      apply Fin.ext
      exact hcount'.symm
    have hs := P.first_support (embed g) hg
    rw [← hanchor]
    dsimp [realDet, embed] at hs
    simp only [det, Prod.fst_sub, Prod.snd_sub, Region.firstAnchor]
    exact_mod_cast hs

private theorem second_row_mem {v w : Lattice} (P : Region v w) (z : Lattice)
    (hrow : det w z = det w P.secondAnchor)
    (hpred : 0 ≤ det P.predecessor (z - P.secondAnchor)) : z ∈ P.lattice := by
  let u := embed P.predecessor
  let y := embed z - embed P.secondAnchor
  let r := realDet u (embed w)
  have hr : 0 < r := by
    have hh : (0 : ℝ) < (det P.predecessor w : ℝ) := by
      exact_mod_cast predecessor_turn P
    simpa [r, u, realDet, det, embed] using hh
  have hy : 0 ≤ realDet u y := by
    have hh : (0 : ℝ) ≤ (det P.predecessor (z - P.secondAnchor) : ℝ) := by
      exact_mod_cast hpred
    simpa [u, y, realDet, det, embed] using hh
  have hcol : realDet (embed w) y = 0 := by
    dsimp [realDet, y, embed, det] at hrow ⊢
    exact_mod_cast (by nlinarith [hrow] :
      w.1 * (z.2 - P.secondAnchor.2) - w.2 * (z.1 - P.secondAnchor.1) = 0)
  have heq : y = (realDet u y / r) • embed w := by
    have hr0 : r ≠ 0 := ne_of_gt hr
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    all_goals
      field_simp
      dsimp [r, realDet] at *
      first
      | linear_combination -u.1 * hcol
      | linear_combination -u.2 * hcol
  have hm := second_ray_mem P (realDet u y / r) (div_nonneg hy hr.le)
  have hz : embed z = embed P.secondAnchor + (realDet u y / r) • embed w := by
    rw [← heq]
    dsimp [y]
    abel
  change embed z ∈ P.carrier
  rwa [← hz] at hm

theorem region_enlargement_zero {v w : Lattice} (P : Region v w) :
    P.enlargement 0 = P.lattice := by
  apply Set.Subset.antisymm
  · rintro z ⟨g, hg, t, rfl, hrow⟩
    rcases hrow with hmem | ⟨hlow, hhigh⟩
    · exact hmem
    · apply second_row_mem P
      · simpa using le_antisymm hhigh (by simpa using hlow)
      · have hs := predecessor_support P g hg
        have heq : det P.predecessor
            (g + (t : ℤ) • P.predecessor - P.secondAnchor) =
            det P.predecessor (g - P.secondAnchor) := by
          simp [det, smul_eq_mul]
          ring
        rwa [heq]
  · intro z hz
    exact ⟨z, hz, 0, by simp, Or.inl hz⟩

theorem region_overlap_to_forward {v w : Lattice} (P : Region v w)
    (x : Configuration ℤ) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpv : OverlapHasPeriod x P.lattice (a • v))
    (hpw : OverlapHasPeriod x P.lattice (b • w)) :
    FullPeriods x P.lattice ((-(a.natAbs : ℤ)) • v) ((b.natAbs : ℤ) • w) := by
  have hpa : OverlapHasPeriod x P.lattice ((-(a.natAbs : ℤ)) • v) := by
    by_cases hsign : 0 ≤ a
    · rw [Int.natCast_natAbs, abs_of_nonneg hsign, neg_smul]
      exact overlap_neg x P.lattice (a • v) hpv
    · rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hsign), neg_neg]
      exact hpv
  have hpb : OverlapHasPeriod x P.lattice ((b.natAbs : ℤ) • w) := by
    by_cases hsign : 0 ≤ b
    · rw [Int.natCast_natAbs, abs_of_nonneg hsign]
      exact hpw
    · rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hsign), neg_smul]
      exact overlap_neg x P.lattice (b • w) hpw
  have hfa := lattice_forward_first P a.natAbs
  have hfb := lattice_forward_second P b.natAbs
  refine ⟨⟨P.firstAnchor, ?_⟩, ?_, hfa, hfb,
    (fun z hz => hpa z hz (hfa z hz)), (fun z hz => hpb z hz (hfb z hz))⟩
  · simpa [Region.lattice] using first_ray_mem P 0 le_rfl
  · have ha' : (a.natAbs : ℤ) ≠ 0 := by simpa using ha
    have hb' : (b.natAbs : ℤ) ≠ 0 := by simpa using hb
    have heq : det ((-(a.natAbs : ℤ)) • v) ((b.natAbs : ℤ) • w) =
        -(a.natAbs : ℤ) * (b.natAbs : ℤ) * det v w := by
      simp [det, smul_eq_mul]
      ring
    change det _ _ ≠ 0
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha') hb') (ne_of_gt P.turn_positive)

end ConvexNivat.Colle
