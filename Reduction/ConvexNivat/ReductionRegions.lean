import ConvexNivat.ReductionDefinitions
import ConvexNivat.CorePeriods
import ConvexNivat.CoreLattice

namespace ConvexNivat

private theorem region_embed_add (x y : Lattice) : embed (x + y) = embed x + embed y := by
  ext <;> simp [embed]

private theorem region_dot_add (x y : Lattice) (n : RealPlane) :
    realDot (embed (x + y)) n = realDot (embed x) n + realDot (embed y) n := by
  simp [realDot, embed]
  ring

private theorem region_dot_zsmul (x : Lattice) (k : ℤ) (n : RealPlane) :
    realDot (embed (k • x)) n = (k : ℝ) * realDot (embed x) n := by
  simp [realDot, embed, smul_eq_mul]
  ring

private theorem region_inward_direction (H : HalfPlane) :
    ∃ g : Lattice, 0 < realDot (embed g) H.normal := by
  have hn : H.normal.1 ≠ 0 ∨ H.normal.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact H.normal_ne_zero (Prod.ext h.1 h.2)
  rcases hn with h | h
  · rcases lt_or_gt_of_ne h with h | h
    · exact ⟨(-1, 0), by simp [realDot, embed]; linarith⟩
    · exact ⟨(1, 0), by simpa [realDot, embed] using h⟩
  · rcases lt_or_gt_of_ne h with h | h
    · exact ⟨(0, -1), by simp [realDot, embed]; linarith⟩
    · exact ⟨(0, 1), by simpa [realDot, embed] using h⟩

private theorem region_inward_basis (H : HalfPlane) :
    ∃ h k : Lattice, Nonparallel h k ∧
      0 ≤ realDot (embed h) H.normal ∧ 0 ≤ realDot (embed k) H.normal := by
  by_cases h : 0 ≤ H.normal.1 <;> by_cases k : 0 ≤ H.normal.2
  · exact ⟨(1, 0), (0, 1), by norm_num [Nonparallel, det],
      by simpa [realDot, embed] using h, by simpa [realDot, embed] using k⟩
  · exact ⟨(1, 0), (0, -1), by norm_num [Nonparallel, det],
      by simpa [realDot, embed] using h, by simp [realDot, embed]; linarith⟩
  · exact ⟨(-1, 0), (0, 1), by norm_num [Nonparallel, det],
      by simp [realDot, embed]; linarith, by simpa [realDot, embed] using k⟩
  · exact ⟨(-1, 0), (0, -1), by norm_num [Nonparallel, det],
      by simp [realDot, embed]; linarith, by simp [realDot, embed]; linarith⟩

/-- §8.1: translation into a half-plane preserves membership. -/
theorem halfPlane_forwardInvariant (H : HalfPlane) (h : Lattice)
    (hh : 0 ≤ realDot (embed h) H.normal) : ForwardInvariant H.carrier h := by
  intro z hz
  unfold HalfPlane.carrier at hz ⊢
  simp only [Set.mem_ofPred_eq, region_dot_add] at hz ⊢
  cases hs : H.strict <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hz ⊢ <;> linarith

/-- §8.1: a strictly inward direction eventually enters either kind of half-plane. -/
theorem halfPlane_eventually_enters (H : HalfPlane) (g z : Lattice)
    (hg : 0 < realDot (embed g) H.normal) :
    ∃ N : ℕ, ∀ n ≥ N, z + (n : ℤ) • g ∈ H.carrier := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((H.threshold - realDot (embed z) H.normal) /
    realDot (embed g) H.normal)
  refine ⟨N, ?_⟩
  intro n hn
  have hN' := (div_lt_iff₀ hg).mp hN
  have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hnn hg.le
  have hlt : H.threshold < realDot (embed z) H.normal +
      (n : ℝ) * realDot (embed g) H.normal := by linarith
  unfold HalfPlane.carrier
  simp only [Set.mem_ofPred_eq, region_dot_add, region_dot_zsmul, Int.cast_natCast]
  cases H.strict <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
  exact hlt.le

theorem halfPlane_nonempty (H : HalfPlane) : H.carrier.Nonempty := by
  obtain ⟨g, hg⟩ := region_inward_direction H
  obtain ⟨N, hN⟩ := halfPlane_eventually_enters H g 0 hg
  exact ⟨0 + (N : ℤ) • g, hN N le_rfl⟩

theorem latticeRegion_closedHull (R : Set Lattice) (hR : LatticeConvexRegion R) :
    R = embed ⁻¹' closedRealHull R := by
  rcases hR with ⟨C, hclosed, hconvex, hR⟩
  have hsub : embed '' R ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [hR] at hz
  have hHull : closedRealHull R ⊆ C :=
    closure_minimal (convexHull_min hsub hconvex) hclosed
  apply Set.Subset.antisymm
  · intro z hz
    exact subset_closure (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)
  · intro z hz
    rw [hR]
    exact hHull hz

theorem latticeRegion_forward_period_in_cone (R : Set Lattice)
    (hR : LatticeConvexRegion R) (h : Lattice) (hh : ForwardInvariant R h) :
    embed h ∈ regionCone R := by
  have hmaps : Set.MapsTo (fun x : RealPlane => x + embed h)
      (convexHull ℝ (embed '' R)) (convexHull ℝ (embed '' R)) := by
    apply convexHull_min _ ((convex_convexHull ℝ (embed '' R)).translate_preimage_left (embed h))
    rintro _ ⟨z, hz, rfl⟩
    change embed z + embed h ∈ convexHull ℝ (embed '' R)
    rw [← region_embed_add]
    exact subset_convexHull ℝ _ ⟨z + h, hh z hz, rfl⟩
  exact hmaps.closure (by fun_prop)

theorem doublyPeriodic_full_halfPlane {A : Type*} (f : Configuration A)
    (hf : DoublyPeriodic f) (H : HalfPlane) : FullyPeriodicOn f H.carrier := by
  obtain ⟨N, hN, hp⟩ := (doublyPeriodic_iff_grid f).mp hf
  obtain ⟨h, k, hind, hdot, kdot⟩ := region_inward_basis H
  refine ⟨(N : ℤ) • h, (N : ℤ) • k, halfPlane_nonempty H, ?_, ?_, ?_, ?_, ?_⟩
  · have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have heq : det ((N : ℤ) • h) ((N : ℤ) • k) = (N : ℤ) * (N : ℤ) * det h k := by
      simp [det, smul_eq_mul]
      ring
    change det ((N : ℤ) • h) ((N : ℤ) • k) ≠ 0
    rw [heq]
    exact mul_ne_zero (mul_ne_zero hNz hNz) hind
  · apply halfPlane_forwardInvariant
    rw [region_dot_zsmul, Int.cast_natCast]
    exact mul_nonneg (Nat.cast_nonneg _) hdot
  · apply halfPlane_forwardInvariant
    rw [region_dot_zsmul, Int.cast_natCast]
    exact mul_nonneg (Nat.cast_nonneg _) kdot
  · exact fun z _ => hp h z
  · exact fun z _ => hp k z

/-- §8.17(γ): a periodic function vanishing on a half-plane vanishes globally. -/
theorem doublyPeriodic_halfPlane_agreement {A : Type*} (f g : Configuration A)
    (hf : DoublyPeriodic f) (hg : DoublyPeriodic g) (H : HalfPlane)
    (hfg : AgreesOn f g H.carrier) : f = g := by
  obtain ⟨N, hN, hp⟩ := (doublyPeriodic_iff_grid f).mp hf
  obtain ⟨M, hM, hq⟩ := (doublyPeriodic_iff_grid g).mp hg
  obtain ⟨u, hu⟩ := region_inward_direction H
  let d : Lattice := ((N * M : ℕ) : ℤ) • u
  have hd : 0 < realDot (embed d) H.normal := by
    dsimp [d]
    simp only [region_dot_zsmul, Int.cast_mul, Int.cast_natCast]
    exact mul_pos (by exact_mod_cast Nat.mul_pos hN hM) hu
  have hpd : HasPeriod f d := by
    simpa only [d, Nat.cast_mul, smul_smul] using hp ((M : ℤ) • u)
  have hqd : HasPeriod g d := by
    simpa only [d, Nat.cast_mul, smul_smul, mul_comm] using hq ((N : ℤ) • u)
  funext z
  obtain ⟨n, hn⟩ := halfPlane_eventually_enters H d z hd
  exact ((hasPeriod_zsmul f d hpd n) z).symm.trans
    ((hfg _ (hn n le_rfl)).trans ((hasPeriod_zsmul g d hqd n) z))

end ConvexNivat
