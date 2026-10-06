import ConvexNivat.Colle.Definitions

namespace ConvexNivat.Colle
noncomputable section

private theorem detR_add_right (p x y : RealPlane) :
    realDet p (x + y) = realDet p x + realDet p y := by
  simp only [realDet, Prod.fst_add, Prod.snd_add]
  ring

private theorem detR_sub_right (p x y : RealPlane) :
    realDet p (x - y) = realDet p x - realDet p y := by
  simp only [realDet, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem detR_smul_right (p x : RealPlane) (r : ℝ) :
    realDet p (r • x) = r * realDet p x := by
  simp only [realDet, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private theorem detR_embed (p x : Lattice) : realDet (embed p) (embed x) = (det p x : ℝ) := by
  simp [realDet, embed, det]

private theorem real_parallel (p y : RealPlane) (hp : p ≠ 0)
    (h : realDet p y = 0) : ∃ c : ℝ, y = c • p := by
  by_cases h1 : p.1 = 0
  · have h2 : p.2 ≠ 0 := by
      intro h2
      exact hp (Prod.ext h1 h2)
    refine ⟨y.2 / p.2, ?_⟩
    apply Prod.ext
    · simp only [Prod.smul_fst, smul_eq_mul, h1, mul_zero]
      dsimp [realDet] at h
      rw [h1, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at h
      exact h.resolve_left h2
    · simp only [Prod.smul_snd, smul_eq_mul]
      exact (div_mul_cancel₀ _ h2).symm
  · refine ⟨y.1 / p.1, ?_⟩
    apply Prod.ext
    · simp only [Prod.smul_fst, smul_eq_mul]
      exact (div_mul_cancel₀ _ h1).symm
    · simp only [Prod.smul_snd, smul_eq_mul]
      dsimp [realDet] at h
      apply (mul_right_cancel₀ h1)
      field_simp
      nlinarith

/-- Accumulation of the actual two-direction periodic subregion leaves a
rational half-plane with the second tangent period. -/
theorem regional_ray_limit_halfplane (ξ x : Configuration ℤ) (v w : Lattice)
    (P : Region v w) (hperiod : DirectionalPeriod ξ P.lattice w)
    (hlimit : SubsequentialTranslateLimit ξ w x) :
    DirectionalPeriod x {z | det w P.secondAnchor ≤ det w z} w := by
  have enters (z : Lattice) (hz : det w P.secondAnchor ≤ det w z) :
      ∃ N : ℕ, ∀ t : ℕ, N ≤ t → z + (t : ℤ) • w ∈ P.lattice := by
    let a := embed P.firstAnchor
    let b := embed P.secondAnchor
    let p := embed v
    let q := embed w
    let zz := embed z
    have δpos : 0 < realDet p q := by
      dsimp [p, q]
      rw [detR_embed]
      exact_mod_cast P.turn_positive
    have qne : q ≠ 0 := by
      intro heq
      rw [heq] at δpos
      simp [realDet] at δpos
    have dnonneg : 0 ≤ realDet q (zz - b) := by
      dsimp [q, zz, b]
      rw [detR_sub_right, detR_embed, detR_embed]
      exact_mod_cast sub_nonneg.mpr hz
    let d := realDet q (zz - b)
    let r := realDet q (a - b)
    let c := (|r| + d + 1) / realDet p q
    have cnonneg : 0 ≤ c := by
      apply div_nonneg _ δpos.le
      dsimp [d]
      linarith [abs_nonneg r]
    let A := a - c • p
    have Ain : A ∈ P.carrier := by
      apply P.closed.frontier_subset
      rw [P.boundary_eq]
      exact Or.inl (Or.inl ⟨c, cnonneg, rfl⟩)
    have antisymm : realDet q p = -realDet p q := by dsimp [realDet]; ring
    have Dformula : realDet q (A - b) = r + |r| + d + 1 := by
      have hc : c * realDet p q = |r| + d + 1 := div_mul_cancel₀ _ (ne_of_gt δpos)
      dsimp [A]
      have heq : a - c • p - b = (a - b) - c • p := by abel
      rw [heq, detR_sub_right, detR_smul_right, antisymm]
      dsimp [r] at *
      nlinarith
    have Dgt : d < realDet q (A - b) := by
      rw [Dformula]
      linarith [neg_abs_le r]
    have Dpos : 0 < realDet q (A - b) := lt_of_le_of_lt dnonneg Dgt
    let α := d / realDet q (A - b)
    have αnonneg : 0 ≤ α := div_nonneg dnonneg Dpos.le
    have αlt : α < 1 := (div_lt_one Dpos).mpr Dgt
    have αeq : α * realDet q (A - b) = d := div_mul_cancel₀ _ (ne_of_gt Dpos)
    let X := α • A + (1 - α) • b
    have hdet : realDet q (zz - X) = 0 := by
      dsimp [X]
      rw [detR_sub_right, detR_add_right, detR_smul_right, detR_smul_right]
      dsimp [d] at αeq
      have αeq2 : α * (realDet q A - realDet q b) = realDet q zz - realDet q b := by
        simpa only [detR_sub_right] using αeq
      nlinarith
    obtain ⟨e, he⟩ := real_parallel q (zz - X) qne hdet
    obtain ⟨N, hN⟩ := exists_nat_ge (-e)
    refine ⟨N, ?_⟩
    intro t ht
    have htR : (N : ℝ) ≤ t := by exact_mod_cast ht
    have er : 0 ≤ (e + t) / (1 - α) := div_nonneg (by linarith) (by linarith)
    have Bin : b + ((e + t) / (1 - α)) • q ∈ P.carrier := by
      apply P.closed.frontier_subset
      rw [P.boundary_eq]
      exact Or.inl (Or.inr ⟨(e + t) / (1 - α), er, rfl⟩)
    have hconv := P.convex Ain Bin αnonneg (show 0 ≤ 1 - α by linarith)
      (show α + (1 - α) = 1 by ring)
    have heq : embed (z + (t : ℤ) • w) =
        α • A + (1 - α) • (b + ((e + t) / (1 - α)) • q) := by
      have hzz : zz = X + e • q := by rw [← he]; abel
      have hemb : embed (z + (t : ℤ) • w) = zz + (t : ℝ) • q := by
        ext <;> simp [zz, q, embed]
      rw [hemb, hzz]
      dsimp [X]
      rw [smul_add, smul_smul, mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr αlt))]
      rw [add_smul]
      module
    change embed _ ∈ P.carrier
    rw [heq]
    exact hconv
  rcases hperiod with ⟨_, k, hk, hp⟩
  rcases hlimit with ⟨s, hs, hlim⟩
  refine ⟨⟨P.secondAnchor, by change det w P.secondAnchor ≤ det w P.secondAnchor; exact le_rfl⟩, k, hk, ?_⟩
  intro z hz hzk
  obtain ⟨Nz, hzN⟩ := enters z hz
  obtain ⟨Nk, hkN⟩ := enters (z + k • w) hzk
  obtain ⟨Lz, hzL⟩ := hlim z
  obtain ⟨Lk, hkL⟩ := hlim (z + k • w)
  let j := max (max Nz Nk) (max Lz Lk)
  have hNz : Nz ≤ s j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hs.id_le j)
  have hNk : Nk ≤ s j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hs.id_le j)
  have hLz : Lz ≤ j := le_trans (le_max_left _ _) (le_max_right _ _)
  have hLk : Lk ≤ j := le_trans (le_max_right _ _) (le_max_right _ _)
  have hper := hp (z + (s j : ℤ) • w) (hzN _ hNz)
    (by simpa only [add_right_comm] using hkN _ hNk)
  rw [← hzL j hLz, ← hkL j hLk]
  simpa only [translate, add_right_comm] using hper

end
end ConvexNivat.Colle
