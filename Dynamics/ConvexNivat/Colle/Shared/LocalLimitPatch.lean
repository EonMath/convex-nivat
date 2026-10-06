import ConvexNivat.Colle.Shared.Definitions

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

private theorem second_ray_entry {v w : Lattice} (P : Region v w) (z : Lattice) (hz : det w P.secondAnchor ≤ det w z) :
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


private theorem finite_eventual {α : Type*} (F : Finset α) (Q : α → ℕ → Prop)
    (hQ : ∀ q ∈ F, ∃ N, ∀ j ≥ N, Q q j) :
    ∃ N, ∀ q ∈ F, ∀ j ≥ N, Q q j := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert q F hq ih =>
      obtain ⟨Nq, hNq⟩ := hQ q (Finset.mem_insert_self _ _)
      obtain ⟨NF, hNF⟩ := ih (fun p hp => hQ p (Finset.mem_insert_of_mem hp))
      refine ⟨max Nq NF, ?_⟩
      intro p hp j hj
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hNq j (le_trans (le_max_left _ _) hj)
      · exact hNF p hp j (le_trans (le_max_right _ _) hj)

private theorem enlargement_lower_bound {v w : Lattice} (P : Region v w)
    (n : ℕ) (z : Lattice) (hz : z ∈ P.enlargement n) :
    det w P.secondAnchor - (n : ℤ) ≤ det w z := by
  obtain ⟨g, hg, t, heq, hrow⟩ := hz
  rcases hrow with hrow | hrow
  · have h := P.second_support (embed z) hrow
    have hcast : 0 ≤ det w (z - P.secondAnchor) := by
      dsimp [realDet, embed] at h
      simp only [det, Prod.fst_sub, Prod.snd_sub]
      exact_mod_cast h
    have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    dsimp [det] at hcast ⊢
    nlinarith
  · exact hrow.1

private theorem shifted_patch_agrees {v w : Lattice} (P : Region v w)
    (θ xper x : Configuration ℤ) (n : ℕ) (b : ℤ)
    (hb : b ≤ -((n : ℤ) + 1))
    (hperiod : HasPeriod xper (b • v))
    (hxperiod : HasPeriod x (b • v))
    (hagrees : AgreesOn θ xper (P.enlargement n))
    (s : ℕ → ℕ) (hs : StrictMono s)
    (hlimit : PointwiseLimit (fun j => translate ((s j : ℤ) • w) θ) x)
    (R L : ℕ) :
    ∃ j : ℕ, L ≤ s j ∧
      (∀ q ∈ integerSquare R, ∀ r ∈ integerSquare R,
        r - q = b • v → translate ((s j : ℤ) • w) θ r =
          translate ((s j : ℤ) • w) θ q) ∧
      AgreesOn θ xper (regionalSeed P n R (s j)) := by
  classical
  obtain ⟨Nlim, hNlim⟩ := finite_eventual
    (integerSquare R ∪ (integerSquare R).image (fun q => q + b • v))
    (fun q j => translate ((s j : ℤ) • w) θ q = x q)
    (fun q _ => hlimit q)
  obtain ⟨Nentry, hNentry⟩ := finite_eventual (integerSquare R)
    (fun q t => det w P.secondAnchor - ((n : ℤ) + 1) ≤ det w q →
      q + b • v + (t : ℤ) • w ∈ P.lattice) (by
        intro q hq
        by_cases hqmin : det w P.secondAnchor - ((n : ℤ) + 1) ≤ det w q
        · have hturn : 1 ≤ det v w := P.turn_positive
          have hbw : det w P.secondAnchor ≤ det w (q + b • v) := by
            have hbneg : b ≤ 0 := by omega
            have hmul := mul_le_mul_of_nonpos_left hturn hbneg
            have hdet : det w (q + b • v) = det w q - b * det v w := by
              simp [det, smul_eq_mul]
              ring
            rw [hdet]
            nlinarith
          obtain ⟨N, hN⟩ := second_ray_entry P (q + b • v) hbw
          exact ⟨N, fun t ht _ => hN t ht⟩
        · exact ⟨0, fun t ht h => False.elim (hqmin h)⟩)
  let j := max Nlim (max Nentry L)
  have hjlim : Nlim ≤ j := le_max_left _ _
  have hjentry : Nentry ≤ s j := le_trans
    (le_trans (le_max_left _ _) (le_max_right _ _)) (hs.id_le j)
  have hjL : L ≤ s j := le_trans
    (le_trans (le_max_right _ _) (le_max_right _ _)) (hs.id_le j)
  have hbase (q : Lattice) (hq : q ∈ integerSquare R) :
      translate ((s j : ℤ) • w) θ q = x q :=
    hNlim q (Finset.mem_union_left _ hq) j hjlim
  have hshift (q : Lattice) (hq : q ∈ integerSquare R) :
      translate ((s j : ℤ) • w) θ (q + b • v) = x (q + b • v) :=
    hNlim _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)) j hjlim
  refine ⟨j, hjL, ?_, ?_⟩
  · intro q hq r hr heq
    have hrq : r = q + b • v := by
      rw [sub_eq_iff_eq_add] at heq
      simpa [add_comm] using heq
    rw [hbase r hr, hbase q hq, hrq, hxperiod q]
  · intro z hz
    rcases hz with hz | ⟨hznew, hzsquare⟩
    · exact hagrees z hz
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hzsquare
      have hqmin : det w P.secondAnchor - ((n : ℤ) + 1) ≤ det w q := by
        have hbound := enlargement_lower_bound P (n + 1) (q + (s j : ℤ) • w) hznew
        have hdet : det w (q + (s j : ℤ) • w) = det w q := by
          simp [det, smul_eq_mul]
          ring
        simpa only [hdet, Nat.cast_add, Nat.cast_one] using hbound
      have hentry := hNentry q hq (s j) hjentry hqmin
      have hold : q + b • v + (s j : ℤ) • w ∈ P.enlargement n := by
        exact ⟨_, hentry, 0, by simp, Or.inl hentry⟩
      have hcompare : θ (q + b • v + (s j : ℤ) • w) =
          θ (q + (s j : ℤ) • w) := by
        exact (hshift q hq).trans ((hxperiod q).trans (hbase q hq).symm)
      calc
        θ (q + (s j : ℤ) • w) = θ (q + b • v + (s j : ℤ) • w) := hcompare.symm
        _ = xper (q + b • v + (s j : ℤ) • w) := hagrees _ hold
        _ = xper (q + (s j : ℤ) • w) := by
          simpa only [add_right_comm] using hperiod (q + (s j : ℤ) • w)

theorem local_limit_common_period_patch (ξ θ xper x : Configuration ℤ)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) {v w : Lattice}
    (P : Region v w) (hweak : WeaklyEnveloped S P)
    (hθ : θ ∈ OrbitClosure ξ) (hxper : xper ∈ OrbitClosure ξ)
    (a : ℤ) (ha : a ≠ 0) (hperiod : HasPeriod xper (a • v))
    (n : ℕ) (hagrees : AgreesOn θ xper (P.enlargement n))
    (s : ℕ → ℕ) (hs : StrictMono s)
    (hlimit : PointwiseLimit (fun j => translate ((s j : ℤ) • w) θ) x)
    (hdouble : DoublyPeriodic x) :
    ∃ b : ℤ, b ≠ 0 ∧ a ∣ b ∧ HasPeriod x (b • v) ∧
      ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ L : ℕ, ∃ j : ℕ, L ≤ s j ∧
        (∀ q ∈ integerSquare R, ∀ r ∈ integerSquare R,
          r - q = b • v → translate ((s j : ℤ) • w) θ r =
            translate ((s j : ℤ) • w) θ q) ∧
        AgreesOn θ xper (regionalSeed P n R (s j)) := by
  obtain ⟨k, hk, hkp⟩ := doublyPeriodic_multiple_period x hdouble v
  let b : ℤ := -((a.natAbs : ℤ) * k * ((n : ℤ) + 2))
  have habs : 1 ≤ (a.natAbs : ℤ) := by
    have hp := Int.natAbs_pos.mpr ha
    exact_mod_cast hp
  have hn : 0 < (n : ℤ) + 2 := by positivity
  have hbne : b ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (ne_of_gt (by omega : 0 < (a.natAbs : ℤ)))
      (ne_of_gt (by omega : 0 < k))) (ne_of_gt hn))
  have hdvd : a ∣ b := by
    have hd : a ∣ (a.natAbs : ℤ) := Int.dvd_natAbs.mpr (dvd_refl a)
    exact dvd_neg.mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd k) _)
  have hxp : HasPeriod x (b • v) := by
    have h := hasPeriod_zsmul x (k • v) hkp (-((a.natAbs : ℤ) * ((n : ℤ) + 2)))
    convert h using 1 <;> dsimp [b] <;> rw [smul_smul] <;> congr 1 <;> ring
  have hper : HasPeriod xper (b • v) := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]
    simpa only [smul_smul, mul_comm] using hasPeriod_zsmul xper (a • v) hperiod c
  have hb : b ≤ -((n : ℤ) + 1) := by
    have hprod : 1 ≤ (a.natAbs : ℤ) * k := by nlinarith
    have hscale := mul_le_mul_of_nonneg_right hprod (show 0 ≤ (n : ℤ) + 2 by positivity)
    dsimp [b]
    nlinarith
  refine ⟨b, hbne, hdvd, hxp, 0, ?_⟩
  intro R hR L
  exact shifted_patch_agrees P θ xper x n b hb hper hxp hagrees s hs hlimit R L

end
end ConvexNivat.Colle
