import ConvexNivat.ReductionDefinitions
import ConvexNivat.CoreLattice

namespace ConvexNivat

/-- 8.15: every nonempty remaining set has an available geometric direction. -/
theorem lemma8_15 (p : ℕ) (hp : p.Prime) (θ : Configuration (ZMod p))
    (D : FirstHalfPlaneData p θ) (O : Finset (Fin D.length))
    (hO : O.Nonempty) (K : TailInventory D O) :
    ∃ b ∈ O, ∃ c : Fin D.length, c ≠ b ∧ ∃ d : Lattice,
      d ≠ 0 ∧ (∃ z : Lattice, d = (K.scale : ℤ) • z) ∧
      det (D.direction c) d = 0 ∧ det (D.direction b) d < 0 ∧
      ∀ j, j ≠ b → j ≠ c → SafeDirection D O d j := by
  classical
  obtain ⟨a, e, hae, hcone⟩ := D.sector
  let w := a + e
  have hpos (i : Fin D.length) : 0 < realDet (embed (D.direction i)) w := by
    have ha : a ∈ D.cone := by rw [hcone]; exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
    have he : e ∈ D.cone := by rw [hcone]; exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
    have hia := D.cone_upper i ha
    have hie := D.cone_upper i he
    change 0 ≤ realDet (embed (D.direction i)) a at hia
    change 0 ≤ realDet (embed (D.direction i)) e at hie
    have hadd : realDet (embed (D.direction i)) w =
        realDet (embed (D.direction i)) a + realDet (embed (D.direction i)) e := by
      simp [w, realDet]; ring
    rw [hadd]
    by_contra h
    have hz₁ : realDet (embed (D.direction i)) a = 0 := by linarith
    have hz₂ : realDet (embed (D.direction i)) e = 0 := by linarith
    have hx : (embed (D.direction i)).1 * realDet a e = 0 := by
      simp only [realDet] at hz₁ hz₂ ⊢
      linear_combination a.1 * hz₂ - e.1 * hz₁
    have hy : (embed (D.direction i)).2 * realDet a e = 0 := by
      simp only [realDet] at hz₁ hz₂ ⊢
      linear_combination a.2 * hz₂ - e.2 * hz₁
    have hx' := (mul_eq_zero.mp hx).resolve_right hae
    have hy' := (mul_eq_zero.mp hy).resolve_right hae
    have hzero : D.direction i = 0 := by
      apply Prod.ext <;> apply Int.cast_injective (α := ℝ)
      · simpa [embed] using hx'
      · simpa [embed] using hy'
    exact primitive_ne_zero _ (D.primitive i) hzero
  have hw : 0 < realDot w w := by
    have hzero : w ≠ 0 := by
      intro hz
      obtain ⟨i, hi⟩ := hO
      simpa [hz, realDet] using hpos i
    have hcoords : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
      by_contra h; push Not at h
      exact hzero (Prod.ext h.1 h.2)
    rcases hcoords with h | h
    · have := sq_pos_of_ne_zero h
      dsimp [realDot]; nlinarith [sq_nonneg w.2]
    · have := sq_pos_of_ne_zero h
      dsimp [realDot]; nlinarith [sq_nonneg w.1]
  let t (i : Fin D.length) := realDot (embed (D.direction i)) w /
    realDet (embed (D.direction i)) w
  have hlt (i j : Fin D.length) : t i < t j ↔ 0 < det (D.direction i) (D.direction j) := by
    have hidentity : realDet (embed (D.direction i)) (embed (D.direction j)) *
        realDot w w = realDet (embed (D.direction i)) w *
        realDot (embed (D.direction j)) w - realDot (embed (D.direction i)) w *
        realDet (embed (D.direction j)) w := by
      simp only [realDot, realDet]; ring
    have hcast : realDet (embed (D.direction i)) (embed (D.direction j)) =
        (det (D.direction i) (D.direction j) : ℝ) := by simp [realDet, embed, det]
    dsimp [t]
    rw [div_lt_div_iff₀ (hpos i) (hpos j)]
    rw [hcast] at hidentity
    constructor
    · intro h
      have hprod : 0 < (det (D.direction i) (D.direction j) : ℝ) * realDot w w := by nlinarith
      have hd := (mul_pos_iff_of_pos_right hw).mp hprod
      exact_mod_cast hd
    · intro h
      have hd : 0 < (det (D.direction i) (D.direction j) : ℝ) := by exact_mod_cast h
      have := mul_pos hd hw
      nlinarith
  have htne (i j : Fin D.length) (hij : i ≠ j) : t i ≠ t j := by
    intro heq
    have hd := D.distinct_directions hij
    change det (D.direction i) (D.direction j) ≠ 0 at hd
    have hnotpos : ¬ 0 < det (D.direction i) (D.direction j) := by
      intro h; exact (lt_irrefl (t i)) (heq ▸ (hlt i j).mpr h)
    have hnotneg : ¬ 0 < det (D.direction j) (D.direction i) := by
      intro h; exact (lt_irrefl (t j)) (heq.symm ▸ (hlt j i).mpr h)
    have hswap : det (D.direction j) (D.direction i) = -det (D.direction i) (D.direction j) := by
      simp [det]; ring
    rw [hswap] at hnotneg
    omega
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image O t hO
  let S := Finset.univ.filter fun j => t b < t j
  have hscale : 0 < (K.scale : ℤ) := by exact_mod_cast K.positive_scale
  by_cases hS : S.Nonempty
  · obtain ⟨c, hc, hcmin⟩ := Finset.exists_min_image S t hS
    have hbc : t b < t c := (Finset.mem_filter.mp hc).2
    have hcb : c ≠ b := by intro heq; subst c; exact lt_irrefl _ hbc
    let d := (K.scale : ℤ) • (-D.direction c)
    have hdet (j : Fin D.length) : det (D.direction j) d =
        -(K.scale : ℤ) * det (D.direction j) (D.direction c) := by
      simp [d, det]; ring
    refine ⟨b, hb, c, hcb, d, ?_, ⟨-D.direction c, rfl⟩, ?_, ?_, ?_⟩
    · intro hz
      have hn := primitive_ne_zero _ (D.primitive c)
      have hmul : (K.scale : ℤ) • (-D.direction c) = 0 := hz
      have hcoord₁ := congrArg Prod.fst hmul
      have hcoord₂ := congrArg Prod.snd hmul
      simp at hcoord₁ hcoord₂
      have hx := hcoord₁.resolve_left (Nat.ne_of_gt K.positive_scale)
      have hy := hcoord₂.resolve_left (Nat.ne_of_gt K.positive_scale)
      exact hn (Prod.ext hx hy)
    · have hself : det (D.direction c) (D.direction c) = 0 := by unfold det; ring
      rw [hdet, hself, mul_zero]
    · rw [hdet]
      exact mul_neg_of_neg_of_pos (by omega) ((hlt b c).mp hbc)
    · intro j hjb hjc
      by_cases hj : j ∈ O
      · have hbjl : t b < t j := lt_of_le_of_ne (hbmin j hj) (htne b j hjb.symm)
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbjl⟩
        have hcjl : t c < t j := lt_of_le_of_ne (hcmin j hjS) (htne c j hjc.symm)
        left
        rw [hdet]
        have hdj := (hlt c j).mp hcjl
        have hswap : det (D.direction j) (D.direction c) = -det (D.direction c) (D.direction j) := by
          simp [det]; ring
        rw [hswap]
        nlinarith
      · have hdne : det (D.direction j) d ≠ 0 := by
          rw [hdet]
          exact mul_ne_zero (by omega) (D.distinct_directions hjc)
        rcases lt_or_gt_of_ne hdne with h | h
        · exact Or.inr ⟨hj, h⟩
        · exact Or.inl h
  · obtain ⟨c, hcb⟩ : ∃ c : Fin D.length, c ≠ b := by
      have hlen := D.at_least_two
      by_cases hbzero : b = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by intro h; have := congrArg Fin.val (h.trans hbzero); simp at this⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm hbzero⟩
    have hcbt : t c < t b := by
      have hnot : ¬ t b < t c := by
        intro h; exact hS ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      exact lt_of_le_of_ne (le_of_not_gt hnot) (htne c b hcb)
    let d := (K.scale : ℤ) • D.direction c
    have hdet (j : Fin D.length) : det (D.direction j) d =
        (K.scale : ℤ) * det (D.direction j) (D.direction c) := by
      simp [d, det]; ring
    refine ⟨b, hb, c, hcb, d, ?_, ⟨D.direction c, rfl⟩, ?_, ?_, ?_⟩
    · intro hz
      have hneg : det (D.direction b) d < 0 := by
        rw [hdet]
        have hd := (hlt c b).mp hcbt
        have hs : det (D.direction b) (D.direction c) = -det (D.direction c) (D.direction b) := by
          simp [det]; ring
        rw [hs]; nlinarith
      simp [hz, det] at hneg
    · have hself : det (D.direction c) (D.direction c) = 0 := by unfold det; ring
      rw [hdet, hself, mul_zero]
    · rw [hdet]
      have hd := (hlt c b).mp hcbt
      have hs : det (D.direction b) (D.direction c) = -det (D.direction c) (D.direction b) := by
        simp [det]; ring
      rw [hs]; nlinarith
    · intro j hjb hjc
      have hj : j ∉ O := by
        intro hj
        have hbjl : t b < t j := lt_of_le_of_ne (hbmin j hj) (htne b j hjb.symm)
        exact hS ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbjl⟩⟩
      have hdne : det (D.direction j) d ≠ 0 := by
        rw [hdet]
        exact mul_ne_zero (ne_of_gt hscale) (D.distinct_directions hjc)
      rcases lt_or_gt_of_ne hdne with h | h
      · exact Or.inr ⟨hj, h⟩
      · exact Or.inl h

end ConvexNivat
