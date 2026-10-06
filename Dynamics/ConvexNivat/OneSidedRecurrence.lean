import Mathlib

open scoped BigOperators

namespace ConvexNivat

/-- The extremal-row recurrence argument in the proof of Lemma 2.3.
A nonzero bi-infinite sequence supported on one side cannot satisfy a nonzero
finite Laurent recurrence. The same cutoff is used for either orientation. -/
theorem one_sided_recurrence_zero (g : ℤ →₀ ℂ) (c : ℤ → ℂ)
    (hc : ∃ t, c t ≠ 0)
    (hside : ∃ b : ℤ, (∀ t, b < t → c t = 0) ∨
      (∀ t, t < b → c t = 0))
    (hrec : ∀ t : ℤ, ∑ β ∈ g.support, g β * c (t + β) = 0) :
    g = 0 := by
  classical
  by_contra hg
  have hs : g.support.Nonempty := Finsupp.support_nonempty_iff.mpr hg
  obtain ⟨b, hupper | hlower⟩ := hside
  · obtain ⟨t₀, ht₀, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun t => c t ≠ 0)
      ⟨b, fun t ht => le_of_not_gt (fun hgt => ht (hupper t hgt))⟩ hc
    let β := g.support.min' hs
    have hβ : β ∈ g.support := Finset.min'_mem _ _
    have hgβ : g β ≠ 0 := Finsupp.mem_support_iff.mp hβ
    have hsum : (∑ j ∈ g.support, g j * c (t₀ - β + j)) = g β * c t₀ := by
      calc
        (∑ j ∈ g.support, g j * c (t₀ - β + j)) =
            g β * c (t₀ - β + β) := by
          apply Finset.sum_eq_single β
          · intro j hj hjβ
            have hβj : β ≤ j := Finset.min'_le _ _ hj
            have hcj : c (t₀ - β + j) = 0 := by
              by_contra hne
              have hle := hmax (t₀ - β + j) hne
              omega
            rw [hcj, mul_zero]
          · intro hnot
            exact (hnot hβ).elim
        _ = g β * c t₀ := by rw [sub_add_cancel]
    have hzero := hrec (t₀ - β)
    rw [hsum] at hzero
    exact (mul_ne_zero hgβ ht₀) hzero
  · obtain ⟨t₀, ht₀, hmin⟩ := Int.exists_least_of_bdd
      (P := fun t => c t ≠ 0)
      ⟨b, fun t ht => le_of_not_gt (fun hlt => ht (hlower t hlt))⟩ hc
    let β := g.support.max' hs
    have hβ : β ∈ g.support := Finset.max'_mem _ _
    have hgβ : g β ≠ 0 := Finsupp.mem_support_iff.mp hβ
    have hsum : (∑ j ∈ g.support, g j * c (t₀ - β + j)) = g β * c t₀ := by
      calc
        (∑ j ∈ g.support, g j * c (t₀ - β + j)) =
            g β * c (t₀ - β + β) := by
          apply Finset.sum_eq_single β
          · intro j hj hjβ
            have hjβle : j ≤ β := Finset.le_max' _ _ hj
            have hcj : c (t₀ - β + j) = 0 := by
              by_contra hne
              have hle := hmin (t₀ - β + j) hne
              omega
            rw [hcj, mul_zero]
          · intro hnot
            exact (hnot hβ).elim
        _ = g β * c t₀ := by rw [sub_add_cancel]
    have hzero := hrec (t₀ - β)
    rw [hsum] at hzero
    exact (mul_ne_zero hgβ ht₀) hzero

end ConvexNivat
