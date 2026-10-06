import Mathlib

namespace ConvexNivat
noncomputable section

def realOpenCut {n : ℕ} (b : Fin n → ℝ) (l : ℕ) : Set ℝ :=
  {t | (∀ r : Fin n, r.val < l → b r < t) ∧
    (∀ r : Fin n, l ≤ r.val → t < b r)}

def realWeakCut {n : ℕ} (b : Fin n → ℝ) (l : ℕ) : Set ℝ :=
  {t | (∀ r : Fin n, r.val < l → b r ≤ t) ∧
    (∀ r : Fin n, l ≤ r.val → t ≤ b r)}

def realCutCount {n : ℕ} (b : Fin n → ℝ) (t : ℝ) : ℕ :=
  @Finset.card _ (@Finset.filter _ (fun r => b r < t)
    (fun _ => Classical.propDecidable _) Finset.univ)

theorem sector_interval_partition {n : ℕ} (b : Fin n → ℝ) (hb : StrictMono b) :
    (∀ l : Fin (n + 1), (realOpenCut b l.val).Nonempty) ∧
    (∀ l k : Fin (n + 1), l ≠ k →
      Disjoint (realOpenCut b l.val) (realOpenCut b k.val)) ∧
    (∀ t : ℝ, (∀ r : Fin n, t ≠ b r) →
      ∃! l : Fin (n + 1), t ∈ realOpenCut b l.val ∧ l.val = realCutCount b t) ∧
    (∀ (r : Fin n) (l : Fin (n + 1)),
      b r ∈ realWeakCut b l.val ↔ l.val = r.val ∨ l.val = r.val + 1) := by
  classical
  have hne (l : Fin (n + 1)) : (realOpenCut b l.val).Nonempty := by
    by_cases hn : n = 0
    · subst n
      exact ⟨0, by constructor <;> intro r <;> exact Fin.elim0 r⟩
    by_cases hl : l.val = 0
    · let r : Fin n := ⟨0, by omega⟩
      refine ⟨b r - 1, ?_, ?_⟩
      · intro s hs
        omega
      · intro s hs
        have hbs := hb.monotone (show r ≤ s by exact Nat.zero_le _)
        linarith
    by_cases hln : l.val = n
    · let r : Fin n := ⟨n - 1, by omega⟩
      refine ⟨b r + 1, ?_, ?_⟩
      · intro s hs
        have hbs := hb.monotone (show s ≤ r by change s.val ≤ n - 1; omega)
        linarith
      · intro s hs
        omega
    · let r : Fin n := ⟨l.val - 1, by omega⟩
      let s : Fin n := ⟨l.val, by omega⟩
      have hrs : b r < b s := hb (show r < s by change l.val - 1 < l.val; omega)
      refine ⟨(b r + b s) / 2, ?_, ?_⟩
      · intro q hq
        have hbr := hb.monotone (show q ≤ r by change q.val ≤ l.val - 1; omega)
        linarith
      · intro q hq
        have hbs := hb.monotone (show s ≤ q by exact hq)
        linarith
  have hdis (l k : Fin (n + 1)) (hlk : l ≠ k) :
      Disjoint (realOpenCut b l.val) (realOpenCut b k.val) := by
    apply Set.disjoint_left.mpr
    intro t ht htk
    rcases lt_or_gt_of_ne (show l.val ≠ k.val from fun h => hlk (Fin.ext h)) with h | h
    · let r : Fin n := ⟨l.val, by omega⟩
      have h1 := ht.2 r (by exact le_rfl)
      have h2 := htk.1 r h
      linarith
    · let r : Fin n := ⟨k.val, by omega⟩
      have h1 := htk.2 r (by exact le_rfl)
      have h2 := ht.1 r h
      linarith
  refine ⟨hne, hdis, ?_, ?_⟩
  · intro t ht
    have hc : realCutCount b t ≤ n := by
      unfold realCutCount
      exact (Finset.card_filter_le _ _).trans (by simp)
    let l : Fin (n + 1) := ⟨realCutCount b t, by omega⟩
    have hcrit (r : Fin n) : r.val < realCutCount b t ↔ b r < t :=
      Fin.lt_card_filter_univ_iff_apply_of_imp (fun r : Fin n => b r < t)
        (fun i j hji hi => lt_of_le_of_lt (hb.monotone hji) hi)
    have hmem : t ∈ realOpenCut b l.val := by
      constructor
      · intro r hr
        exact (hcrit r).mp hr
      · intro r hr
        have hn : ¬ b r < t := fun h => Nat.not_lt_of_ge hr ((hcrit r).mpr h)
        exact lt_of_le_of_ne (le_of_not_gt hn) (ht r)
    refine ⟨l, ⟨hmem, rfl⟩, ?_⟩
    intro k hk
    apply Fin.ext
    exact hk.2
  · intro r l
    constructor
    · intro h
      have hlo : r.val ≤ l.val := by
        by_contra hn
        let q : Fin n := ⟨l.val, by omega⟩
        have hbr := hb (show q < r by change l.val < r.val; omega)
        have hq := h.2 q (by exact le_rfl)
        linarith
      have hhi : l.val ≤ r.val + 1 := by
        by_contra hn
        let q : Fin n := ⟨r.val + 1, by omega⟩
        have hbr := hb (show r < q by change r.val < r.val + 1; omega)
        have hq := h.1 q (by change r.val + 1 < l.val; omega)
        linarith
      omega
    · intro h
      constructor
      · intro q hq
        exact hb.monotone (show q ≤ r by rcases h with h | h <;> change q.val ≤ r.val <;> omega)
      · intro q hq
        exact hb.monotone (show r ≤ q by rcases h with h | h <;> change r.val ≤ q.val <;> omega)

end
end ConvexNivat
