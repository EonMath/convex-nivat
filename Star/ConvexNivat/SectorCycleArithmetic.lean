import Mathlib

namespace ConvexNivat
noncomputable section

def sectorTwoBlockEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (two_mul m).symm)

def sectorTwoBlockRelation (m : ℕ) (a b : Fin m ⊕ Fin m) : Prop :=
  match a, b with
  | .inl j, .inl k => j.val + 1 = k.val ∨ k.val + 1 = j.val
  | .inr j, .inr k => j.val + 1 = k.val ∨ k.val + 1 = j.val
  | .inl j, .inr k =>
      (j.val = m - 1 ∧ k.val = 0) ∨ (j.val = 0 ∧ k.val = m - 1)
  | .inr j, .inl k =>
      (j.val = m - 1 ∧ k.val = 0) ∨ (j.val = 0 ∧ k.val = m - 1)

theorem two_block_cycle_arithmetic (m : ℕ) (hm : 2 ≤ m) :
    (∀ l : Fin m, (sectorTwoBlockEquiv m (.inl l)).val = l.val) ∧
    (∀ l : Fin m, (sectorTwoBlockEquiv m (.inr l)).val = m + l.val) ∧
    (∀ j k : Fin (2 * m),
      sectorTwoBlockRelation m ((sectorTwoBlockEquiv m).symm j)
        ((sectorTwoBlockEquiv m).symm k) ↔
        ((j.val + 1) % (2 * m) = k.val ∨ (k.val + 1) % (2 * m) = j.val)) := by
  have hl (l : Fin m) : (sectorTwoBlockEquiv m (.inl l)).val = l.val := by
    simp [sectorTwoBlockEquiv]
  have hr (l : Fin m) : (sectorTwoBlockEquiv m (.inr l)).val = m + l.val := by
    simp [sectorTwoBlockEquiv, Nat.add_comm]
  have hmod (a : Fin m) : (m + a.val + 1) % (2 * m) =
      if a.val + 1 = m then 0 else m + a.val + 1 := by
    by_cases h : a.val + 1 = m
    · rw [if_pos h]
      have he : m + a.val + 1 = 2 * m := by omega
      rw [he, Nat.mod_self]
    · rw [if_neg h]
      exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hl, hr, ?_⟩
  intro j k
  obtain ⟨a, rfl⟩ := (sectorTwoBlockEquiv m).surjective j
  obtain ⟨b, rfl⟩ := (sectorTwoBlockEquiv m).surjective k
  simp only [Equiv.symm_apply_apply]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp only [sectorTwoBlockRelation, hl]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    | inr b =>
      simp only [sectorTwoBlockRelation, hl, hr]
      by_cases hb : b.val + 1 = m
      · have hmod : (m + b.val + 1) % (2 * m) = 0 := by
          have he : m + b.val + 1 = 2 * m := by omega
          rw [he, Nat.mod_self]
        rw [Nat.mod_eq_of_lt (by omega), hmod]
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  | inr a =>
    cases b with
    | inl b =>
      simp only [sectorTwoBlockRelation, hl, hr]
      by_cases ha : a.val + 1 = m
      · have hmod : (m + a.val + 1) % (2 * m) = 0 := by
          have he : m + a.val + 1 = 2 * m := by omega
          rw [he, Nat.mod_self]
        rw [hmod, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    | inr b =>
      simp only [sectorTwoBlockRelation, hr]
      rw [hmod a, hmod b]
      by_cases ha : a.val + 1 = m <;> by_cases hb : b.val + 1 = m
      all_goals
        simp only [ha, hb, if_true, if_false]
        omega

end
end ConvexNivat
