import NivatTrial.MorseHedlund

/-! Quantitative forms of finite-state periodicity and Morse--Hedlund.
The ordinary existence theorem loses the period bound; the strip induction
needs a period no larger than its ambiguity budget. -/

namespace NivatTrial.ColleMorseBound

open NivatTrial.Periodicity NivatTrial.MorseHedlund
open scoped Classical

noncomputable section

variable {X A : Type*} [Fintype X] [Fintype A]

theorem finite_state_periodic_bounded (σ : ℤ → X)
    (hforward : ∀ i j, σ i = σ j → σ (i+1)=σ (j+1))
    (hbackward : ∀ i j, σ i = σ j → σ (i-1)=σ (j-1)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Fintype.card X ∧
      ∀ i : ℤ, σ (i+q)=σ i := by
  let F : Fin (Fintype.card X+1) → X := fun i => σ i.val
  have hnoninj : ¬ Function.Injective F := by
    intro hinj
    have hcard := Fintype.card_le_of_injective F hinj
    simp only [Fintype.card_fin] at hcard
    omega
  simp only [Function.Injective] at hnoninj
  push Not at hnoninj
  obtain ⟨i,j,he,hne⟩ := hnoninj
  have horder : ∃ m n : Fin (Fintype.card X+1),
      m.val<n.val ∧ F m=F n := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨i,j,hij,he⟩
    · exact ⟨j,i,hji,he.symm⟩
  obtain ⟨m,n,hmn,heq⟩ := horder
  let q := n.val-m.val
  have hq : 0<q := Nat.sub_pos_of_lt hmn
  have hqbound : q≤Fintype.card X := by
    have := n.isLt
    dsimp [q]
    omega
  refine ⟨q,hq,hqbound,?_⟩
  intro z
  have hp := finite_state_propagate σ hforward hbackward heq (z-m.val)
  have hcast : (q:ℤ)=(n.val:ℤ)-m.val :=
    Int.ofNat_sub (le_of_lt hmn)
  rw [hcast]
  convert hp.symm using 1 <;> congr 1 <;> omega

theorem morse_hedlund_bounded (ξ : ℤ → A) {n : ℕ}
    (hbound : wordComplexity ξ n ≤ n) :
    ∃ q : ℕ, 0 < q ∧ q ≤ n ∧ IsPeriod ξ (q:ℤ) := by
  obtain ⟨k,hk,hplateau⟩ := plateau_of_diagonal_bound (wordComplexity ξ)
    (wordComplexity_zero ξ) (wordComplexity_monotone ξ) hbound
  have hf : ∀ i j, blockState ξ k i = blockState ξ k j →
      blockState ξ k (i+1) = blockState ξ k (j+1) := by
    intro i j hij
    exact Subtype.ext (plateau_forward_determinacy ξ k hplateau
      (congrArg Subtype.val hij))
  have hb : ∀ i j, blockState ξ k i = blockState ξ k j →
      blockState ξ k (i-1) = blockState ξ k (j-1) := by
    intro i j hij
    exact Subtype.ext (plateau_backward_determinacy ξ k hplateau
      (congrArg Subtype.val hij))
  obtain ⟨q,hq,hqcard,hstate⟩ :=
    finite_state_periodic_bounded (blockState ξ k) hf hb
  have hqk : q ≤ wordComplexity ξ k := by
    simpa [wordComplexity,Nat.card_eq_fintype_card] using hqcard
  have hkn : wordComplexity ξ k ≤ wordComplexity ξ n :=
    wordComplexity_monotone ξ (Nat.le_of_lt hk)
  refine ⟨q,hq,by omega,?_⟩
  intro i
  have hh := prefix_determines ξ k hplateau
    (congrArg Subtype.val (hstate i))
  simpa only [wordAt, Fin.val_zero, Nat.cast_zero, add_zero] using congrFun hh 0

end

end NivatTrial.ColleMorseBound
