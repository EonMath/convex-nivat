import NivatTrial.ColleGenerating

/-! The one-sided Morse--Hedlund principle needed for Colle's semi-ambiguous
half-strips. Tail words are counted only at starts beyond a fixed threshold. -/

namespace NivatTrial.ColleTailWords

open NivatTrial.MorseHedlund
open scoped Classical

noncomputable section

variable {A : Type*} [Fintype A]

def tailWordSet (ξ : ℤ → A) (n : ℕ) (τ : ℤ) : Set (Fin n → A) :=
  {w | ∃ i : ℤ, τ ≤ i ∧ w = wordAt ξ n i}

instance tailWordSetFintype (ξ : ℤ → A) (n : ℕ) (τ : ℤ) :
    Fintype (tailWordSet ξ n τ) := Fintype.ofFinite _

def tailWordComplexity (ξ : ℤ → A) (n : ℕ) (τ : ℤ) : ℕ :=
  Nat.card (tailWordSet ξ n τ)

theorem tailWordComplexity_zero (ξ : ℤ → A) (τ : ℤ) :
    tailWordComplexity ξ 0 τ = 1 := by
  letI : Unique (tailWordSet ξ 0 τ) :=
    { default := ⟨wordAt ξ 0 τ, ⟨τ, le_rfl, rfl⟩⟩
      uniq := fun _ => Subsingleton.elim _ _ }
  rw [tailWordComplexity, Nat.card_eq_fintype_card]
  exact Fintype.card_unique

def tailPrefixMap (ξ : ℤ → A) (n : ℕ) (τ : ℤ) :
    tailWordSet ξ (n + 1) τ → tailWordSet ξ n τ :=
  fun p => ⟨blockPrefix p.val, by
    obtain ⟨i, hi, hp⟩ := p.property
    exact ⟨i, hi, by rw [hp]; exact prefix_wordAt ξ n i⟩⟩

theorem tailPrefixMap_surjective (ξ : ℤ → A) (n : ℕ) (τ : ℤ) :
    Function.Surjective (tailPrefixMap ξ n τ) := by
  rintro ⟨p, i, hi, rfl⟩
  exact ⟨⟨wordAt ξ (n + 1) i, ⟨i, hi, rfl⟩⟩, rfl⟩

theorem tailWordComplexity_step (ξ : ℤ → A) (n : ℕ) (τ : ℤ) :
    tailWordComplexity ξ n τ ≤ tailWordComplexity ξ (n + 1) τ := by
  simpa [tailWordComplexity, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective _ (tailPrefixMap_surjective ξ n τ)

theorem tailWordComplexity_monotone (ξ : ℤ → A) (τ : ℤ) :
    Monotone (fun n => tailWordComplexity ξ n τ) :=
  monotone_nat_of_le_succ (fun n => tailWordComplexity_step ξ n τ)

theorem tailPrefixMap_injective_of_plateau (ξ : ℤ → A) (n : ℕ) (τ : ℤ)
    (hcard : tailWordComplexity ξ n τ = tailWordComplexity ξ (n + 1) τ) :
    Function.Injective (tailPrefixMap ξ n τ) := by
  exact ((Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨tailPrefixMap_surjective ξ n τ,
      by simpa [tailWordComplexity, Nat.card_eq_fintype_card] using hcard.symm⟩).1

theorem tail_prefix_determines (ξ : ℤ → A) (n : ℕ) (τ : ℤ)
    (hcard : tailWordComplexity ξ n τ = tailWordComplexity ξ (n + 1) τ)
    {i j : ℤ} (hi : τ ≤ i) (hj : τ ≤ j)
    (hij : wordAt ξ n i = wordAt ξ n j) :
    wordAt ξ (n + 1) i = wordAt ξ (n + 1) j := by
  have h := tailPrefixMap_injective_of_plateau ξ n τ hcard
    (show tailPrefixMap ξ n τ
      ⟨wordAt ξ (n + 1) i, ⟨i, hi, rfl⟩⟩ =
      tailPrefixMap ξ n τ
        ⟨wordAt ξ (n + 1) j, ⟨j, hj, rfl⟩⟩ from Subtype.ext hij)
  exact congrArg Subtype.val h

theorem tail_forward_determines (ξ : ℤ → A) (n : ℕ) (τ : ℤ)
    (hcard : tailWordComplexity ξ n τ = tailWordComplexity ξ (n + 1) τ)
    {i j : ℤ} (hi : τ ≤ i) (hj : τ ≤ j)
    (hij : wordAt ξ n i = wordAt ξ n j) :
    wordAt ξ n (i + 1) = wordAt ξ n (j + 1) := by
  have h := congrArg (suffix (n := n))
    (tail_prefix_determines ξ n τ hcard hi hj hij)
  simpa only [suffix_wordAt] using h

/-- A finite state sequence with a forward transition rule eventually cycles. -/
theorem finite_forward_eventually_periodic {X : Type*} [Finite X]
    (σ : ℕ → X)
    (hforward : ∀ i j, σ i = σ j → σ (i + 1) = σ (j + 1)) :
    ∃ N q : ℕ, 0 < q ∧ ∀ k ≥ N, σ (k + q) = σ k := by
  obtain ⟨m, n, hmn, hne⟩ := Function.not_injective_iff.mp
    (not_injective_infinite_finite σ)
  wlog hlt : m < n generalizing m n
  · exact this n m hmn.symm hne.symm (lt_of_le_of_ne (le_of_not_gt hlt) hne.symm)
  have hprop : ∀ k : ℕ, σ (m + k) = σ (n + k) := by
    intro k
    induction k with
    | zero => simpa using hmn
    | succ k ih =>
      simpa only [Nat.add_succ] using hforward (m + k) (n + k) ih
  refine ⟨m, n - m, Nat.sub_pos_of_lt hlt, ?_⟩
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := hprop d
  convert h.symm using 1 <;> congr 1 <;> omega

theorem tail_periodic_of_plateau (ξ : ℤ → A) (n : ℕ) (τ : ℤ)
    (hcard : tailWordComplexity ξ n τ = tailWordComplexity ξ (n + 1) τ) :
    ∃ N q : ℕ, 0 < q ∧
      ∀ i : ℤ, τ + N ≤ i → ξ (i + q) = ξ i := by
  let σ : ℕ → (Fin n → A) := fun k => wordAt ξ n (τ + k)
  have hf : ∀ i j, σ i = σ j → σ (i + 1) = σ (j + 1) := by
    intro i j hij
    have hi : τ ≤ τ + (i : ℤ) := by omega
    have hj : τ ≤ τ + (j : ℤ) := by omega
    have h := tail_forward_determines ξ n τ hcard hi hj hij
    simpa only [σ, Nat.cast_add, Nat.cast_one, add_assoc] using h
  obtain ⟨N, q, hq, hstate⟩ := finite_forward_eventually_periodic σ hf
  refine ⟨N, q, hq, ?_⟩
  intro i hi
  have hik : 0 ≤ i - τ := by omega
  let k : ℕ := (i - τ).toNat
  have hk : τ + (k : ℤ) = i := by
    dsimp [k]
    omega
  have hNk : N ≤ k := by
    dsimp [k]
    omega
  have hs := hstate k hNk
  have hs' : wordAt ξ n i = wordAt ξ n (i + q) := by
    have hcast : τ + ((k + q : ℕ) : ℤ) = i + (q : ℤ) := by omega
    simpa only [σ, hk, hcast] using hs.symm
  have hp := tail_prefix_determines ξ n τ hcard (by omega) (by omega) hs'
  simpa [wordAt] using congrFun hp 0 |>.symm

/-- One-sided Morse--Hedlund on the actual tail language. -/
theorem tail_morse_hedlund (ξ : ℤ → A) (τ : ℤ) {n : ℕ}
    (hbound : tailWordComplexity ξ n τ ≤ n) :
    ∃ N q : ℕ, 0 < q ∧
      ∀ i : ℤ, τ + N ≤ i → ξ (i + q) = ξ i := by
  obtain ⟨k, hk, hplateau⟩ := plateau_of_diagonal_bound
    (fun j => tailWordComplexity ξ j τ)
    (tailWordComplexity_zero ξ τ)
    (tailWordComplexity_monotone ξ τ) hbound
  exact tail_periodic_of_plateau ξ k τ hplateau

end

end NivatTrial.ColleTailWords
