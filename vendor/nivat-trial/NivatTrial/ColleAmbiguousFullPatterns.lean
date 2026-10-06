import NivatTrial.ColleSlantedBlock

/-! A multiplicity bound needed for the nonunique-extension step of the
Cyr–Kra/Colle strip induction: full patterns above ambiguous base patterns
consume at most twice the extension surplus. -/

namespace NivatTrial.ColleAmbiguousFullPatterns

open NivatTrial.Dynamics NivatTrial.ColleAmbiguity
open scoped Classical

noncomputable section

variable {M N : Type*} [Fintype M] [Fintype N]

def ambiguousFull (f : M → N) : Finset M :=
  Finset.univ.filter (fun x => 2 ≤ extensionCount f (f x))

theorem card_ambiguousFull_le_twice_surplus
    (f : M → N) (hf : Function.Surjective f) :
    (ambiguousFull f).card + 2 * Fintype.card N ≤
      2 * Fintype.card M := by
  let Γ : Finset N := Finset.univ.filter
    (fun y => 2 ≤ extensionCount f y)
  have hΓ {y : N} : y ∈ Γ ↔ 2 ≤ extensionCount f y := by
    simp [Γ]
  have hcount : (ambiguousFull f).card =
      ∑ y ∈ Γ, extensionCount f y := by
    classical
    let he : {x : M // f x ∈ Γ} ≃
        Σ y : Γ, {x : M // f x = y.val} := {
      toFun := fun x => ⟨⟨f x.val, x.property⟩, ⟨x.val,rfl⟩⟩
      invFun := fun p => ⟨p.2.val, by simpa [p.2.property] using p.1.property⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨y,hy⟩,⟨x,hx⟩⟩
        cases hx
        rfl
    }
    calc
      (ambiguousFull f).card = Fintype.card {x : M // f x ∈ Γ} := by
        simp [ambiguousFull, Γ, Fintype.card_subtype]
      _ = Fintype.card (Σ y : Γ, {x : M // f x = y.val}) :=
        Fintype.card_congr he
      _ = ∑ y ∈ Γ, extensionCount f y := by
        rw [Fintype.card_sigma]
        have hu : (Finset.univ : Finset Γ) = Γ.attach := by ext y; simp
        have hs := Finset.sum_attach Γ
          (fun y : N => Fintype.card {x : M // f x = y})
        rw [← hu] at hs
        simpa only [extensionCount, Nat.card_eq_fintype_card] using hs
  have hfiber : ∑ y ∈ Γ, extensionCount f y ≤
      2 * ∑ y ∈ Γ, (extensionCount f y - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    have hh := hΓ.mp hy
    omega
  have hsub : ∑ y ∈ Γ, (extensionCount f y - 1) ≤
      ∑ y : N, (extensionCount f y - 1) :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hsurplus := extension_surplus f hf
  omega

variable {A : Type*} [Fintype A]

def ambiguousFullPatterns (θ : (ℤ × ℤ) → A)
    (S : Finset (ℤ × ℤ)) (v : ℝ × ℝ) :
    Finset (patternSet θ S) :=
  ambiguousFull (restriction θ S v)

theorem ambiguousFullPatterns_card_bound
    (θ : (ℤ × ℤ) → A) (S : Finset (ℤ × ℤ)) (v : ℝ × ℝ) :
    (ambiguousFullPatterns θ S v).card +
      2 * patternComplexity θ (supportBase S v) ≤
        2 * patternComplexity θ S := by
  have h := card_ambiguousFull_le_twice_surplus
    (restriction θ S v) (restriction_surjective θ S v)
  simpa [ambiguousFullPatterns, patternComplexity,
    Nat.card_eq_fintype_card] using h

end

end NivatTrial.ColleAmbiguousFullPatterns
