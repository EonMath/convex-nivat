import NivatTrial.ColleStripInduction

/-! A quantitative repetition step for the nonunique branch of the
Cyr--Kra strip induction. A finite family of full patterns lying above
ambiguous base patterns has size at most twice the complexity surplus.
Thus a bilateral sequence of such patterns repeats within that bound. -/

namespace NivatTrial.ColleAmbiguousRepeat

open NivatTrial.Dynamics NivatTrial.ColleAmbiguity
open NivatTrial.ColleAmbiguousFullPatterns NivatTrial.ColleLocalSubshift
open scoped Classical

noncomputable section

variable {M N : Type*} [Fintype M] [Fintype N]

theorem bounded_repeat_of_ambiguous_fiber
    (f : M → N) (hf : Function.Surjective f)
    (x : ℤ → M) (hamb : ∀ i, 2 ≤ extensionCount f (f (x i)))
    (h : ℕ) (hsurplus : Fintype.card M ≤ Fintype.card N + h) :
    ∃ i j : ℤ, 0 ≤ i ∧ i < j ∧ j ≤ 2*h ∧ x i = x j := by
  let T : Finset M := ambiguousFull f
  have hcard : T.card ≤ 2*h := by
    have h := card_ambiguousFull_le_twice_surplus f hf
    dsimp [T]
    omega
  let F : Fin (2*h+1) → T := fun k =>
    ⟨x k.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hamb _⟩⟩
  have hnoninj : ¬ Function.Injective F := by
    intro hinj
    have hle := Fintype.card_le_of_injective F hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at hle
    omega
  simp only [Function.Injective] at hnoninj
  push Not at hnoninj
  obtain ⟨i,j,he,hne⟩ := hnoninj
  have hxi : x (i.val:ℤ) = x (j.val:ℤ) := congrArg Subtype.val he
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i.val,j.val,by omega,by exact_mod_cast hij,
      by have := j.isLt; omega,hxi⟩
  · exact ⟨j.val,i.val,by omega,by exact_mod_cast hji,
      by have := i.isLt; omega,hxi.symm⟩

variable {A : Type*} [Fintype A]

theorem bounded_repeated_full_pattern
    (θ : (ℤ × ℤ) → A) (S : Finset (ℤ × ℤ)) (v : ℝ × ℝ)
    (x : (ℤ × ℤ) → A) (hx : LocalAdmissible θ S x)
    (anchor : ℤ → ℤ × ℤ)
    (hamb : ∀ i : ℤ,
      2 ≤ extensionCount (restriction θ S v)
        (restriction θ S v
          ⟨patternAt x S (anchor i),hx (anchor i)⟩))
    (h : ℕ)
    (hbudget : patternComplexity θ S ≤
      patternComplexity θ (supportBase S v) + h) :
    ∃ i j : ℤ, 0 ≤ i ∧ i < j ∧ j ≤ 2*h ∧
      patternAt x S (anchor i) = patternAt x S (anchor j) := by
  let F : ℤ → patternSet θ S := fun i =>
    ⟨patternAt x S (anchor i),hx (anchor i)⟩
  have h := bounded_repeat_of_ambiguous_fiber
    (restriction θ S v) (restriction_surjective θ S v)
    F (fun i => hamb i) h (by
      simpa [patternComplexity, Nat.card_eq_fintype_card] using hbudget)
  obtain ⟨i,j,hi,hij,hj,he⟩ := h
  exact ⟨i,j,hi,hij,hj,congrArg Subtype.val he⟩

end

end NivatTrial.ColleAmbiguousRepeat
