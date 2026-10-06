import NivatTrial.FiniteIncrementFibers

/-! Choose a difference fiber of maximum finite cardinality. The maximum is
an attained cardinality, not a supremum assumed to have representatives. -/

namespace NivatTrial.MaximalIncrementFibers

open NivatTrial.Dynamics NivatTrial.PeriodicDifference
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

theorem exists_maximal_fiber (θ : Lattice → A) (w : A → ℤ) (h : Lattice)
    (N : ℕ)
    (hbound : ∀ n : ℕ, ∀ F : Fin n → Lattice → A,
      (∀ i, F i ∈ languageHull θ) → Function.Injective F →
      (∀ i j, increment (encode w (F i)) h = increment (encode w (F j)) h) → n ≤ N) :
    ∃ n : ℕ, 0 < n ∧ ∃ F : Fin n → Lattice → A,
      (∀ i, F i ∈ languageHull θ) ∧ Function.Injective F ∧
      (∀ i j, increment (encode w (F i)) h = increment (encode w (F j)) h) ∧
      ∀ m : ℕ, ∀ G : Fin m → Lattice → A,
        (∀ i, G i ∈ languageHull θ) → Function.Injective G →
        (∀ i j, increment (encode w (G i)) h = increment (encode w (G j)) h) → m ≤ n := by
  let P (n : ℕ) : Prop := ∃ F : Fin n → Lattice → A,
    (∀ i, F i ∈ languageHull θ) ∧ Function.Injective F ∧
      ∀ i j, increment (encode w (F i)) h = increment (encode w (F j)) h
  have hone : P 1 :=
    ⟨fun _ => θ,fun _ => self_mem_languageHull θ,
      fun _ _ _ => Subsingleton.elim _ _,fun _ _ => rfl⟩
  have hPbound {n : ℕ} (hp : P n) : n ≤ N := by
    obtain ⟨F,hF,hi,hinc⟩ := hp
    exact hbound n F hF hi hinc
  let C := (Finset.range (N+1)).filter P
  have hmem {n : ℕ} (hp : P n) : n ∈ C := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hPbound hp; omega),hp⟩
  obtain ⟨n,hn,hmax⟩ := Finset.exists_max_image C id ⟨1,hmem hone⟩
  have hnpos : 0 < n := by
    have hh := hmax 1 (hmem hone)
    change 1 ≤ n at hh
    omega
  obtain ⟨F,hF,hi,hinc⟩ := (Finset.mem_filter.mp hn).2
  exact ⟨n,hnpos,F,hF,hi,hinc,fun m G hG hj hjinc => hmax m (hmem ⟨G,hG,hj,hjinc⟩)⟩

end
end NivatTrial.MaximalIncrementFibers
