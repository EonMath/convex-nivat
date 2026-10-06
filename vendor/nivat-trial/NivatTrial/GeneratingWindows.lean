import NivatTrial.Nonexpansive

/-! A generated exposed point rules out ambiguity on the opposite half-plane.
The proof iterates the local extension rule through the entire lattice. -/

namespace NivatTrial.GeneratingWindows

open NivatTrial.Dynamics NivatTrial.AmbiguityPropagation NivatTrial.Nonexpansive
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

/-- `g` is the unique point of the window minimizing the oriented score. -/
def UniqueMinimum (S : Finset G) (v : Plane) (g : G) : Prop :=
  g ∈ S ∧ ∀ s ∈ S, s ≠ g → score v g < score v s

/-- Every actual `S`-pattern is uniquely determined by its restriction away
from `g`. The equality of actual complexities is the convenient finite test. -/
def Generated [Fintype A] (θ : G → A) (S : Finset G) (g : G) : Prop :=
  g ∈ S ∧ patternComplexity θ (S.erase g) = patternComplexity θ S

theorem generated_determines [Fintype A] {θ : G → A} {S : Finset G}
    {g : G} (h : Generated θ S g) : Determines θ (S.erase g) g := by
  rcases h with ⟨hg, hcard⟩
  apply determines_of_plateau
  simpa [Finset.insert_erase hg] using hcard

private theorem positive_uniform_gap {S : Finset G} {v : Plane} {g : G}
    (h : UniqueMinimum S v g) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S.erase g, δ ≤ score v s - score v g := by
  have hpos : ∀ s ∈ S.erase g, 0 < score v s - score v g := by
    intro s hs
    have hsg := Finset.mem_erase.mp hs
    have hlt := h.2 s hsg.2 hsg.1
    linarith
  have aux (T : Finset G) (hT : T ⊆ S.erase g) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ T, δ ≤ score v s - score v g := by
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨1, by norm_num, by simp⟩
    | @insert a T ha ih =>
      have hsub : T ⊆ S.erase g :=
        Finset.Subset.trans (Finset.subset_insert a T) hT
      obtain ⟨δ, hδ, hbound⟩ := ih hsub
      have hpa : 0 < score v a - score v g :=
        hpos a (hT (Finset.mem_insert_self a T))
      refine ⟨min δ (score v a - score v g), lt_min hδ hpa, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound s hs)
  exact aux (S.erase g) Finset.Subset.rfl

/-- Colle's elementary generating-vertex lemma: an exposed point generated
by the other sites excludes one-sided nonexpansiveness in the orientation
whose half-plane contains all sites of the translated base. -/
theorem oneSidedExpansive_of_uniqueMinimum_determines [Fintype A]
    {θ : G → A} {S : Finset G} {v : Plane} {g : G}
    (hext : UniqueMinimum S v g) (hdet : Determines θ (S.erase g) g) :
    OneSidedExpansive θ v := by
  intro hamb
  obtain ⟨x, hx, y, hy, hne, hagree⟩ := hamb
  obtain ⟨δ, hδ, hgap⟩ := positive_uniform_gap hext
  have hall (n : ℕ) :
      ∀ z : G, -(n : ℝ) * δ ≤ score v z → x z = y z := by
    induction n with
    | zero =>
      intro z hz
      apply hagree z
      simpa [halfPlane] using hz
    | succ n ih =>
      intro z hz
      have hpatterns : patternAt x (S.erase g) (z - g) =
          patternAt y (S.erase g) (z - g) := by
        funext s
        have hs := hgap s s.property
        have hscore : score v (z - g + s.val) =
            score v z + (score v s.val - score v g) := by
          rw [score_add, score_sub]
          ring
        have hz' : -((n : ℝ) + 1) * δ ≤ score v z := by
          simpa [Nat.cast_add] using hz
        have hbound : -(n : ℝ) * δ ≤ score v (z - g + s.val) := by
          rw [hscore]
          nlinarith
        exact ih _ hbound
      have heq := hdet x hx y hy (z - g) (z - g) hpatterns
      simpa using heq
  apply hne
  funext z
  obtain ⟨n, hn⟩ := exists_nat_gt (-score v z / δ)
  have hmul : -score v z < (n : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hn
  exact hall n z (by linarith)

theorem oneSidedExpansive_of_uniqueMinimum_generated [Fintype A]
    {θ : G → A} {S : Finset G} {v : Plane} {g : G}
    (hext : UniqueMinimum S v g) (hgen : Generated θ S g) :
    OneSidedExpansive θ v :=
  oneSidedExpansive_of_uniqueMinimum_determines hext (generated_determines hgen)

theorem oneSidedNonexpansive_not_generated [Fintype A]
    {θ : G → A} {S : Finset G} {v : Plane} {g : G}
    (hext : UniqueMinimum S v g)
    (hamb : OneSidedNonexpansive θ v) :
    patternComplexity θ (S.erase g) < patternComplexity θ S := by
  have hmono : patternComplexity θ (S.erase g) ≤ patternComplexity θ S :=
    patternComplexity_mono θ (Finset.erase_subset g S)
  rcases lt_or_eq_of_le hmono with hlt | heq
  · exact hlt
  · exact False.elim ((oneSidedExpansive_of_uniqueMinimum_generated
      hext ⟨hext.1, heq⟩) hamb)

end

end NivatTrial.GeneratingWindows
