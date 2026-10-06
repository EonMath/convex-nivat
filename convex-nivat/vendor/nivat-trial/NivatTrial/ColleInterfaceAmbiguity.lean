import NivatTrial.ColleBalancedRows

/-! A one-sided interface yields a real ambiguous pattern at its highest
disagreement row. This is the local predecessor of the source's full
ambiguous-configuration propagation. -/

namespace NivatTrial.ColleInterfaceAmbiguity

open NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.ColleAmbiguity NivatTrial.ColleBalancedRows
open NivatTrial.BalancedWindows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

variable {A : Type*} [Fintype A]

/-- Two hull patterns that coincide on the base and disagree on the exposed
edge give two actual extensions of a single actual base pattern. -/
theorem ambiguous_of_two_hull_extensions
    (θ : G → A) (S : Finset G) (v : Plane)
    {x y : G → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (a : G)
    (hbase : ∀ s ∈ supportBase S v, x (a+s) = y (a+s))
    (hedge : ∃ s ∈ supportEdge S v, x (a+s) ≠ y (a+s)) :
    AmbiguousPattern θ S v
      ⟨patternAt x (supportBase S v) a,
        patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩ := by
  let px : patternSet θ S :=
    ⟨patternAt x S a,patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩
  let py : patternSet θ S :=
    ⟨patternAt y S a,patternSet_subset_of_mem_languageHull hy _ ⟨a,rfl⟩⟩
  let p : patternSet θ (supportBase S v) :=
    ⟨patternAt x (supportBase S v) a,
      patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩
  have hpx : restriction θ S v px = p := by
    apply Subtype.ext
    funext s
    rfl
  have hpy : restriction θ S v py = p := by
    apply Subtype.ext
    funext s
    exact (hbase s s.property).symm
  have hpne : px ≠ py := by
    obtain ⟨s,hs,hne⟩ := hedge
    intro he
    have hf := congrFun (congrArg Subtype.val he) ⟨s,(supportEdge_subset S v) hs⟩
    exact hne hf
  exact two_extensions_imply_count hpx hpy hpne

/-- Because the integer levels are discrete, the disagreement set below an
agreed half-plane has a highest occupied row. -/
theorem highest_disagreement_row
    {x y : G → A}
    (hagree : ∀ z : G, 0 ≤ z.2 → x z = y z) (hne : x ≠ y) :
    ∃ d : ℤ, (∃ w : G, w.2 = d ∧ x w ≠ y w) ∧
      ∀ z : G, d < z.2 → x z = y z := by
  let P : ℤ → Prop := fun d => ∃ w : G, w.2 = d ∧ x w ≠ y w
  have hbdd : ∃ b : ℤ, ∀ d, P d → d ≤ b := by
    refine ⟨-1,?_⟩
    intro d ⟨w,hw,hxy⟩
    have hwneg : w.2 < 0 := by
      by_contra h
      exact hxy (hagree w (le_of_not_gt h))
    omega
  have hinh : ∃ d, P d := by
    by_contra h
    apply hne
    funext w
    by_contra hxy
    exact h ⟨w.2,w,rfl,hxy⟩
  obtain ⟨d,hd,hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  refine ⟨d,hd,?_⟩
  intro z hdz
  by_contra hxy
  have hz := hmax z.2 ⟨z,rfl,hxy⟩
  omega

/-- At the exposed bottom edge of any nonempty window, an actual one-sided
nonexpansive pair produces at least one ambiguous base pattern. -/
theorem exists_ambiguous_pattern_of_horizontal_interface
    (θ : G → A) (B : Finset G) (hB : B.Nonempty)
    {x y : G → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (hagree : AgreeOn x y (halfPlane (1,0) 0)) (hne : x ≠ y) :
    ∃ a : G, AmbiguousPattern θ B (1,0)
      ⟨patternAt x (supportBase B (1,0)) a,
        patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩ := by
  have hrowAgree : ∀ z : G, 0 ≤ z.2 → x z = y z := by
    intro z hz
    exact hagree z (by simpa [halfPlane, score] using hz)
  obtain ⟨d,⟨w,hw,hwne⟩,hhighest⟩ :=
    highest_disagreement_row hrowAgree hne
  obtain ⟨g,hg⟩ := bottomEdge_nonempty hB
  let a : G := w-g
  have hbase : ∀ s ∈ supportBase B (1,0), x (a+s)=y (a+s) := by
    intro s hs
    have hsupper : s ∈ upperBase B := by
      rw [← horizontal_supportBase_eq_upperBase B hB]
      exact hs
    have hslt : lower B < s.2 := by
      rw [upperBase_eq_filter] at hsupper
      exact (Finset.mem_filter.mp hsupper).2
    have hgheight : g.2 = lower B := (mem_row B (lower B) g).mp hg |>.2
    apply hhighest
    dsimp [a]
    change d < w.2 - g.2 + s.2
    omega
  have hedge : ∃ s ∈ supportEdge B (1,0), x (a+s) ≠ y (a+s) := by
    refine ⟨g,?_,?_⟩
    · have heq : supportEdge B (1,0) = bottomEdge B :=
        horizontal_supportEdge_eq_bottomEdge B hB
      rw [heq]
      exact hg
    · simpa [a] using hwne
  exact ⟨a,ambiguous_of_two_hull_extensions θ B (1,0) hx hy a hbase hedge⟩

end

end NivatTrial.ColleInterfaceAmbiguity
