import NivatTrial.ColleLocalSubshift

/-! Full, rather than one-sided, ambiguity yields bilateral periods on the
adjacent rows of a balanced generating window. This preserves the original
interface point; the compactness recentering used for eventual periods is not
needed for Cyr–Kra's boundary-strip base case. -/

namespace NivatTrial.ColleAmbiguousStrip

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.MorseHedlund
open NivatTrial.AmbiguityPropagation
open NivatTrial.ColleAmbiguity NivatTrial.ColleBalancedRows
open NivatTrial.BalancedWindows NivatTrial.ColleSemiAmbiguity
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ
private def horizontal : G := (1,0)
private def horizontalReal : Plane := (1,0)

variable {A : Type*} [Fintype A]

theorem ambiguous_row_periodic_sharp
    (θ : G → A) (S : Finset G) (v : Plane) (u w : G) (n : ℕ)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S v) + (supportEdge S v).card)
    (hamb : ∀ i : ℤ,
      AmbiguousPattern θ S v
        ⟨patternAt x (supportBase S v) (i • u),
          patternSet_subset_of_mem_languageHull hx _ ⟨i • u, rfl⟩⟩)
    (hrun : ∀ j : Fin n, w + (j.val : ℤ) • u ∈ supportBase S v)
    (hlen : (supportEdge S v).card - 1 ≤ n) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod (rowSequence x w u) (q : ℤ) := by
  have hdir := directional_complexity_lt_edge θ S v u hx hbudget hamb
  have hrow := row_wordComplexity_le_directional x (supportBase S v) w u n hrun
  apply morse_hedlund (n := n)
  omega

theorem common_ambiguous_halfStrip_period
    (θ : G → A) (S : Finset G) (v : Plane) (u : G)
    (W : Finset G) (n : ℕ)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hamb : ∀ i : ℤ,
      AmbiguousPattern θ S v
        ⟨patternAt x (supportBase S v) (i • u),
          patternSet_subset_of_mem_languageHull hx _ ⟨i • u, rfl⟩⟩)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S v) + (supportEdge S v).card)
    (hrun : ∀ w ∈ W, ∀ j : Fin n,
      w + (j.val : ℤ) • u ∈ supportBase S v)
    (hlen : (supportEdge S v).card - 1 ≤ n) :
    ∃ Q : ℕ, 0 < Q ∧
      ∀ w ∈ W, IsPeriod (rowSequence x w u) (Q : ℤ) := by
  let ξ : W → ℤ → A := fun w => rowSequence x w.val u
  have hper (w : W) :
      ∃ q : ℕ, 0 < q ∧ IsPeriod (ξ w) (q : ℤ) :=
    ambiguous_row_periodic_sharp θ S v u w.val n hx hbudget hamb
      (hrun w.val w.property) hlen
  obtain ⟨Q,hQ,hcommon⟩ := common_row_period ξ hper
  exact ⟨Q,hQ,fun w hw => hcommon ⟨w,hw⟩⟩

theorem ambiguous_minus_balanced_adjacent_strip
    (θ : G → A) (B : Finset G) (hB : MinusBalanced θ B)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hamb : ∀ i : ℤ,
      AmbiguousPattern θ B horizontalReal
        ⟨patternAt x (supportBase B horizontalReal) (i • horizontal),
          patternSet_subset_of_mem_languageHull hx _ ⟨i • horizontal, rfl⟩⟩) :
    ∃ Q : ℕ, 0 < Q ∧
      ∀ z : G, lower B < z.2 → z.2 ≤ upper B →
        x (z + (Q : ℤ) • horizontal) = x z := by
  let n := (bottomEdge B).card - 1
  have hedge : supportEdge B horizontalReal = bottomEdge B :=
    horizontal_supportEdge_eq_bottomEdge B hB.nonempty
  have hbase : supportBase B horizontalReal = upperBase B :=
    horizontal_supportBase_eq_upperBase B hB.nonempty
  have hbudget : patternComplexity θ B <
      patternComplexity θ (supportBase B horizontalReal) +
        (supportEdge B horizontalReal).card := by
    simpa only [hbase,hedge] using hB.edge_budget
  have hpositive : 0 < (ambiguousPatterns θ B horizontalReal).card := by
    apply Finset.card_pos.mpr
    let p : patternSet θ (supportBase B horizontalReal) :=
      ⟨patternAt x (supportBase B horizontalReal) 0,
        patternSet_subset_of_mem_languageHull hx _ ⟨0,rfl⟩⟩
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [p] using hamb 0
  have hn : 0 < n := by
    have hlt := ambiguity_count_lt_edge θ B horizontalReal hbudget
    rw [hedge] at hlt
    omega
  let W : Finset G := (upperBase B).filter
    (fun w => ∀ j : Fin n, w + (j.val : ℤ) • horizontal ∈ upperBase B)
  have hrun : ∀ w ∈ W, ∀ j : Fin n,
      w + (j.val : ℤ) • horizontal ∈ supportBase B horizontalReal := by
    intro w hw j
    rw [hbase]
    exact (Finset.mem_filter.mp hw).2 j
  have hlen : (supportEdge B horizontalReal).card - 1 ≤ n := by
    rw [hedge]
  obtain ⟨Q,hQ,hper⟩ :=
    common_ambiguous_halfStrip_period θ B horizontalReal horizontal
      W n hx hamb hbudget hrun hlen
  refine ⟨Q,hQ,?_⟩
  intro z hzl hzu
  have hrowcard : n ≤ (row B z.2).card :=
    hB.row_card z.2 (by omega) hzu
  have hrow : (row B z.2).Nonempty :=
    Finset.card_pos.mp (by omega : 0 < (row B z.2).card)
  obtain ⟨l,hl⟩ := row_run hB.latticeConvex z.2 hrow
  let w : G := (l,z.2)
  have hwj (j : Fin n) : w + (j.val : ℤ) • horizontal ∈ upperBase B := by
    have hmem : (l+(j.val:ℤ),z.2) ∈ row B z.2 := by
      rw [hl]
      exact Finset.mem_image.mpr ⟨j.val,Finset.mem_range.mpr
        (lt_of_lt_of_le j.isLt hrowcard),rfl⟩
    have hu : (l+(j.val:ℤ),z.2) ∈ upperBase B := by
      rw [upperBase_eq_filter]
      exact Finset.mem_filter.mpr ⟨(row_subset B z.2) hmem,hzl⟩
    simpa [w,horizontal] using hu
  have hwbase : w ∈ upperBase B := by
    simpa [w,horizontal] using hwj ⟨0,hn⟩
  have hw : w ∈ W := Finset.mem_filter.mpr ⟨hwbase,hwj⟩
  have hperiod := hper w hw (z.1-l)
  change x (w + ((z.1-l)+Q) • horizontal) =
    x (w + (z.1-l) • horizontal) at hperiod
  convert hperiod using 1 <;> congr 1 <;> ext <;> simp [w,horizontal] <;> omega

end

end NivatTrial.ColleAmbiguousStrip
