import NivatTrial.ColleHalfStrip
import NivatTrial.BalancedWindows
import NivatTrial.ColleGenerating

/-! A genuine lattice-convex balanced window supplies the full row runs
needed in Colle's half-strip Morse--Hedlund argument. -/

namespace NivatTrial.ColleBalancedRows

open NivatTrial.Dynamics NivatTrial.ColleAmbiguity
open NivatTrial.ColleSemiAmbiguity NivatTrial.ColleHalfStrip
open NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

private def horizontal : G := (1, 0)
private def horizontalReal : Plane := (1, 0)

theorem horizontal_supportEdge_eq_bottomEdge
    (B : Finset G) (hB : B.Nonempty) :
    supportEdge B horizontalReal = bottomEdge B := by
  ext z
  simp only [supportEdge, Finset.mem_filter, bottomEdge, mem_row]
  constructor
  · rintro ⟨hz, hmin⟩
    obtain ⟨w, hw⟩ := bottomEdge_nonempty hB
    have hwB := (mem_row B (lower B) w).mp hw
    have hs := hmin w hwB.1
    have hzmin : z.2 ≤ lower B := by
      have hs' : (z.2 : ℝ) ≤ (lower B : ℝ) := by
        simpa [horizontalReal, NivatTrial.Nonexpansive.score, hwB.2] using hs
      exact_mod_cast hs'
    exact ⟨hz, le_antisymm hzmin (lower_le_of_mem hz)⟩
  · rintro ⟨hz, hzlower⟩
    refine ⟨hz, ?_⟩
    intro s hs
    have hle := lower_le_of_mem hs
    have hle' : (z.2 : ℝ) ≤ (s.2 : ℝ) := by
      exact_mod_cast hzlower ▸ hle
    simpa [horizontalReal, NivatTrial.Nonexpansive.score] using hle'

theorem horizontal_supportBase_eq_upperBase
    (B : Finset G) (hB : B.Nonempty) :
    supportBase B horizontalReal = upperBase B := by
  simp only [supportBase, upperBase, horizontal_supportEdge_eq_bottomEdge B hB]

theorem negative_horizontal_supportEdge_eq_topEdge
    (B : Finset G) (hB : B.Nonempty) :
    supportEdge B (-1,0) = topEdge B := by
  ext z
  simp only [supportEdge, Finset.mem_filter, topEdge, mem_row]
  constructor
  · rintro ⟨hz, hmin⟩
    obtain ⟨w, hw⟩ := topEdge_nonempty hB
    have hwB := (mem_row B (upper B) w).mp hw
    have hs := hmin w hwB.1
    have hzmax : upper B ≤ z.2 := by
      have hs' : (upper B : ℝ) ≤ (z.2 : ℝ) := by
        simpa [NivatTrial.Nonexpansive.score, hwB.2] using hs
      exact_mod_cast hs'
    exact ⟨hz, le_antisymm (le_upper_of_mem hz) hzmax⟩
  · rintro ⟨hz, hzupper⟩
    refine ⟨hz, ?_⟩
    intro s hs
    have hle := le_upper_of_mem hs
    have hle' : (s.2 : ℝ) ≤ (z.2 : ℝ) := by
      exact_mod_cast hzupper ▸ hle
    simpa [NivatTrial.Nonexpansive.score] using hle'

theorem negative_horizontal_supportBase_eq_base
    (B : Finset G) (hB : B.Nonempty) :
    supportBase B (-1,0) = base B := by
  simp only [supportBase, base, negative_horizontal_supportEdge_eq_topEdge B hB]

variable {A : Type*} [Fintype A]

/-- No second minimization is needed: the same minimal generating window is
already balanced on whichever extreme horizontal edge is shorter. -/
theorem generatingWindow_balanced_choice
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B)
    (hlow : patternComplexity θ B ≤ B.card) :
    PlusBalanced θ B ∨ MinusBalanced θ B := by
  by_cases hchoice : (topEdge B).card ≤ (bottomEdge B).card
  · left
    refine ⟨hgen.nonempty,hgen.latticeConvex,hlow,?_,?_⟩
    · have hb := hgen.strict_edge_budget (-1,0)
      simpa only [negative_horizontal_supportBase_eq_base B hgen.nonempty,
        negative_horizontal_supportEdge_eq_topEdge B hgen.nonempty] using hb
    · intro t htl htu
      simpa [min_eq_left hchoice] using
        row_card_ge_min_edges hgen.latticeConvex hgen.nonempty t htl htu
  · right
    have hchoice' : (bottomEdge B).card ≤ (topEdge B).card := by omega
    refine ⟨hgen.nonempty,hgen.latticeConvex,hlow,?_,?_⟩
    · have hb := hgen.strict_edge_budget (1,0)
      have hbase : supportBase B (1,0) = upperBase B :=
        horizontal_supportBase_eq_upperBase B hgen.nonempty
      have hedge : supportEdge B (1,0) = bottomEdge B :=
        horizontal_supportEdge_eq_bottomEdge B hgen.nonempty
      rw [hbase,hedge] at hb
      exact hb
    · intro t htl htu
      simpa [min_eq_right hchoice'] using
        row_card_ge_min_edges hgen.latticeConvex hgen.nonempty t htl htu

/-- Colle Claim 4.2 in horizontal coordinates: every row above the deleted
bottom edge has a common eventual horizontal period, obtained from actual
ambiguity and actual finite-window complexity. -/
theorem balanced_semi_ambiguous_halfStrip_period
    (θ : G → A) (B : Finset G) (hB : MinusBalanced θ B)
    {x : G → A} (hx : x ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ B horizontalReal horizontal x hx τ) :
    ∃ N Q : ℕ, 0 < Q ∧
      ∀ t : ℤ, lower B < t → t ≤ upper B →
        ∃ w : G, w.2 = t ∧
          ∀ i : ℤ, τ + N ≤ i →
            x (w + (i + Q) • horizontal) = x (w + i • horizontal) := by
  let n := (bottomEdge B).card - 1
  have hedge : supportEdge B horizontalReal = bottomEdge B :=
    horizontal_supportEdge_eq_bottomEdge B hB.nonempty
  have hbase : supportBase B horizontalReal = upperBase B :=
    horizontal_supportBase_eq_upperBase B hB.nonempty
  have hbudget : patternComplexity θ B <
      patternComplexity θ (supportBase B horizontalReal) +
        (supportEdge B horizontalReal).card := by
    simpa only [hbase, hedge] using hB.edge_budget
  have hambpos : 0 < (ambiguousPatterns θ B horizontalReal).card := by
    apply Finset.card_pos.mpr
    let p : patternSet θ (supportBase B horizontalReal) :=
      ⟨patternAt x (supportBase B horizontalReal) (τ • horizontal),
        patternSet_subset_of_mem_languageHull hx _ ⟨τ • horizontal, rfl⟩⟩
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact hamb τ le_rfl
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
  obtain ⟨N, Q, hQ, hper⟩ :=
    common_semi_ambiguous_halfStrip_period θ B horizontalReal horizontal
      W n τ hx hamb hbudget hrun hlen
  refine ⟨N, Q, hQ, ?_⟩
  intro t htl htu
  have hrowcard : n ≤ (row B t).card :=
    hB.row_card t (by omega) htu
  have hrow : (row B t).Nonempty :=
    Finset.card_pos.mp (by omega : 0 < (row B t).card)
  obtain ⟨l, hl⟩ := row_run hB.latticeConvex t hrow
  let w : G := (l, t)
  have hwj (j : Fin n) : w + (j.val : ℤ) • horizontal ∈ upperBase B := by
    have hmem : (l + (j.val : ℤ), t) ∈ row B t := by
      rw [hl]
      apply Finset.mem_image.mpr
      exact ⟨j.val, Finset.mem_range.mpr (lt_of_lt_of_le j.isLt hrowcard), rfl⟩
    have hu : (l + (j.val : ℤ), t) ∈ upperBase B := by
      rw [upperBase_eq_filter]
      exact Finset.mem_filter.mpr ⟨(row_subset B t) hmem, htl⟩
    simpa [w, horizontal] using hu
  have hwbase : w ∈ upperBase B := by
    simpa [w, horizontal] using hwj ⟨0, hn⟩
  have hw : w ∈ W := Finset.mem_filter.mpr ⟨hwbase, hwj⟩
  exact ⟨w, rfl, hper w hw⟩

end

end NivatTrial.ColleBalancedRows
