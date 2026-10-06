import NivatTrial.ColleOneSidedAmbiguity
import NivatTrial.ColleBalancedRows

/-! The negative-horizontal form of the semi-ambiguous half-strip count.
The original counting lemmas are directional; only the geometric choice of
a length-n run at the right end of each row differs from the positive case. -/

namespace NivatTrial.ColleReverseBalancedRows

open NivatTrial.Dynamics NivatTrial.ColleAmbiguity
open NivatTrial.ColleSemiAmbiguity NivatTrial.ColleHalfStrip
open NivatTrial.BalancedWindows NivatTrial.ColleBalancedRows
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

private def reverseHorizontal : G := (-1,0)
private def horizontalReal : ℝ × ℝ := (1,0)

theorem reverse_semi_ambiguous_halfStrip_period
    (θ : G → A) (B : Finset G) (hB : MinusBalanced θ B)
    {x : G → A} (hx : x ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ B horizontalReal reverseHorizontal x hx τ) :
    ∃ N Q : ℕ, 0 < Q ∧
      ∀ t : ℤ, lower B < t → t ≤ upper B →
        ∃ w : G, w ∈ B ∧ w.2=t ∧
          ∀ i : ℤ, τ + N ≤ i →
            x (w+(i+Q) • reverseHorizontal) =
              x (w+i • reverseHorizontal) := by
  let n := (bottomEdge B).card-1
  have hedge : supportEdge B horizontalReal = bottomEdge B :=
    horizontal_supportEdge_eq_bottomEdge B hB.nonempty
  have hbase : supportBase B horizontalReal = upperBase B :=
    horizontal_supportBase_eq_upperBase B hB.nonempty
  have hbudget : patternComplexity θ B <
      patternComplexity θ (supportBase B horizontalReal)+
        (supportEdge B horizontalReal).card := by
    simpa only [hbase,hedge] using hB.edge_budget
  have hambpos : 0 < (ambiguousPatterns θ B horizontalReal).card := by
    apply Finset.card_pos.mpr
    let p : patternSet θ (supportBase B horizontalReal) :=
      ⟨patternAt x (supportBase B horizontalReal) (τ • reverseHorizontal),
        patternSet_subset_of_mem_languageHull hx _
          ⟨τ • reverseHorizontal,rfl⟩⟩
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact hamb τ le_rfl
  have hn : 0<n := by
    have hlt := ambiguity_count_lt_edge θ B horizontalReal hbudget
    rw [hedge] at hlt
    omega
  let W : Finset G := (upperBase B).filter
    (fun w => ∀ j : Fin n,
      w+(j.val:ℤ) • reverseHorizontal ∈ upperBase B)
  have hrun : ∀ w ∈ W, ∀ j : Fin n,
      w+(j.val:ℤ) • reverseHorizontal ∈ supportBase B horizontalReal := by
    intro w hw j
    rw [hbase]
    exact (Finset.mem_filter.mp hw).2 j
  have hlen : (supportEdge B horizontalReal).card-1≤n := by rw [hedge]
  obtain ⟨N,Q,hQ,hper⟩ :=
    common_semi_ambiguous_halfStrip_period θ B horizontalReal
      reverseHorizontal W n τ hx hamb hbudget hrun hlen
  refine ⟨N,Q,hQ,?_⟩
  intro t htl htu
  have hrowcard : n≤(row B t).card := hB.row_card t (by omega) htu
  have hrow : (row B t).Nonempty :=
    Finset.card_pos.mp (by omega : 0<(row B t).card)
  obtain ⟨l,hl⟩ := row_run hB.latticeConvex t hrow
  let w : G := (l+((row B t).card:ℤ)-1,t)
  have hwj (j : Fin n) :
      w+(j.val:ℤ) • reverseHorizontal ∈ upperBase B := by
    have hjcard : j.val < (row B t).card :=
      lt_of_lt_of_le j.isLt hrowcard
    let k : ℕ := (row B t).card-1-j.val
    have hk : k < (row B t).card := by dsimp [k]; omega
    have hcoord : w+(j.val:ℤ) • reverseHorizontal = (l+(k:ℤ),t) := by
      ext <;> dsimp [w,reverseHorizontal,k] <;> simp <;> omega
    rw [hcoord]
    have hmem : (l+(k:ℤ),t) ∈ row B t := by
      rw [hl]
      exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr hk,rfl⟩
    rw [upperBase_eq_filter]
    exact Finset.mem_filter.mpr ⟨(row_subset B t) hmem,htl⟩
  have hwbase : w ∈ upperBase B := by
    simpa using hwj ⟨0,hn⟩
  have hw : w ∈ W := Finset.mem_filter.mpr ⟨hwbase,hwj⟩
  have hwB : w ∈ B := by
    rw [upperBase_eq_filter] at hwbase
    exact (Finset.mem_filter.mp hwbase).1
  exact ⟨w,hwB,rfl,hper w hw⟩

/-- A single left-tail threshold works for the whole finite-height band.
The finite bound on starts is automatic for a finite window and is exposed
here so the result can be placed directly into a geometric wedge. -/
theorem reverse_semi_ambiguous_band_period
    (θ : G → A) (B : Finset G) (hB : MinusBalanced θ B)
    {x : G → A} (hx : x ∈ languageHull θ) (τ : ℤ)
    (hamb : SemiAmbiguous θ B horizontalReal reverseHorizontal x hx τ)
    (L : ℤ) (hL : ∀ s ∈ B, L ≤ s.1) :
    ∃ N Q : ℕ, 0 < Q ∧
      ∀ z : G, lower B < z.2 → z.2 ≤ upper B →
        z.1 ≤ L-(τ+N) →
          x (z+(Q:ℤ) • reverseHorizontal)=x z := by
  obtain ⟨N,Q,hQ,hper⟩ :=
    reverse_semi_ambiguous_halfStrip_period θ B hB hx τ hamb
  refine ⟨N,Q,hQ,?_⟩
  intro z hzl hzu hzbound
  obtain ⟨w,hwB,hwrow,hwperiod⟩ := hper z.2 hzl hzu
  let i : ℤ := w.1-z.1
  have hi : τ + N ≤ i := by
    have hwL := hL w hwB
    dsimp [i]
    omega
  have hsame : w+i • reverseHorizontal=z := by
    ext <;> dsimp [i,reverseHorizontal] <;> simp <;> omega
  have hshift : w+(i+Q) • reverseHorizontal=
      z+(Q:ℤ) • reverseHorizontal := by
    rw [add_zsmul]
    rw [← add_assoc, hsame]
  simpa only [hsame,hshift] using hwperiod i hi

end
end NivatTrial.ColleReverseBalancedRows
