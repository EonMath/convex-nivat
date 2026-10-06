import NivatTrial.ColleLocalBoundaryPropagation

/-! Nonunique-extension step for one adjacent horizontal strip. The actual
full-window patterns repeat within twice the edge budget. Their overlap
fixes the phase on the old periodic rows; generated endpoints then extend
the repeated block across the new row. -/

namespace NivatTrial.ColleNonuniqueStrip

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.MorseHedlund
open NivatTrial.BalancedWindows NivatTrial.ColleAmbiguity
open NivatTrial.ColleLocalSubshift NivatTrial.ColleAmbiguousRepeat
open NivatTrial.ColleStripPeriod NivatTrial.ColleLocalBoundaryPropagation
open NivatTrial.ColleBalancedRows NivatTrial.GeneratingWindows
open NivatTrial.LatticePolygon NivatTrial.ColleGenerating
open scoped Classical

set_option maxHeartbeats 1000000

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [Fintype A]

private def horizontal : G := (1,0)
private def horizontalReal : ℝ × ℝ := (1,0)

theorem repeated_pattern_aligns_inner_rows
    (B : Finset G) (hconv : IsLatticeConvex B)
    (x : G → A) (d i j : ℤ) (p : ℕ) (hp : 0 < p)
    (hrowcard : ∀ t : ℤ, lower B < t → t ≤ upper B →
      p ≤ (row B t).card)
    (hperiod : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B →
      x (z+(p:ℤ) • horizontal) = x z)
    (hmatch : patternAt x B (i,d-lower B) =
      patternAt x B (j,d-lower B)) :
    ∀ z : G, d < z.2 → z.2 ≤ d + upper B - lower B →
      x (z+(j-i) • horizontal) = x z := by
  intro z hzlow hzhigh
  let t : ℤ := z.2-d+lower B
  have htlow : lower B < t := by dsimp [t]; omega
  have hthigh : t ≤ upper B := by dsimp [t]; omega
  have hcard := hrowcard t htlow hthigh
  have hrow : (row B t).Nonempty :=
    Finset.card_pos.mp (by omega : 0 < (row B t).card)
  obtain ⟨l,hl⟩ := row_run hconv t hrow
  let ξ : ℤ → A := fun k => x (k,d-lower B+t)
  have hξ : IsPeriod ξ (p:ℤ) := by
    intro k
    have h' := hperiod (k,d-lower B+t) (by dsimp [t]; omega)
      (by dsimp [t]; omega)
    simpa [ξ,horizontal] using h'
  have hblock : ∀ r : ℤ, 0 ≤ r → r < p →
      ξ ((i+l)+r+(j-i)) = ξ ((i+l)+r) := by
    intro r hr0 hrp
    have hrnat : (r.toNat:ℤ) = r := Int.toNat_of_nonneg hr0
    have hrlt : r.toNat < (row B t).card := by
      have hp' : r < (p:ℤ) := hrp
      omega
    have hsrow : (l+r,t) ∈ row B t := by
      rw [hl]
      apply Finset.mem_image.mpr
      exact ⟨r.toNat,Finset.mem_range.mpr hrlt,by simp [hrnat]⟩
    have hsB : (l+r,t) ∈ B := (row_subset B t) hsrow
    have hm := congrFun hmatch ⟨(l+r,t),hsB⟩
    change x ((i,d-lower B)+(l+r,t)) =
      x ((j,d-lower B)+(l+r,t)) at hm
    change x (((i+l)+r+(j-i),d-lower B+t)) =
      x (((i+l)+r,d-lower B+t))
    convert hm.symm using 1 <;> congr 1 <;> ext <;> simp <;> omega
  have hq := period_of_equal_block ξ p hp hξ (i+l) (j-i) hblock
  have he : d-lower B+t = z.2 := by dsimp [t]; omega
  have hz' := hq z.1
  change x (z.1+(j-i),d-lower B+t) = x (z.1,d-lower B+t) at hz'
  convert hz' using 1 <;> congr 1 <;> ext <;> simp [horizontal,he] <;> omega

theorem ambiguous_extension_propagates_bounded_period
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B) (hbalanced : MinusBalanced θ B)
    {x : G → A} (hx : x ∈ languageHull θ)
    (d : ℤ) (p : ℕ) (hp : 0 < p)
    (hpedge : p ≤ (bottomEdge B).card - 1)
    (hperiod : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B →
      x (z+(p:ℤ) • horizontal) = x z)
    (hamb : ∀ i : ℤ,
      2 ≤ extensionCount (restriction θ B horizontalReal)
        (restriction θ B horizontalReal
          ⟨patternAt x B (i,d-lower B),
            localAdmissible_of_hull hx (i,d-lower B)⟩)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2*((bottomEdge B).card-1) ∧
      ∀ z : G, d ≤ z.2 → z.2 ≤ d + upper B - lower B →
        x (z+(q:ℤ) • horizontal) = x z := by
  let h := (bottomEdge B).card-1
  have hxlocal : LocalAdmissible θ B x := localAdmissible_of_hull hx
  have hbase : supportBase B horizontalReal = upperBase B :=
    horizontal_supportBase_eq_upperBase B hbalanced.nonempty
  have hedge : supportEdge B horizontalReal = bottomEdge B :=
    horizontal_supportEdge_eq_bottomEdge B hbalanced.nonempty
  have hbudget : patternComplexity θ B ≤
      patternComplexity θ (supportBase B horizontalReal) + h := by
    have hb := hbalanced.edge_budget
    have hpos : 0 < (bottomEdge B).card :=
      Finset.card_pos.mpr (bottomEdge_nonempty hbalanced.nonempty)
    rw [hbase]
    dsimp [h]
    omega
  obtain ⟨i,j,hi,hij,hj,hmatch⟩ :=
    bounded_repeated_full_pattern θ B horizontalReal x hxlocal
      (fun k => (k,d-lower B)) hamb h hbudget
  let q : ℕ := (j-i).toNat
  have hqcast : (q:ℤ) = j-i := Int.toNat_of_nonneg (by omega : 0 ≤ j-i)
  have hq : 0 < q := by dsimp [q]; omega
  have hqbound : q ≤ 2*h := by dsimp [q]; omega
  have hrowcard : ∀ t : ℤ, lower B < t → t ≤ upper B →
      p ≤ (row B t).card := by
    intro t htl htu
    have hh := hbalanced.row_card t (by omega) htu
    omega
  have hinner := repeated_pattern_aligns_inner_rows B hbalanced.latticeConvex
    x d i j p hp hrowcard hperiod hmatch
  have hinnerQ : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B →
      x (z+(q:ℤ) • horizontal) = x z := by
    intro z hzlow hzhigh
    simpa only [hqcast] using hinner z hzlow hzhigh
  let anchor : G := (i,d-lower B)
  let y : G → A := shift ((q:ℤ) • horizontal) x
  have hylocal : LocalAdmissible θ B y :=
    localAdmissible_shift hxlocal _
  have hlocal : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B → x z = y z := by
    intro z hzlow hzhigh
    have hh := hinnerQ z hzlow hzhigh
    simpa [y,shift,add_comm] using hh.symm
  have hanheight : anchor.2 + lower B = d := by dsimp [anchor]; omega
  have hblock : ∀ s ∈ bottomEdge B, x (anchor+s)=y (anchor+s) := by
    intro s hs
    have hsB := (mem_row B (lower B) s).mp hs |>.1
    have hm := congrFun hmatch ⟨s,hsB⟩
    change x (anchor+s) = x ((j,d-lower B)+s) at hm
    calc
      x (anchor+s) = x ((j,d-lower B)+s) := hm
      _ = y (anchor+s) := by
        dsimp [y,shift]
        congr 1
        dsimp [anchor,horizontal]
        ext <;> simp [hqcast] <;> omega
  have hbottom := bottom_block_forces_whole_row_local θ B hgen
    hxlocal hylocal d hlocal anchor hanheight hblock
  refine ⟨q,hq,hqbound,?_⟩
  intro z hzlow hzhigh
  by_cases hz : z.2 = d
  · have hh := hbottom z hz
    simpa [y,shift,add_comm] using hh.symm
  · exact hinnerQ z (by omega) hzhigh

end

end NivatTrial.ColleNonuniqueStrip
