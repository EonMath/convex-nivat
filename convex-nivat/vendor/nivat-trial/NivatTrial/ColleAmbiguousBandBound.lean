import NivatTrial.ColleMorseBound
import NivatTrial.ColleBalancedRows
import NivatTrial.ColleLocalSubshift

/-! The quantitative ambiguous-border lemma in horizontal coordinates.
All rows in the inner band are bundled into one finite-alphabet column
sequence. Every length-h word is read from a single actual base pattern,
so Morse--Hedlund gives one common period no larger than h. -/

namespace NivatTrial.ColleAmbiguousBandBound

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.MorseHedlund
open NivatTrial.BalancedWindows NivatTrial.ColleAmbiguity
open NivatTrial.ColleBalancedRows NivatTrial.ColleGenerating
open NivatTrial.ColleLocalSubshift NivatTrial.ColleMorseBound
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

private def horizontal : G := (1,0)
private def horizontalReal : ℝ × ℝ := (1,0)

theorem ambiguous_inner_band_bounded_period
    (θ : G → A) (B : Finset G) (hB : MinusBalanced θ B)
    (x : G → A) (hx : LocalAdmissible θ B x) (d : ℤ)
    (hamb : ∀ i : ℤ,
      2 ≤ extensionCount (restriction θ B horizontalReal)
        (restriction θ B horizontalReal
          ⟨patternAt x B (i,d-lower B),hx (i,d-lower B)⟩)) :
    ∃ p : ℕ, 0 < p ∧ p ≤ (bottomEdge B).card-1 ∧
      ∀ z : G, d < z.2 → z.2 ≤ d+upper B-lower B →
        x (z+(p:ℤ) • horizontal) = x z := by
  let h := (bottomEdge B).card-1
  have hedge : supportEdge B horizontalReal = bottomEdge B :=
    horizontal_supportEdge_eq_bottomEdge B hB.nonempty
  have hbase : supportBase B horizontalReal = upperBase B :=
    horizontal_supportBase_eq_upperBase B hB.nonempty
  have hbudget : patternComplexity θ B <
      patternComplexity θ (supportBase B horizontalReal) +
        (supportEdge B horizontalReal).card := by
    simpa only [hbase,hedge] using hB.edge_budget
  have hambpos : 0 < (ambiguousPatterns θ B horizontalReal).card := by
    apply Finset.card_pos.mpr
    let p : patternSet θ (supportBase B horizontalReal) :=
      restriction θ B horizontalReal
        ⟨patternAt x B (0,d-lower B),hx (0,d-lower B)⟩
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    change 2 ≤ extensionCount (restriction θ B horizontalReal) p
    simpa [p] using hamb 0
  have hpositive : 0<h := by
    have hlt := ambiguity_count_lt_edge θ B horizontalReal hbudget
    rw [hedge] at hlt
    dsimp [h]
    omega
  let T : Finset ℤ := Finset.Ioc (lower B) (upper B)
  have hrowrun (t : T) : ∃ l : ℤ,
      ∀ j : Fin h, (l+(j.val:ℤ),t.val) ∈ upperBase B := by
    have ht := Finset.mem_Ioc.mp t.property
    have hcard : h ≤ (row B t.val).card :=
      hB.row_card t.val (le_of_lt ht.1) ht.2
    have hrow : (row B t.val).Nonempty :=
      Finset.card_pos.mp (by omega : 0<(row B t.val).card)
    obtain ⟨l,hl⟩ := row_run hB.latticeConvex t.val hrow
    refine ⟨l,?_⟩
    intro j
    have hsrow : (l+(j.val:ℤ),t.val) ∈ row B t.val := by
      rw [hl]
      exact Finset.mem_image.mpr
        ⟨j.val,Finset.mem_range.mpr (lt_of_lt_of_le j.isLt hcard),rfl⟩
    rw [upperBase_eq_filter]
    exact Finset.mem_filter.mpr ⟨(row_subset B t.val) hsrow,ht.1⟩
  choose l hl using hrowrun
  let ξ : ℤ → (T → A) := fun i t => x (i+l t,d-lower B+t.val)
  let F : wordSet ξ h →
      {p : patternSet θ (supportBase B horizontalReal) //
        p ∈ ambiguousPatterns θ B horizontalReal} := fun w => by
    let i : ℤ := w.property.choose
    let p : patternSet θ (supportBase B horizontalReal) :=
      restriction θ B horizontalReal
        ⟨patternAt x B (i,d-lower B),hx (i,d-lower B)⟩
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      change 2 ≤ extensionCount (restriction θ B horizontalReal) p
      simpa [p] using hamb i⟩⟩
  have hF : Function.Injective F := by
    intro w w' he
    apply Subtype.ext
    rw [← w.property.choose_spec,← w'.property.choose_spec]
    funext j t
    have hs : (l t+(j.val:ℤ),t.val) ∈ supportBase B horizontalReal :=
      hbase.symm ▸ hl t j
    have heval := congrFun
      (congrArg (fun p : {p : patternSet θ (supportBase B horizontalReal) //
        p ∈ ambiguousPatterns θ B horizontalReal} => p.val.val) he)
      ⟨(l t+(j.val:ℤ),t.val),hs⟩
    change x ((w.property.choose,d-lower B)+(l t+(j.val:ℤ),t.val)) =
      x ((w'.property.choose,d-lower B)+(l t+(j.val:ℤ),t.val)) at heval
    change x (w.property.choose+(j.val:ℤ)+l t,d-lower B+t.val) =
      x (w'.property.choose+(j.val:ℤ)+l t,d-lower B+t.val)
    convert heval using 1 <;> congr 1 <;> ext <;>
      simp only [Prod.fst_add,Prod.snd_add] <;> omega
  have hcard : wordComplexity ξ h ≤
      (ambiguousPatterns θ B horizontalReal).card := by
    have hh := Fintype.card_le_of_injective F hF
    simpa [wordComplexity,Nat.card_eq_fintype_card,
      Fintype.card_coe] using hh
  have hlt := ambiguity_count_lt_edge θ B horizontalReal hbudget
  rw [hedge] at hlt
  have hh : h+1=(bottomEdge B).card := by dsimp [h]; omega
  have hbound : wordComplexity ξ h ≤ h := by omega
  obtain ⟨p,hp,hpbound,hper⟩ := morse_hedlund_bounded ξ hbound
  refine ⟨p,hp,hpbound,?_⟩
  intro z hzlow hzhigh
  let tval : ℤ := z.2-d+lower B
  have ht : tval ∈ T := Finset.mem_Ioc.mpr (by dsimp [tval]; omega)
  let t : T := ⟨tval,ht⟩
  have hpoint := congrFun (hper (z.1-l t)) t
  change x ((z.1-l t+(p:ℤ))+l t,d-lower B+t.val) =
    x ((z.1-l t)+l t,d-lower B+t.val) at hpoint
  convert hpoint using 1 <;> congr 1 <;> ext <;>
    simp [horizontal,t,tval] <;> omega

end

end NivatTrial.ColleAmbiguousBandBound
