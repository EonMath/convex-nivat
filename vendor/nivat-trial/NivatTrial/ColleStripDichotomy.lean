import NivatTrial.ColleHorizontalSplice
import NivatTrial.ColleAmbiguousBandBound

/-! Adjacent-strip dichotomy. If the old period extends to the next row,
we keep it. Otherwise splice a shifted copy along that row. The splice is
locally admissible; generated edge endpoints imply that every translated
base pattern is ambiguous. The quantitative nonunique-extension theorem
then supplies a new period bounded by twice the exposed-edge budget. -/

namespace NivatTrial.ColleStripDichotomy

open NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.BalancedWindows NivatTrial.ColleAmbiguity
open NivatTrial.ColleBalancedRows NivatTrial.ColleGenerating
open NivatTrial.ColleLocalSubshift NivatTrial.ColleHorizontalSplice
open NivatTrial.ColleLocalBoundaryPropagation NivatTrial.ColleNonuniqueStrip
open NivatTrial.ColleAmbiguousBandBound
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

private def horizontal : G := (1,0)
private def horizontalReal : ℝ × ℝ := (1,0)

theorem adjacent_strip_bounded_period
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B) (hbalanced : MinusBalanced θ B)
    {x : G → A} (hx : x ∈ languageHull θ)
    (d : ℤ) (p : ℕ) (hp : 0 < p)
    (hpedge : p ≤ 2*((bottomEdge B).card - 1))
    (hperiod : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B →
      x (z+(p:ℤ) • horizontal) = x z) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2*((bottomEdge B).card-1) ∧
      ∀ z : G, d ≤ z.2 → z.2 ≤ d + upper B - lower B →
        x (z+(q:ℤ) • horizontal) = x z := by
  by_cases hnew : ∀ z : G, z.2=d →
      x (z+(p:ℤ) • horizontal) = x z
  · refine ⟨p,hp,by omega,?_⟩
    intro z hzl hzu
    by_cases hz : z.2=d
    · exact hnew z hz
    · exact hperiod z (by omega) hzu
  · push Not at hnew
    obtain ⟨z0,hz0,hfail⟩ := hnew
    let sh : G := (p:ℤ) • horizontal
    let xshift : G → A := shift sh x
    let y : G → A := spliceAtRow d x xshift
    have hxlocal : LocalAdmissible θ B x := localAdmissible_of_hull hx
    have hshiftlocal : LocalAdmissible θ B xshift :=
      localAdmissible_shift hxlocal sh
    have hmatch : ∀ z : G, d < z.2 →
        z.2 ≤ d+upper B-lower B → x z = xshift z := by
      intro z hzlow hzhigh
      have hh := hperiod z hzlow hzhigh
      simpa [xshift,sh,shift,add_comm] using hh.symm
    have hylocal : LocalAdmissible θ B y :=
      localAdmissible_spliceAtRow θ B d hxlocal hshiftlocal hmatch
    have habove : ∀ z : G, d < z.2 →
        z.2 ≤ d+upper B-lower B → x z = y z := by
      intro z hzlow _
      dsimp [y,spliceAtRow]
      split_ifs with hc
      · omega
      · rfl
    have hrowneq : ¬ ∀ z : G, z.2=d → x z=y z := by
      intro heq
      have hh := heq z0 hz0
      have hyz : y z0 = x (z0+sh) := by
        dsimp [y,spliceAtRow,xshift,shift]
        split_ifs with hc
        · rw [add_comm]
        · omega
      apply hfail
      simpa only [sh] using (hh.trans hyz).symm
    have hbaseEq : supportBase B horizontalReal = upperBase B :=
      horizontal_supportBase_eq_upperBase B hbalanced.nonempty
    have hamb : ∀ i : ℤ,
        2 ≤ extensionCount (restriction θ B horizontalReal)
          (restriction θ B horizontalReal
            ⟨patternAt x B (i,d-lower B),
              localAdmissible_of_hull hx (i,d-lower B)⟩) := by
      intro i
      let a : G := (i,d-lower B)
      let px : patternSet θ B := ⟨patternAt x B a,hxlocal a⟩
      let py : patternSet θ B := ⟨patternAt y B a,hylocal a⟩
      have hbase : restriction θ B horizontalReal px =
          restriction θ B horizontalReal py := by
        apply Subtype.ext
        funext s
        have hs' : s.val ∈ upperBase B := hbaseEq ▸ s.property
        have hsheight : lower B < s.val.2 := by
          rw [upperBase_eq_filter] at hs'
          exact (Finset.mem_filter.mp hs').2
        have hheight : d < (a+s.val).2 := by
          change d < a.2+s.val.2
          dsimp [a]
          omega
        change d < a.2+s.val.2 at hheight
        change x (a+s.val)=y (a+s.val)
        dsimp [y,spliceAtRow]
        split_ifs with hc
        · omega
        · rfl
      have hne : px ≠ py := by
        intro heq
        have hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s) := by
          intro s hs
          have hsB := (mem_row B (lower B) s).mp hs |>.1
          exact congrFun (congrArg Subtype.val heq) ⟨s,hsB⟩
        have haheight : a.2+lower B=d := by dsimp [a]; omega
        exact hrowneq (bottom_block_forces_whole_row_local θ B hgen
          hxlocal hylocal d habove a haheight hblock)
      have hcount : 2 ≤ extensionCount (restriction θ B horizontalReal)
          (restriction θ B horizontalReal px) :=
        two_extensions_imply_count rfl hbase.symm hne
      simpa [px,a] using hcount
    obtain ⟨p0,hp0,hp0edge,hperiod0⟩ :=
      ambiguous_inner_band_bounded_period θ B hbalanced x hxlocal d hamb
    exact ambiguous_extension_propagates_bounded_period θ B hgen
      hbalanced hx d p0 hp0 hp0edge hperiod0 hamb

end

end NivatTrial.ColleStripDichotomy
