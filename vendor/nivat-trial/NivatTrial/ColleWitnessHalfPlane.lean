import NivatTrial.ColleHalfPlaneAmbiguity
import NivatTrial.ColleBoundaryPropagation

/-! Keep both original one-sided nonexpansive witnesses and their last
disagreement point while extracting half-plane periods. Neither witness is
replaced by a compactness recentering, so subsequent regional arguments can
use the same actual interface. -/

namespace NivatTrial.ColleWitnessHalfPlane

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.Nonexpansive
open NivatTrial.BalancedWindows NivatTrial.ColleAmbiguity
open NivatTrial.ColleBalancedRows NivatTrial.ColleGenerating
open NivatTrial.ColleInterfaceAmbiguity NivatTrial.ColleBoundaryPropagation
open NivatTrial.ColleHalfPlaneAmbiguity NivatTrial.ColleLocalSubshift
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

private def horizontal : G := (1,0)
private def horizontalReal : ℝ × ℝ := (1,0)

theorem periodic_halfPlanes_of_last_disagreement
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B) (hB : MinusBalanced θ B)
    {x y : G → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (d : ℤ) (w : G) (hw : w.2=d) (hwne : x w ≠ y w)
    (hhighest : ∀ z : G, d<z.2 → x z=y z) :
    let Q := Nat.factorial (2*((bottomEdge B).card-1))
    0<Q ∧
      (∀ z : G, z.2≤d+upper B-lower B →
        x (z+(Q:ℤ) • horizontal)=x z) ∧
      (∀ z : G, z.2≤d+upper B-lower B →
        y (z+(Q:ℤ) • horizontal)=y z) := by
  have hbaseEq : supportBase B horizontalReal = upperBase B :=
    horizontal_supportBase_eq_upperBase B hgen.nonempty
  have hedgeEq : supportEdge B horizontalReal = bottomEdge B :=
    horizontal_supportEdge_eq_bottomEdge B hgen.nonempty
  have hlocalX : LocalAdmissible θ B x := localAdmissible_of_hull hx
  have hlocalY : LocalAdmissible θ B y := localAdmissible_of_hull hy
  have htwo (i : ℤ) :
      let a : G := (i,d-lower B)
      let px : patternSet θ B := ⟨patternAt x B a,hlocalX a⟩
      let py : patternSet θ B := ⟨patternAt y B a,hlocalY a⟩
      restriction θ B horizontalReal px = restriction θ B horizontalReal py ∧
        px ≠ py := by
    dsimp
    let a : G := (i,d-lower B)
    let px : patternSet θ B := ⟨patternAt x B a,hlocalX a⟩
    let py : patternSet θ B := ⟨patternAt y B a,hlocalY a⟩
    have hbase : ∀ s ∈ supportBase B horizontalReal,
        x (a+s)=y (a+s) := by
      intro s hs
      have hs' : s ∈ upperBase B := hbaseEq ▸ hs
      have hsheight : lower B<s.2 := by
        rw [upperBase_eq_filter] at hs'
        exact (Finset.mem_filter.mp hs').2
      apply hhighest
      change d<a.2+s.2
      dsimp [a]
      omega
    have hres : restriction θ B horizontalReal px =
        restriction θ B horizontalReal py := by
      apply Subtype.ext
      funext s
      exact hbase s.val s.property
    have hpne : px ≠ py := by
      intro heq
      have hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s) := by
        intro s hs
        have hsB : s ∈ B := (mem_row B (lower B) s).mp hs |>.1
        exact congrFun (congrArg Subtype.val heq) ⟨s,hsB⟩
      have haheight : a.2+lower B=d := by dsimp [a]; omega
      have hwhole := bottom_block_forces_whole_row θ B hgen hx hy
        d hhighest a haheight hblock
      exact hwne (hwhole w hw)
    exact ⟨hres,hpne⟩
  have hambX : ∀ i : ℤ,
      2 ≤ extensionCount (restriction θ B horizontalReal)
        (restriction θ B horizontalReal
          ⟨patternAt x B (i,d-lower B),
            localAdmissible_of_hull hx (i,d-lower B)⟩) := by
    intro i
    let a : G := (i,d-lower B)
    let px : patternSet θ B := ⟨patternAt x B a,hlocalX a⟩
    let py : patternSet θ B := ⟨patternAt y B a,hlocalY a⟩
    have hh := htwo i
    change restriction θ B horizontalReal px =
      restriction θ B horizontalReal py ∧ px ≠ py at hh
    have hc : 2 ≤ extensionCount (restriction θ B horizontalReal)
        (restriction θ B horizontalReal px) :=
      two_extensions_imply_count rfl hh.1.symm hh.2
    simpa [px,a] using hc
  have hambY : ∀ i : ℤ,
      2 ≤ extensionCount (restriction θ B horizontalReal)
        (restriction θ B horizontalReal
          ⟨patternAt y B (i,d-lower B),
            localAdmissible_of_hull hy (i,d-lower B)⟩) := by
    intro i
    let a : G := (i,d-lower B)
    let px : patternSet θ B := ⟨patternAt x B a,hlocalX a⟩
    let py : patternSet θ B := ⟨patternAt y B a,hlocalY a⟩
    have hh := htwo i
    change restriction θ B horizontalReal px =
      restriction θ B horizontalReal py ∧ px ≠ py at hh
    have hc : 2 ≤ extensionCount (restriction θ B horizontalReal)
        (restriction θ B horizontalReal py) :=
      two_extensions_imply_count rfl hh.1 hh.2.symm
    simpa [py,a] using hc
  obtain ⟨hQ,hperiodX⟩ := ambiguous_lower_halfPlane_period
    θ B hgen hB hx d hambX
  obtain ⟨_,hperiodY⟩ := ambiguous_lower_halfPlane_period
    θ B hgen hB hy d hambY
  exact ⟨hQ,hperiodX,hperiodY⟩

theorem horizontal_ONED_has_periodic_interface_pair
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B) (hB : MinusBalanced θ B)
    (honed : OneSidedNonexpansive θ horizontalReal) :
    ∃ x : G → A, ∃ hx : x ∈ languageHull θ,
    ∃ y : G → A, ∃ hy : y ∈ languageHull θ,
    ∃ d : ℤ, ∃ w : G,
      w.2=d ∧ x w≠y w ∧
      (∀ z : G, 0≤z.2 → x z=y z) ∧
      (∀ z : G, d<z.2 → x z=y z) ∧
      let Q := Nat.factorial (2*((bottomEdge B).card-1))
      0<Q ∧
        (∀ z : G, z.2≤d+upper B-lower B →
          x (z+(Q:ℤ) • horizontal)=x z) ∧
        (∀ z : G, z.2≤d+upper B-lower B →
          y (z+(Q:ℤ) • horizontal)=y z) := by
  obtain ⟨x,hx,y,hy,hne,hagree⟩ := honed
  have hrowAgree : ∀ z : G, 0≤z.2 → x z=y z := by
    intro z hz
    exact hagree z (by simpa [halfPlane,score,horizontalReal] using hz)
  obtain ⟨d,⟨w,hw,hwne⟩,hhighest⟩ :=
    highest_disagreement_row hrowAgree hne
  obtain ⟨hQ,hxper,hyper⟩ :=
    periodic_halfPlanes_of_last_disagreement θ B hgen hB hx hy
      d w hw hwne hhighest
  exact ⟨x,hx,y,hy,d,w,hw,hwne,hrowAgree,hhighest,hQ,hxper,hyper⟩

end

end NivatTrial.ColleWitnessHalfPlane
