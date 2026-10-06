import NivatTrial.ColleVertexGeometry
import NivatTrial.ColleInterfaceAmbiguity

/-! A generated convex window propagates a matched full bottom-edge block
across an entire adjacent lattice row. Hence the highest disagreement row of
a one-sided interface meets every translated edge block. -/

namespace NivatTrial.ColleBoundaryPropagation

open NivatTrial.Dynamics NivatTrial.AmbiguityPropagation
open NivatTrial.BalancedWindows NivatTrial.ColleAmbiguity
open NivatTrial.GeneratingWindows NivatTrial.ColleGenerating
open NivatTrial.ColleVertexGeometry NivatTrial.ColleInterfaceAmbiguity
open NivatTrial.ColleBalancedRows
open NivatTrial.Nonexpansive NivatTrial.ColleSemiAmbiguity
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [Fintype A]

/-- If two hull points agree strictly above a row and on one translated
bottom edge, generated left and right endpoints propagate agreement over the
whole row. -/
theorem bottom_block_forces_whole_row
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (d : ℤ) (habove : ∀ z : G, d < z.2 → x z = y z)
    (a : G) (haheight : a.2 + lower B = d)
    (hblock : ∀ s ∈ bottomEdge B, x (a+s) = y (a+s)) :
    ∀ z : G, z.2 = d → x z = y z := by
  obtain ⟨l,r,hlr,heq,hgl,hgr⟩ := bottom_interval_generated θ B hB
  let left : G := (l,lower B)
  let right : G := (r,lower B)
  let L : ℤ := a.1+l
  let R : ℤ := a.1+r
  have hcoords {s : G} (hs : s ∈ bottomEdge B) :
      l ≤ s.1 ∧ s.1 ≤ r ∧ s.2 = lower B := by
    rw [heq] at hs
    obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hs
    have hsj : s = (j,lower B) := hjs.symm
    subst s
    exact ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,rfl⟩
  have hbase (j : ℤ) (hj : L ≤ j ∧ j ≤ R) : x (j,d) = y (j,d) := by
    have hs : (j-a.1,lower B) ∈ bottomEdge B := by
      rw [heq]
      apply Finset.mem_image.mpr
      exact ⟨j-a.1,Finset.mem_Icc.mpr (by dsimp [L,R] at hj; omega),rfl⟩
    have hh := hblock _ hs
    have he : a+(j-a.1,lower B) = (j,d) := by
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
      · omega
      · exact haheight
    rw [he] at hh
    exact hh
  have hdetL := generated_determines hgl
  have hdetR := generated_determines hgr
  have hwide : ∀ n : ℕ, ∀ j : ℤ,
      L-(n:ℤ) ≤ j → j ≤ R+(n:ℤ) → x (j,d)=y (j,d) := by
    intro n
    induction n with
    | zero =>
      intro j hlj hjr
      apply hbase j
      simpa using And.intro hlj hjr
    | succ n ih =>
      let aR : G := a+((n:ℤ)+1,0)
      let aL : G := a-((n:ℤ)+1,0)
      have hrightpat : patternAt x (B.erase right) aR =
          patternAt y (B.erase right) aR := by
        funext s
        have hsB := (Finset.mem_erase.mp s.property).2
        by_cases hsrow : s.val.2 = lower B
        · have hsedge : s.val ∈ bottomEdge B :=
            (mem_row B (lower B) s.val).mpr ⟨hsB,hsrow⟩
          obtain ⟨hsl,hsr,_⟩ := hcoords hsedge
          have hsne : s.val ≠ right := (Finset.mem_erase.mp s.property).1
          have hsstrict : s.val.1 < r := by
            by_contra h
            apply hsne
            exact Prod.ext (by dsimp [right]; omega) (by dsimp [right]; exact hsrow)
          have hvalue := ih (aR.1+s.val.1) (by dsimp [aR,L]; omega)
            (by dsimp [aR,R]; omega)
          change x (aR+s.val) = y (aR+s.val)
          have he : aR+s.val = (aR.1+s.val.1,d) := by
            apply Prod.ext
            · rfl
            · dsimp [aR]
              omega
          rw [he]
          exact hvalue
        · have hsabove : d < (aR+s.val).2 := by
            have hsmin := lower_le_of_mem hsB
            dsimp [aR]
            omega
          exact habove _ hsabove
      have hleftpat : patternAt x (B.erase left) aL =
          patternAt y (B.erase left) aL := by
        funext s
        have hsB := (Finset.mem_erase.mp s.property).2
        by_cases hsrow : s.val.2 = lower B
        · have hsedge : s.val ∈ bottomEdge B :=
            (mem_row B (lower B) s.val).mpr ⟨hsB,hsrow⟩
          obtain ⟨hsl,hsr,_⟩ := hcoords hsedge
          have hsne : s.val ≠ left := (Finset.mem_erase.mp s.property).1
          have hsstrict : l < s.val.1 := by
            by_contra h
            apply hsne
            exact Prod.ext (by dsimp [left]; omega) (by dsimp [left]; exact hsrow)
          have hvalue := ih (aL.1+s.val.1) (by dsimp [aL,L]; omega)
            (by dsimp [aL,R]; omega)
          change x (aL+s.val) = y (aL+s.val)
          have he : aL+s.val = (aL.1+s.val.1,d) := by
            apply Prod.ext
            · rfl
            · dsimp [aL]
              omega
          rw [he]
          exact hvalue
        · have hsabove : d < (aL+s.val).2 := by
            have hsmin := lower_le_of_mem hsB
            dsimp [aL]
            omega
          exact habove _ hsabove
      have hright := hdetR x hx y hy aR aR hrightpat
      have hleft := hdetL x hx y hy aL aL hleftpat
      have hright' : x (R+(n:ℤ)+1,d)=y (R+(n:ℤ)+1,d) := by
        have he : aR+right=(R+(n:ℤ)+1,d) := by
          apply Prod.ext <;> dsimp [aR,R,right] <;> omega
        rw [he] at hright
        exact hright
      have hleft' : x (L-(n:ℤ)-1,d)=y (L-(n:ℤ)-1,d) := by
        have he : aL+left=(L-(n:ℤ)-1,d) := by
          apply Prod.ext <;> dsimp [aL,L,left] <;> omega
        rw [he] at hleft
        exact hleft
      intro j hlj hjr
      by_cases hjleft : j < L-(n:ℤ)
      · have he : j=L-(n:ℤ)-1 := by omega
        simpa [he] using hleft'
      by_cases hjright : R+(n:ℤ)<j
      · have he : j=R+(n:ℤ)+1 := by omega
        simpa [he] using hright'
      exact ih j (by omega) (by omega)
  intro z hz
  obtain ⟨n,hn⟩ := exists_nat_gt
    (max ((L:ℝ)-(z.1:ℝ)) ((z.1:ℝ)-(R:ℝ)))
  have hl : L-(n:ℤ) ≤ z.1 := by
    have h : (L:ℝ)-(z.1:ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact_mod_cast (by linarith : (L:ℝ)-(n:ℝ) ≤ (z.1:ℝ))
  have hr : z.1 ≤ R+(n:ℤ) := by
    have h : (z.1:ℝ)-(R:ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
    exact_mod_cast (by linarith : (z.1:ℝ) ≤ (R:ℝ)+(n:ℝ))
  have he : z = (z.1,d) := Prod.ext rfl hz
  rw [he]
  exact hwide n z.1 hl hr

/-- The generating rule turns the highest interface row into an ambiguous
configuration at *every* horizontal anchor, not merely at one local patch. -/
theorem exists_fully_ambiguous_of_horizontal_ONED
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    (honed : OneSidedNonexpansive θ (1,0)) :
    ∃ ξ : G → A, ∃ hξ : ξ ∈ languageHull θ,
      SemiAmbiguous θ B (1,0) (1,0) ξ hξ 0 := by
  obtain ⟨x,hx,y,hy,hne,hagree⟩ := honed
  have hrowAgree : ∀ z : G, 0 ≤ z.2 → x z = y z := by
    intro z hz
    exact hagree z (by simpa [halfPlane, score] using hz)
  obtain ⟨d,⟨w,hw,hwne⟩,hhighest⟩ :=
    highest_disagreement_row hrowAgree hne
  let a₀ : G := (0,d-lower B)
  let ξ : G → A := shift a₀ x
  have hξ : ξ ∈ languageHull θ := shift_mem_languageHull hx a₀
  refine ⟨ξ,hξ,?_⟩
  intro i _
  let a : G := a₀+i • ((1,0):G)
  have haheight : a.2+lower B=d := by
    dsimp [a,a₀]
    simp
  have hbase : ∀ s ∈ supportBase B (1,0), x (a+s)=y (a+s) := by
    intro s hs
    have hsup : s ∈ upperBase B := by
      rw [← horizontal_supportBase_eq_upperBase B hB.nonempty]
      exact hs
    have hslt : lower B < s.2 := by
      rw [upperBase_eq_filter] at hsup
      exact (Finset.mem_filter.mp hsup).2
    apply hhighest
    have hheight : (a+s).2=a.2+s.2 := rfl
    rw [hheight]
    omega
  have hedge : ∃ s ∈ supportEdge B (1,0), x (a+s) ≠ y (a+s) := by
    by_contra h
    have hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s) := by
      intro s hs
      by_contra hsne
      apply h
      have heq : supportEdge B (1,0) = bottomEdge B :=
        horizontal_supportEdge_eq_bottomEdge B hB.nonempty
      exact ⟨s,heq.symm ▸ hs,hsne⟩
    exact hwne (bottom_block_forces_whole_row θ B hB hx hy d hhighest
      a haheight hblock w hw)
  have hamb := ambiguous_of_two_hull_extensions θ B (1,0) hx hy a hbase hedge
  have hpat : patternAt ξ (supportBase B (1,0)) (i • ((1,0):G)) =
      patternAt x (supportBase B (1,0)) a := by
    funext s
    simp [patternAt,ξ,shift,a,add_assoc,add_comm,add_left_comm]
  have hsubtype :
      (⟨patternAt ξ (supportBase B (1,0)) (i • ((1,0):G)),
        patternSet_subset_of_mem_languageHull hξ _ ⟨i • ((1,0):G),rfl⟩⟩ :
          patternSet θ (supportBase B (1,0))) =
      ⟨patternAt x (supportBase B (1,0)) a,
        patternSet_subset_of_mem_languageHull hx _ ⟨a,rfl⟩⟩ :=
    Subtype.ext hpat
  rw [hsubtype]
  exact hamb

end

end NivatTrial.ColleBoundaryPropagation
