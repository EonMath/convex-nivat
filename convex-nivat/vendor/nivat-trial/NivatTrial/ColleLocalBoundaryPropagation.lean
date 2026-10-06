import NivatTrial.ColleBoundaryPropagation
import NivatTrial.ColleStripPeriod

/-! The generated endpoints of a convex window propagate equality along an
entire exposed row. Only the finitely many rows actually touched by the
window need to agree; this local form supports adjacent-strip induction. -/

namespace NivatTrial.ColleLocalBoundaryPropagation

open NivatTrial.Dynamics NivatTrial.AmbiguityPropagation
open NivatTrial.BalancedWindows NivatTrial.ColleAmbiguity
open NivatTrial.GeneratingWindows NivatTrial.ColleGenerating
open NivatTrial.ColleVertexGeometry NivatTrial.ColleInterfaceAmbiguity
open NivatTrial.ColleBalancedRows NivatTrial.ColleLocalSubshift
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [Fintype A]

theorem bottom_block_forces_whole_row_local
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x)
    (hy : LocalAdmissible θ B y)
    (d : ℤ)
    (habove : ∀ z : G, d < z.2 →
      z.2 ≤ d + upper B - lower B → x z = y z)
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
  have hdetL := generated_determines_local θ B left hgl hx hy
  have hdetR := generated_determines_local θ B right hgr hx hy
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
          have hsupper : (aR+s.val).2 ≤ d + upper B - lower B := by
            have hsmax := le_upper_of_mem hsB
            dsimp [aR]
            omega
          exact habove _ hsabove hsupper
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
          have hsupper : (aL+s.val).2 ≤ d + upper B - lower B := by
            have hsmax := le_upper_of_mem hsB
            dsimp [aL]
            omega
          exact habove _ hsabove hsupper
      have hright := hdetR aR aR hrightpat
      have hleft := hdetL aL aL hleftpat
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

end

end NivatTrial.ColleLocalBoundaryPropagation
