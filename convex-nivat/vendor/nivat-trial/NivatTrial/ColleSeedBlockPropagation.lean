import NivatTrial.ColleLocalBoundaryPropagation

/-! A consecutive seed block one site shorter than a generated exposed edge
determines the entire row, provided the finite band immediately above is
already matched. This is the local downward step in the second-direction
parallel-cell argument. -/

namespace NivatTrial.ColleSeedBlockPropagation

open NivatTrial.Dynamics NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating NivatTrial.ColleVertexGeometry
open NivatTrial.ColleLocalSubshift
open NivatTrial.ColleLocalBoundaryPropagation
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

theorem whole_row_of_seed_block
    (θ : G → A) (B : Finset G) (hgen : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x)
    (hy : LocalAdmissible θ B y)
    (d b : ℤ)
    (habove : ∀ z : G, d<z.2 →
      z.2≤d+upper B-lower B → x z=y z)
    (hseed : ∀ j : ℤ, b≤j →
      j<b+((bottomEdge B).card:ℤ)-1 →
      x (j,d)=y (j,d)) :
    ∀ z : G, z.2=d → x z=y z := by
  obtain ⟨l,r,hlr,heq,hgl,hgr⟩ := bottom_interval_generated θ B hgen
  have hcard : ((bottomEdge B).card:ℤ)=r-l+1 := by
    rw [heq,Finset.card_image_of_injective _
      (fun i j he => congrArg Prod.fst he)]
    rw [Int.card_Icc]
    omega
  let right : G := (r,lower B)
  let a : G := (b-l,d-lower B)
  have haheight : a.2+lower B=d := by dsimp [a]; omega
  have hpat : patternAt x (B.erase right) a =
      patternAt y (B.erase right) a := by
    funext s
    have hsB := (Finset.mem_erase.mp s.property).2
    by_cases hsrow : s.val.2=lower B
    · have hsedge : s.val ∈ bottomEdge B :=
        (mem_row B (lower B) s.val).mpr ⟨hsB,hsrow⟩
      rw [heq] at hsedge
      obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hsedge
      have hsj : s.val=(j,lower B) := hjs.symm
      have hjrange := Finset.mem_Icc.mp hj
      have hsne : s.val≠right := (Finset.mem_erase.mp s.property).1
      have hjlt : j<r := by
        by_contra hn
        apply hsne
        rw [hsj]
        exact Prod.ext (by dsimp [right]; omega) rfl
      have hseedj := hseed (b-l+j) (by omega) (by rw [hcard]; omega)
      change x (a+s.val)=y (a+s.val)
      have he : a+s.val=(b-l+j,d) := by
        rw [hsj]
        ext <;> dsimp [a] <;> omega
      rw [he]
      exact hseedj
    · have hmin := lower_le_of_mem hsB
      have hmax := le_upper_of_mem hsB
      change x (a+s.val)=y (a+s.val)
      apply habove
      · change d<(d-lower B)+s.val.2
        omega
      · change (d-lower B)+s.val.2≤d+upper B-lower B
        omega
  have hright := generated_determines_local θ B right hgr hx hy a a hpat
  have hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s) := by
    intro s hs
    by_cases hsright : s=right
    · simpa [hsright] using hright
    · rw [heq] at hs
      obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hs
      have hsj : s=(j,lower B) := hjs.symm
      have hjrange := Finset.mem_Icc.mp hj
      have hjlt : j<r := by
        by_contra hn
        apply hsright
        rw [hsj]
        exact Prod.ext (by dsimp [right]; omega) rfl
      have hseedj := hseed (b-l+j) (by omega) (by rw [hcard]; omega)
      have he : a+s=(b-l+j,d) := by
        rw [hsj]
        ext <;> dsimp [a] <;> omega
      rw [he]
      exact hseedj
  exact bottom_block_forces_whole_row_local θ B hgen hx hy d habove
    a haheight hblock

end
end NivatTrial.ColleSeedBlockPropagation
