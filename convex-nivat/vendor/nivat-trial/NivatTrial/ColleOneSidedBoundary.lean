import NivatTrial.ColleLocalBoundaryPropagation

/-! The one-sided version of generated-edge propagation. A matched exposed
block at a distant anchor can be propagated backwards through a finite
corridor of matched interior patches. Its contrapositive turns a fixed
boundary defect into defects on every sufficiently distant exposed block. -/

namespace NivatTrial.ColleOneSidedBoundary

open NivatTrial.Dynamics NivatTrial.BalancedWindows
open NivatTrial.ColleLocalSubshift NivatTrial.ColleVertexGeometry
open NivatTrial.ColleGenerating NivatTrial.GeneratingWindows
open scoped Classical

set_option maxHeartbeats 1000000
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

theorem bottom_block_forces_left_corridor
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x)
    (hy : LocalAdmissible θ B y)
    (a : G) (N : ℕ)
    (hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s))
    (hinterior : ∀ k : ℕ, k ≤ N → ∀ s ∈ B,
      lower B < s.2 →
      x (a-(k:ℤ) • ((1,0):G)+s)=
        y (a-(k:ℤ) • ((1,0):G)+s)) :
    ∃ l r : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)) ∧
      ∀ j : ℤ, a.1+l-(N:ℤ)≤j → j≤a.1+r →
        x (j,a.2+lower B)=y (j,a.2+lower B) := by
  obtain ⟨l,r,hlr,heq,hgl,hgr⟩ := bottom_interval_generated θ B hB
  let left : G := (l,lower B)
  let L : ℤ := a.1+l
  let R : ℤ := a.1+r
  have hcoords {s : G} (hs : s ∈ bottomEdge B) :
      l ≤ s.1 ∧ s.1 ≤ r ∧ s.2 = lower B := by
    rw [heq] at hs
    obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hs
    have hsj : s=(j,lower B) := hjs.symm
    subst s
    exact ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,rfl⟩
  have hbase : ∀ j : ℤ, L≤j → j≤R →
      x (j,a.2+lower B)=y (j,a.2+lower B) := by
    intro j hjL hjR
    have hs : (j-a.1,lower B) ∈ bottomEdge B := by
      rw [heq]
      exact Finset.mem_image.mpr
        ⟨j-a.1,Finset.mem_Icc.mpr (by dsimp [L,R] at hjL hjR ⊢; omega),rfl⟩
    have hh := hblock _ hs
    have he : a+(j-a.1,lower B)=(j,a.2+lower B) := by
      ext <;> simp <;> omega
    rw [he] at hh
    exact hh
  have hwide : ∀ k : ℕ, k≤N → ∀ j : ℤ,
      L-(k:ℤ)≤j → j≤R →
      x (j,a.2+lower B)=y (j,a.2+lower B) := by
    intro k
    induction k with
    | zero =>
      intro _ j hjL hjR
      exact hbase j (by simpa using hjL) hjR
    | succ k ih =>
      intro hk j hjL hjR
      by_cases hfar : j < L-(k:ℤ)
      · have hj : j=L-(k:ℤ)-1 := by omega
        subst j
        let ak : G := a-((k:ℤ)+1,0)
        have hpat : patternAt x (B.erase left) ak =
            patternAt y (B.erase left) ak := by
          funext s
          have hsB := (Finset.mem_erase.mp s.property).2
          by_cases hsrow : s.val.2=lower B
          · have hsedge : s.val ∈ bottomEdge B :=
              (mem_row B (lower B) s.val).mpr ⟨hsB,hsrow⟩
            obtain ⟨hsl,hsr,_⟩ := hcoords hsedge
            have hsne : s.val≠left := (Finset.mem_erase.mp s.property).1
            have hsstrict : l<s.val.1 := by
              by_contra hh
              apply hsne
              exact Prod.ext (by dsimp [left]; omega)
                (by dsimp [left]; exact hsrow)
            have hval := ih (by omega) (ak.1+s.val.1)
              (by dsimp [ak,L]; omega) (by dsimp [ak,R]; omega)
            change x (ak+s.val)=y (ak+s.val)
            have he : ak+s.val=(ak.1+s.val.1,a.2+lower B) := by
              ext <;> dsimp [ak] <;> omega
            rw [he]
            exact hval
          · have hstrict : lower B<s.val.2 := by
              have hmin := lower_le_of_mem hsB
              omega
            have hh := hinterior (k+1) hk s.val hsB hstrict
            change x (ak+s.val)=y (ak+s.val)
            convert hh using 1 <;> congr 1 <;> ext <;>
              simp [ak] <;> omega
        have hnew := generated_determines_local θ B left hgl
          hx hy ak ak hpat
        have he : ak+left=(L-(k:ℤ)-1,a.2+lower B) := by
          ext <;> dsimp [ak,left,L] <;> omega
        rw [he] at hnew
        exact hnew
      · exact ih (by omega) j (by omega) hjR
  refine ⟨l,r,heq,?_⟩
  intro j hjL hjR
  exact hwide N le_rfl j hjL hjR

theorem exposed_defect_of_interior_corridor
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x)
    (hy : LocalAdmissible θ B y)
    (a w : G) (N : ℕ)
    (hwrow : w.2=a.2+lower B)
    (hwin : ∀ l r : ℤ,
      bottomEdge B=(Finset.Icc l r).image (fun j => (j,lower B)) →
      a.1+l-(N:ℤ)≤w.1 ∧ w.1≤a.1+r)
    (hbad : x w≠y w)
    (hinterior : ∀ k : ℕ, k≤N → ∀ s ∈ B,
      lower B<s.2 →
      x (a-(k:ℤ) • ((1,0):G)+s)=
        y (a-(k:ℤ) • ((1,0):G)+s)) :
    ∃ s ∈ bottomEdge B, x (a+s)≠y (a+s) := by
  by_contra hn
  push Not at hn
  have hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s) := by
    intro s hs
    exact hn s hs
  obtain ⟨l,r,heq,hwhole⟩ :=
    bottom_block_forces_left_corridor θ B hB hx hy a N hblock hinterior
  have hpos := hwin l r heq
  have he : w=(w.1,a.2+lower B) := Prod.ext rfl hwrow
  exact hbad (by rw [he]; exact hwhole w.1 hpos.1 hpos.2)

/-- The companion sweep uses the generated right endpoint. This is the
orientation required when a convex agreement region recedes to the left. -/
theorem bottom_block_forces_right_corridor
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x)
    (hy : LocalAdmissible θ B y)
    (a : G) (N : ℕ)
    (hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s))
    (hinterior : ∀ k : ℕ, k ≤ N → ∀ s ∈ B,
      lower B < s.2 →
      x (a+(k:ℤ) • ((1,0):G)+s)=
        y (a+(k:ℤ) • ((1,0):G)+s)) :
    ∃ l r : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)) ∧
      ∀ j : ℤ, a.1+l≤j → j≤a.1+r+(N:ℤ) →
        x (j,a.2+lower B)=y (j,a.2+lower B) := by
  obtain ⟨l,r,hlr,heq,hgl,hgr⟩ := bottom_interval_generated θ B hB
  let right : G := (r,lower B)
  let L : ℤ := a.1+l
  let R : ℤ := a.1+r
  have hcoords {s : G} (hs : s ∈ bottomEdge B) :
      l ≤ s.1 ∧ s.1 ≤ r ∧ s.2 = lower B := by
    rw [heq] at hs
    obtain ⟨j,hj,hjs⟩ := Finset.mem_image.mp hs
    have hsj : s=(j,lower B) := hjs.symm
    subst s
    exact ⟨(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,rfl⟩
  have hbase : ∀ j : ℤ, L≤j → j≤R →
      x (j,a.2+lower B)=y (j,a.2+lower B) := by
    intro j hjL hjR
    have hs : (j-a.1,lower B) ∈ bottomEdge B := by
      rw [heq]
      exact Finset.mem_image.mpr
        ⟨j-a.1,Finset.mem_Icc.mpr (by dsimp [L,R] at hjL hjR ⊢; omega),rfl⟩
    have hh := hblock _ hs
    have he : a+(j-a.1,lower B)=(j,a.2+lower B) := by
      ext <;> simp <;> omega
    rw [he] at hh
    exact hh
  have hwide : ∀ k : ℕ, k≤N → ∀ j : ℤ,
      L≤j → j≤R+(k:ℤ) →
      x (j,a.2+lower B)=y (j,a.2+lower B) := by
    intro k
    induction k with
    | zero =>
      intro _ j hjL hjR
      exact hbase j hjL (by simpa using hjR)
    | succ k ih =>
      intro hk j hjL hjR
      by_cases hfar : R+(k:ℤ)<j
      · have hj : j=R+(k:ℤ)+1 := by omega
        subst j
        let ak : G := a+((k:ℤ)+1,0)
        have hpat : patternAt x (B.erase right) ak =
            patternAt y (B.erase right) ak := by
          funext s
          have hsB := (Finset.mem_erase.mp s.property).2
          by_cases hsrow : s.val.2=lower B
          · have hsedge : s.val ∈ bottomEdge B :=
              (mem_row B (lower B) s.val).mpr ⟨hsB,hsrow⟩
            obtain ⟨hsl,hsr,_⟩ := hcoords hsedge
            have hsne : s.val≠right := (Finset.mem_erase.mp s.property).1
            have hsstrict : s.val.1<r := by
              by_contra hh
              apply hsne
              exact Prod.ext (by dsimp [right]; omega)
                (by dsimp [right]; exact hsrow)
            have hval := ih (by omega) (ak.1+s.val.1)
              (by dsimp [ak,L]; omega) (by dsimp [ak,R]; omega)
            change x (ak+s.val)=y (ak+s.val)
            have he : ak+s.val=(ak.1+s.val.1,a.2+lower B) := by
              ext <;> dsimp [ak] <;> omega
            rw [he]
            exact hval
          · have hstrict : lower B<s.val.2 := by
              have hmin := lower_le_of_mem hsB
              omega
            have hh := hinterior (k+1) hk s.val hsB hstrict
            change x (ak+s.val)=y (ak+s.val)
            convert hh using 1 <;> congr 1 <;> ext <;>
              simp [ak] <;> omega
        have hnew := generated_determines_local θ B right hgr
          hx hy ak ak hpat
        have he : ak+right=(R+(k:ℤ)+1,a.2+lower B) := by
          ext <;> dsimp [ak,right,R] <;> omega
        rw [he] at hnew
        exact hnew
      · exact ih (by omega) j hjL (by omega)
  refine ⟨l,r,heq,?_⟩
  intro j hjL hjR
  exact hwide N le_rfl j hjL hjR

theorem exposed_defect_of_interior_right_corridor
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : LocalAdmissible θ B x)
    (hy : LocalAdmissible θ B y)
    (a w : G) (N : ℕ)
    (hwrow : w.2=a.2+lower B)
    (hwin : ∀ l r : ℤ,
      bottomEdge B=(Finset.Icc l r).image (fun j => (j,lower B)) →
      a.1+l≤w.1 ∧ w.1≤a.1+r+(N:ℤ))
    (hbad : x w≠y w)
    (hinterior : ∀ k : ℕ, k≤N → ∀ s ∈ B,
      lower B<s.2 →
      x (a+(k:ℤ) • ((1,0):G)+s)=
        y (a+(k:ℤ) • ((1,0):G)+s)) :
    ∃ s ∈ bottomEdge B, x (a+s)≠y (a+s) := by
  by_contra hn
  push Not at hn
  have hblock : ∀ s ∈ bottomEdge B, x (a+s)=y (a+s) := by
    intro s hs
    exact hn s hs
  obtain ⟨l,r,heq,hwhole⟩ :=
    bottom_block_forces_right_corridor θ B hB hx hy a N hblock hinterior
  have hpos := hwin l r heq
  have he : w=(w.1,a.2+lower B) := Prod.ext rfl hwrow
  exact hbad (by rw [he]; exact hwhole w.1 hpos.1 hpos.2)

end

end NivatTrial.ColleOneSidedBoundary
