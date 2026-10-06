import NivatTrial.ColleGenerating
import NivatTrial.BalancedWindows

/-! Exposed individual lattice sites are removable vertices. This connects
Colle's minimal generating windows to deterministic propagation along a row. -/

namespace NivatTrial.ColleVertexGeometry

open NivatTrial.Dynamics NivatTrial.Zonotope NivatTrial.LatticePolygon
open NivatTrial.Nonexpansive NivatTrial.GeneratingWindows
open NivatTrial.ColleGenerating
open NivatTrial.BalancedWindows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

theorem latticeConvex_erase_uniqueMinimum
    (B : Finset G) (hB : IsLatticeConvex B)
    (v : Plane) (g : G) (hg : UniqueMinimum B v g) :
    IsLatticeConvex (B.erase g) := by
  have hconv : Convex ℝ
      {x : Plane | linearScore v (embed g) < linearScore v x} :=
    convex_halfSpace_gt (linearScore v).isLinear (linearScore v (embed g))
  have hsub : embed '' ((B.erase g : Finset G) : Set G) ⊆
      {x : Plane | linearScore v (embed g) < linearScore v x} := by
    rintro x ⟨s, hs, rfl⟩
    have hs' := Finset.mem_erase.mp hs
    exact hg.2 s hs'.2 hs'.1
  intro z
  constructor
  · intro hz
    have hzB : z ∈ B := (hB z).mp
      (convexHull_mono (Set.image_mono (Finset.erase_subset g B)) hz)
    have hzscore : score v g < score v z := by
      have h := convexHull_min hsub hconv hz
      change linearScore v (embed g) < linearScore v (embed z) at h
      simpa only [linearScore_embed] using h
    exact Finset.mem_erase.mpr ⟨by
      intro he
      subst z
      exact (lt_irrefl _ hzscore),hzB⟩
  · exact mem_windowHull_of_mem _

private theorem horizontal_coordinate_bounds (B : Finset G) (hB : B.Nonempty)
    (g : G) (hg : g ∈ B) :
    ∃ M : ℤ, 0 < M ∧ ∀ s ∈ B, -(M-1) ≤ s.1-g.1 ∧ s.1-g.1 ≤ M-1 := by
  let X := B.image Prod.fst
  have hX : X.Nonempty := hB.image _
  let l := X.min' hX
  let r := X.max' hX
  let M := r-l+1
  have hlr : l ≤ r := Finset.min'_le_max' X hX
  have hgX : g.1 ∈ X := Finset.mem_image.mpr ⟨g,hg,rfl⟩
  have hgl : l ≤ g.1 := Finset.min'_le X _ hgX
  have hgr : g.1 ≤ r := Finset.le_max' X _ hgX
  refine ⟨M,by dsimp [M]; omega,?_⟩
  intro s hs
  have hsX : s.1 ∈ X := Finset.mem_image.mpr ⟨s,hs,rfl⟩
  have hsl : l ≤ s.1 := Finset.min'_le X _ hsX
  have hsr : s.1 ≤ r := Finset.le_max' X _ hsX
  dsimp [M]
  omega

theorem bottom_left_uniqueMinimum (B : Finset G) (hB : B.Nonempty)
    (g : G) (hg : g ∈ bottomEdge B)
    (hleft : ∀ s ∈ bottomEdge B, g.1 ≤ s.1) :
    ∃ v : Plane, UniqueMinimum B v g := by
  have hgb := (mem_row B (lower B) g).mp hg
  obtain ⟨M,hM,hbound⟩ := horizontal_coordinate_bounds B hB g hgb.1
  let v : Plane := ((M : ℝ), -1)
  refine ⟨v,hgb.1,?_⟩
  intro s hs hsg
  have hslow := lower_le_of_mem hs
  have hgbot := hgb.2
  have hdelta : 0 < M*(s.2-g.2)+(s.1-g.1) := by
    rcases eq_or_lt_of_le hslow with heq | hlt
    · have hsedge : s ∈ bottomEdge B :=
        (mem_row B (lower B) s).mpr ⟨hs,heq.symm⟩
      have hstrict : g.1 < s.1 := by
        have hle := hleft s hsedge
        have hne : g.1 ≠ s.1 := by
          intro he
          apply hsg
          exact Prod.ext he.symm (heq.symm.trans hgbot.symm)
        omega
      rw [heq.symm.trans hgbot.symm]
      simp only [sub_self, mul_zero, zero_add]
      omega
    · have hb := (hbound s hs).1
      have hmul : 0 ≤ M*(s.2-g.2-1) :=
        mul_nonneg hM.le (by omega)
      nlinarith
  have hreal : (0 : ℝ) < (M:ℝ)*((s.2:ℝ)-(g.2:ℝ))+
      ((s.1:ℝ)-(g.1:ℝ)) := by exact_mod_cast hdelta
  dsimp [v,score]
  linarith

theorem bottom_right_uniqueMinimum (B : Finset G) (hB : B.Nonempty)
    (g : G) (hg : g ∈ bottomEdge B)
    (hright : ∀ s ∈ bottomEdge B, s.1 ≤ g.1) :
    ∃ v : Plane, UniqueMinimum B v g := by
  have hgb := (mem_row B (lower B) g).mp hg
  obtain ⟨M,hM,hbound⟩ := horizontal_coordinate_bounds B hB g hgb.1
  let v : Plane := ((M : ℝ), 1)
  refine ⟨v,hgb.1,?_⟩
  intro s hs hsg
  have hslow := lower_le_of_mem hs
  have hgbot := hgb.2
  have hdelta : 0 < M*(s.2-g.2)-(s.1-g.1) := by
    rcases eq_or_lt_of_le hslow with heq | hlt
    · have hsedge : s ∈ bottomEdge B :=
        (mem_row B (lower B) s).mpr ⟨hs,heq.symm⟩
      have hstrict : s.1 < g.1 := by
        have hle := hright s hsedge
        have hne : s.1 ≠ g.1 := by
          intro he
          apply hsg
          exact Prod.ext he (heq.symm.trans hgbot.symm)
        omega
      rw [heq.symm.trans hgbot.symm]
      simp only [sub_self, mul_zero, zero_sub]
      omega
    · have hb := (hbound s hs).2
      have hmul : 0 ≤ M*(s.2-g.2-1) :=
        mul_nonneg hM.le (by omega)
      nlinarith
  have hreal : (0 : ℝ) < (M:ℝ)*((s.2:ℝ)-(g.2:ℝ))-
      ((s.1:ℝ)-(g.1:ℝ)) := by exact_mod_cast hdelta
  dsimp [v,score]
  linarith

variable {A : Type*} [Fintype A]

theorem generated_of_uniqueMinimum
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    (v : Plane) (g : G) (hg : UniqueMinimum B v g) :
    Generated θ B g :=
  hB.generated_vertex g hg.1
    (latticeConvex_erase_uniqueMinimum B hB.latticeConvex v g hg)

theorem bottom_vertices_generated (θ : G → A) (B : Finset G)
    (hB : GeneratingWindow θ B) :
    ∃ l r : G, l ∈ bottomEdge B ∧ r ∈ bottomEdge B ∧
      (∀ s ∈ bottomEdge B, l.1 ≤ s.1 ∧ s.1 ≤ r.1) ∧
      Generated θ B l ∧ Generated θ B r := by
  obtain ⟨l,hl,hleft⟩ :=
    Finset.exists_min_image (bottomEdge B) Prod.fst
      (bottomEdge_nonempty hB.nonempty)
  obtain ⟨r,hr,hright⟩ :=
    Finset.exists_max_image (bottomEdge B) Prod.fst
      (bottomEdge_nonempty hB.nonempty)
  obtain ⟨vl,hvl⟩ := bottom_left_uniqueMinimum B hB.nonempty l hl hleft
  obtain ⟨vr,hvr⟩ := bottom_right_uniqueMinimum B hB.nonempty r hr hright
  exact ⟨l,r,hl,hr,fun s hs => ⟨hleft s hs,hright s hs⟩,
    generated_of_uniqueMinimum θ B hB vl l hvl,
    generated_of_uniqueMinimum θ B hB vr r hvr⟩

theorem bottom_interval_generated (θ : G → A) (B : Finset G)
    (hB : GeneratingWindow θ B) :
    ∃ l r : ℤ, l ≤ r ∧
      bottomEdge B = (Finset.Icc l r).image (fun x => (x,lower B)) ∧
      Generated θ B (l,lower B) ∧ Generated θ B (r,lower B) := by
  obtain ⟨l,r,hlr,heq⟩ := row_eq_interval hB.latticeConvex
    (lower B) (bottomEdge_nonempty hB.nonempty)
  change bottomEdge B = (Finset.Icc l r).image (fun x => (x,lower B)) at heq
  have hleftmem : (l,lower B) ∈ bottomEdge B := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨l,Finset.mem_Icc.mpr ⟨le_refl _,hlr⟩,rfl⟩
  have hrightmem : (r,lower B) ∈ bottomEdge B := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_Icc.mpr ⟨hlr,le_refl _⟩,rfl⟩
  have hleft : ∀ s ∈ bottomEdge B, l ≤ s.1 := by
    intro s hs
    rw [heq] at hs
    obtain ⟨x,hx,hxs⟩ := Finset.mem_image.mp hs
    have he : s.1=x := congrArg Prod.fst hxs.symm
    rw [he]
    exact (Finset.mem_Icc.mp hx).1
  have hright : ∀ s ∈ bottomEdge B, s.1 ≤ r := by
    intro s hs
    rw [heq] at hs
    obtain ⟨x,hx,hxs⟩ := Finset.mem_image.mp hs
    have he : s.1=x := congrArg Prod.fst hxs.symm
    rw [he]
    exact (Finset.mem_Icc.mp hx).2
  obtain ⟨vl,hvl⟩ := bottom_left_uniqueMinimum B hB.nonempty
    (l,lower B) hleftmem hleft
  obtain ⟨vr,hvr⟩ := bottom_right_uniqueMinimum B hB.nonempty
    (r,lower B) hrightmem hright
  exact ⟨l,r,hlr,heq,
    generated_of_uniqueMinimum θ B hB vl _ hvl,
    generated_of_uniqueMinimum θ B hB vr _ hvr⟩

end

end NivatTrial.ColleVertexGeometry
