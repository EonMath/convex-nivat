import NivatTrial.ColleGeneratingTransforms

/-! Generating windows and directional support faces are invariant under
integer changes of basis. This lets the horizontal generated-edge
propagation argument be applied to any primitive lattice direction. -/

namespace NivatTrial.ColleDirectionalPropagation

open NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.ColleGenerating NivatTrial.ColleAmbiguity
open NivatTrial.GeneratingWindows NivatTrial.LatticeCoordinates
open NivatTrial.ColleBoundaryPropagation NivatTrial.BalancedWindows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def dualNormal (e : G ≃+ G) (v : Plane) : Plane :=
  (score v (e (0,1)), -score v (e (1,0)))

theorem score_mapWindow (e : G ≃+ G) (v : Plane) (z : G) :
    score v (e z) = score (dualNormal e v) z := by
  have hz : z = z.1 • (1,0) + z.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [hz, map_add, map_zsmul, map_zsmul,
    score_add, score_zsmul, score_zsmul]
  simp [dualNormal, score]
  ring

theorem supportEdge_mapWindow (e : G ≃+ G) (B : Finset G) (v : Plane) :
    supportEdge (mapWindow e B) v =
      mapWindow e (supportEdge B (dualNormal e v)) := by
  ext z
  simp only [supportEdge, Finset.mem_filter, mem_mapWindow]
  constructor
  · rintro ⟨hz,hmin⟩
    refine ⟨hz,?_⟩
    intro s hs
    have hh := hmin (e s) (by simpa using hs)
    calc
      score (dualNormal e v) (e.symm z) = score v z := by
        rw [← score_mapWindow e v (e.symm z)]
        simp
      _ ≤ score v (e s) := hh
      _ = score (dualNormal e v) s := score_mapWindow e v s
  · rintro ⟨hz,hmin⟩
    refine ⟨hz,?_⟩
    intro s hs
    have hh := hmin (e.symm s) (by simpa using hs)
    calc
      score v z = score (dualNormal e v) (e.symm z) := by
        rw [← score_mapWindow e v (e.symm z)]
        simp
      _ ≤ score (dualNormal e v) (e.symm s) := hh
      _ = score v s := by
        rw [← score_mapWindow e v (e.symm s)]
        simp

theorem supportBase_mapWindow (e : G ≃+ G) (B : Finset G) (v : Plane) :
    supportBase (mapWindow e B) v =
      mapWindow e (supportBase B (dualNormal e v)) := by
  ext z
  simp only [supportBase, Finset.mem_sdiff, supportEdge_mapWindow, mem_mapWindow]

theorem mapWindow_erase (e : G ≃+ G) (B : Finset G) (g : G) :
    mapWindow e (B.erase g) = (mapWindow e B).erase (e g) := by
  ext z
  simp only [mem_mapWindow, Finset.mem_erase]
  constructor
  · rintro ⟨hne,hmem⟩
    exact ⟨fun he => hne (by simpa using congrArg e.symm he),hmem⟩
  · rintro ⟨hne,hmem⟩
    exact ⟨fun he => hne (by simpa using congrArg e he),hmem⟩

theorem mapWindow_symm_mapWindow (e : G ≃+ G) (B : Finset G) :
    mapWindow e.symm (mapWindow e B) = B := by
  ext z
  simp

variable {A : Type*} [Fintype A]

theorem complexity_mapWindow (e : G ≃+ G) (θ : G → A) (B : Finset G) :
    patternComplexity (θ ∘ e.symm) (mapWindow e B) =
      patternComplexity θ B := by
  rw [patternComplexity_mapWindow]
  have he : (θ ∘ e.symm) ∘ e = θ := by funext z; simp
  rw [he]

theorem generated_mapWindow (e : G ≃+ G)
    {θ : G → A} {B : Finset G} {g : G}
    (h : Generated θ B g) :
    Generated (θ ∘ e.symm) (mapWindow e B) (e g) := by
  refine ⟨by simpa using h.1,?_⟩
  rw [← mapWindow_erase]
  simpa only [complexity_mapWindow] using h.2

theorem generatingWindow_mapWindow (e : G ≃+ G)
    {θ : G → A} {B : Finset G}
    (h : GeneratingWindow θ B) :
    GeneratingWindow (θ ∘ e.symm) (mapWindow e B) := by
  refine ⟨mapWindow_nonempty e h.nonempty,
    isLatticeConvex_mapWindow e h.latticeConvex, ?_, ?_⟩
  · intro z hz hconv
    let g := e.symm z
    have hg : g ∈ B := (mem_mapWindow e B z).mp hz
    have heq : B.erase g =
        mapWindow e.symm ((mapWindow e B).erase z) := by
      ext s
      simp only [Finset.mem_erase, mem_mapWindow]
      constructor
      · rintro ⟨hne,hmem⟩
        refine ⟨?_, by simpa using hmem⟩
        intro he
        apply hne
        simpa [g] using congrArg e.symm he
      · rintro ⟨hne,hmem⟩
        refine ⟨?_, by simpa using hmem⟩
        intro he
        apply hne
        simpa [g] using congrArg e he
    have hconvOrig : NivatTrial.LatticePolygon.IsLatticeConvex (B.erase g) := by
      rw [heq]
      exact isLatticeConvex_mapWindow e.symm hconv
    have hgGenerated := h.generated_vertex g hg hconvOrig
    have hmapped := generated_mapWindow e hgGenerated
    simpa [g] using hmapped
  · intro v
    have hb := h.strict_edge_budget (dualNormal e v)
    simpa only [complexity_mapWindow, supportBase_mapWindow,
      supportEdge_mapWindow, card_mapWindow] using hb

omit [Fintype A] in
theorem mem_languageHull_comp_equiv (e : G ≃+ G)
    {θ ξ : G → A} (hξ : ξ ∈ languageHull θ) :
    ξ ∘ e ∈ languageHull (θ ∘ e) := by
  intro S
  obtain ⟨u,hu⟩ := hξ (mapWindow e S)
  refine ⟨e.symm u, ?_⟩
  intro z hz
  have hh := hu (e z) (by simpa using hz)
  change θ (e (e.symm u + z)) = ξ (e z)
  rw [map_add, e.apply_symm_apply]
  exact hh

/-- The horizontal two-endpoint propagation rule in any unimodular lattice
coordinates. The "row" is the line with fixed second `e⁻¹` coordinate. -/
theorem generated_block_forces_whole_line
    (e : G ≃+ G) (θ : G → A) (B : Finset G)
    (hB : GeneratingWindow θ B)
    {x y : G → A} (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (d : ℤ)
    (habove : ∀ z : G, d < (e.symm z).2 → x z = y z)
    (a : G)
    (haheight : (e.symm a).2 + BalancedWindows.lower (mapWindow e.symm B) = d)
    (hblock : ∀ s ∈ BalancedWindows.bottomEdge (mapWindow e.symm B),
      x (a + e s) = y (a + e s)) :
    ∀ z : G, (e.symm z).2 = d → x z = y z := by
  let B' := mapWindow e.symm B
  let θ' := θ ∘ e
  let x' := x ∘ e
  let y' := y ∘ e
  have hB' : GeneratingWindow θ' B' := by
    simpa [θ', B'] using generatingWindow_mapWindow e.symm hB
  have hx' : x' ∈ languageHull θ' := mem_languageHull_comp_equiv e hx
  have hy' : y' ∈ languageHull θ' := mem_languageHull_comp_equiv e hy
  have habove' : ∀ w : G, d < w.2 → x' w = y' w := by
    intro w hw
    apply habove (e w)
    simpa using hw
  have hblock' : ∀ s ∈ bottomEdge B',
      x' (e.symm a + s) = y' (e.symm a + s) := by
    intro s hs
    have hh := hblock s hs
    simpa [x', y', map_add] using hh
  have hline := bottom_block_forces_whole_row θ' B' hB' hx' hy'
    d habove' (e.symm a) haheight hblock'
  intro z hz
  have hh := hline (e.symm z) hz
  simpa [x',y'] using hh

end

end NivatTrial.ColleDirectionalPropagation
