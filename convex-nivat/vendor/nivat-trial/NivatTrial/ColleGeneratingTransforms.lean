import NivatTrial.ColleActualHalfStrip
import NivatTrial.BalancedTransforms

/-! Reflection transports the entire actual generating-window structure,
including actual pattern complexities and directional exposed faces. -/

namespace NivatTrial.ColleGeneratingTransforms

open NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.GeneratingWindows NivatTrial.ColleGenerating
open NivatTrial.ColleAmbiguity NivatTrial.BalancedWindows
open NivatTrial.LatticeCoordinates
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def mirrorNormal (v : Plane) : Plane := (-v.1,v.2)

@[simp] theorem mirrorNormal_mirrorNormal (v : Plane) :
    mirrorNormal (mirrorNormal v) = v := by
  cases v
  simp [mirrorNormal]

theorem score_reflectY (v : Plane) (z : G) :
    score v (reflectY z) = score (mirrorNormal v) z := by
  simp [score,mirrorNormal]

theorem mapWindow_reflectY_erase (B : Finset G) (g : G) :
    mapWindow reflectY (B.erase g) =
      (mapWindow reflectY B).erase (reflectY g) := by
  ext z
  simp only [mem_mapWindow, Finset.mem_erase]
  constructor
  · rintro ⟨hne,hmem⟩
    exact ⟨fun he => hne (by simpa using congrArg reflectY.symm he),hmem⟩
  · rintro ⟨hne,hmem⟩
    exact ⟨fun he => hne (by simpa using congrArg reflectY he),hmem⟩

theorem supportEdge_reflectY (B : Finset G) (v : Plane) :
    supportEdge (mapWindow reflectY B) v =
      mapWindow reflectY (supportEdge B (mirrorNormal v)) := by
  ext z
  simp only [supportEdge, Finset.mem_filter, mem_mapWindow]
  constructor
  · rintro ⟨hz,hmin⟩
    refine ⟨hz,?_⟩
    intro s hs
    have hh := hmin (reflectY s) (by simpa using hs)
    simpa [score, mirrorNormal] using hh
  · rintro ⟨hz,hmin⟩
    refine ⟨hz,?_⟩
    intro s hs
    have hh := hmin (reflectY s) (by simpa using hs)
    simpa [score, mirrorNormal] using hh

theorem supportBase_reflectY (B : Finset G) (v : Plane) :
    supportBase (mapWindow reflectY B) v =
      mapWindow reflectY (supportBase B (mirrorNormal v)) := by
  ext z
  simp only [supportBase, Finset.mem_sdiff, supportEdge_reflectY, mem_mapWindow]

variable {A : Type*} [Fintype A]

theorem Generated.reflectY {θ : G → A} {B : Finset G} {g : G}
    (h : Generated θ B g) :
    Generated (θ ∘ reflectY) (mapWindow reflectY B) (reflectY g) := by
  refine ⟨by simpa using h.1,?_⟩
  rw [← mapWindow_reflectY_erase]
  simpa only [complexity_reflectY] using h.2

theorem GeneratingWindow.reflectY {θ : G → A} {B : Finset G}
    (h : GeneratingWindow θ B) :
    GeneratingWindow (θ ∘ LatticeCoordinates.reflectY)
      (mapWindow LatticeCoordinates.reflectY B) := by
  refine ⟨mapWindow_nonempty LatticeCoordinates.reflectY h.nonempty,
    isLatticeConvex_mapWindow LatticeCoordinates.reflectY h.latticeConvex,?_,?_⟩
  · intro g hg hconvErase
    let z := LatticeCoordinates.reflectY g
    have hz : z ∈ B := by
      have hmem := (mem_mapWindow LatticeCoordinates.reflectY B g).mp hg
      simpa [z] using hmem
    have heq : B.erase z =
        mapWindow LatticeCoordinates.reflectY
          ((mapWindow LatticeCoordinates.reflectY B).erase g) := by
      ext t
      simp only [Finset.mem_erase,mem_mapWindow]
      constructor
      · rintro ⟨hne,hmem⟩
        refine ⟨?_,?_⟩
        · intro ht
          apply hne
          simpa [z] using congrArg LatticeCoordinates.reflectY ht
        · simpa using hmem
      · rintro ⟨hne,hmem⟩
        refine ⟨?_,?_⟩
        · intro ht
          apply hne
          simpa [z] using congrArg LatticeCoordinates.reflectY ht
        · simpa using hmem
    have hconvOrig : NivatTrial.LatticePolygon.IsLatticeConvex (B.erase z) := by
      rw [heq]
      exact isLatticeConvex_mapWindow LatticeCoordinates.reflectY hconvErase
    have hgenerated := h.generated_vertex z hz hconvOrig
    have hreflected := Generated.reflectY hgenerated
    simpa [z] using hreflected
  · intro v
    have hb := h.strict_edge_budget (mirrorNormal v)
    simpa only [complexity_reflectY, supportBase_reflectY,
      supportEdge_reflectY, mirrorNormal_mirrorNormal, card_mapWindow] using hb

theorem bottomEdge_reflectY {B : Finset G} (hB : B.Nonempty) :
    bottomEdge (mapWindow LatticeCoordinates.reflectY B) =
      mapWindow LatticeCoordinates.reflectY (topEdge B) := by
  rw [bottomEdge, lower_reflectY hB, row_reflectY, neg_neg]
  rfl

theorem upperBase_reflectY {B : Finset G} (hB : B.Nonempty) :
    upperBase (mapWindow LatticeCoordinates.reflectY B) =
      mapWindow LatticeCoordinates.reflectY (base B) := by
  ext z
  simp only [upperBase, base, Finset.mem_sdiff,
    bottomEdge_reflectY hB, mem_mapWindow]

theorem PlusBalanced.reflectY_minus {θ : G → A} {B : Finset G}
    (h : PlusBalanced θ B) :
    MinusBalanced (θ ∘ LatticeCoordinates.reflectY)
      (mapWindow LatticeCoordinates.reflectY B) := by
  refine ⟨mapWindow_nonempty LatticeCoordinates.reflectY h.nonempty,
    isLatticeConvex_mapWindow LatticeCoordinates.reflectY h.latticeConvex,
    ?_, ?_, ?_⟩
  · simpa only [complexity_reflectY, card_mapWindow] using h.low
  · simpa only [complexity_reflectY, upperBase_reflectY h.nonempty,
      bottomEdge_reflectY h.nonempty, card_mapWindow] using h.edge_budget
  · intro t htlo hthi
    rw [lower_reflectY h.nonempty] at htlo
    rw [upper_reflectY h.nonempty] at hthi
    simpa only [bottomEdge_reflectY h.nonempty, row_reflectY, card_mapWindow]
      using h.row_card (-t) (by omega) (by omega)

theorem mem_languageHull_reflectY {θ ξ : G → A}
    (hξ : ξ ∈ languageHull θ) :
    (ξ ∘ LatticeCoordinates.reflectY) ∈
      languageHull (θ ∘ LatticeCoordinates.reflectY) := by
  intro S
  obtain ⟨u, hu⟩ := hξ (mapWindow LatticeCoordinates.reflectY S)
  refine ⟨LatticeCoordinates.reflectY u, ?_⟩
  intro z hz
  have h := hu (LatticeCoordinates.reflectY z) (by simpa using hz)
  change θ (LatticeCoordinates.reflectY
    (LatticeCoordinates.reflectY u + z)) = ξ (LatticeCoordinates.reflectY z)
  have he : LatticeCoordinates.reflectY (LatticeCoordinates.reflectY u + z) =
      u + LatticeCoordinates.reflectY z := by
    simp [map_add]
  rw [he]
  exact h

theorem oneSidedNonexpansive_reflectY {θ : G → A} {v : Plane}
    (h : OneSidedNonexpansive θ v) :
    OneSidedNonexpansive (θ ∘ LatticeCoordinates.reflectY)
      (mirrorNormal v) := by
  obtain ⟨x, hx, y, hy, hxy, hagree⟩ := h
  refine ⟨x ∘ LatticeCoordinates.reflectY, mem_languageHull_reflectY hx,
    y ∘ LatticeCoordinates.reflectY, mem_languageHull_reflectY hy, ?_, ?_⟩
  · intro he
    apply hxy
    funext z
    have hh := congrFun he (LatticeCoordinates.reflectY z)
    simpa [Function.comp_def] using hh
  · intro z hz
    apply hagree (LatticeCoordinates.reflectY z)
    change (0 : ℝ) ≤ score v (LatticeCoordinates.reflectY z)
    rw [score_reflectY]
    exact hz

theorem oneSidedNonexpansive_reflectY_horizontal {θ : G → A}
    (h : OneSidedNonexpansive θ (-1,0)) :
    OneSidedNonexpansive (θ ∘ LatticeCoordinates.reflectY) (1,0) := by
  simpa [mirrorNormal] using (oneSidedNonexpansive_reflectY h)

end

end NivatTrial.ColleGeneratingTransforms
