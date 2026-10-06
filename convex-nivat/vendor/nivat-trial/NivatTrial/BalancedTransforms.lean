import NivatTrial.BalancedWindows
import NivatTrial.LatticeCoordinates

/-! Translation and reversal of the actual balanced windows. -/

namespace NivatTrial.BalancedWindows

open NivatTrial.Zonotope NivatTrial.LatticePolygon NivatTrial.Dynamics
open NivatTrial.LatticeCoordinates
open scoped Classical

noncomputable section

theorem lower_eq_of_bounds {B : Finset Lattice} {t : ℤ} (hB : B.Nonempty)
    (hle : ∀ z ∈ B, t ≤ z.2) (he : ∃ z ∈ B, z.2 = t) : lower B = t := by
  obtain ⟨z, hz, hzt⟩ := he
  apply le_antisymm
  · simpa [hzt] using lower_le_of_mem hz
  · obtain ⟨w, hw⟩ := bottomEdge_nonempty hB
    obtain ⟨hwB, hwlo⟩ := (mem_row B (lower B) w).mp hw
    simpa [hwlo] using hle w hwB

theorem upper_eq_of_bounds {B : Finset Lattice} {t : ℤ} (hB : B.Nonempty)
    (hle : ∀ z ∈ B, z.2 ≤ t) (he : ∃ z ∈ B, z.2 = t) : upper B = t := by
  obtain ⟨z, hz, hzt⟩ := he
  apply le_antisymm
  · obtain ⟨w, hw⟩ := topEdge_nonempty hB
    obtain ⟨hwB, hwup⟩ := (mem_row B (upper B) w).mp hw
    simpa [hwup] using hle w hwB
  · simpa [hzt] using le_upper_of_mem hz

theorem lower_translateWindow (u : Lattice) {B : Finset Lattice} (hB : B.Nonempty) :
    lower (translateWindow u B) = u.2 + lower B := by
  apply lower_eq_of_bounds hB.map
  · intro z hz
    have h := lower_le_of_mem ((mem_translateWindow u B z).mp hz)
    simp only [Prod.snd_sub] at h
    omega
  · obtain ⟨z, hz⟩ := bottomEdge_nonempty hB
    obtain ⟨hzB, he⟩ := (mem_row B (lower B) z).mp hz
    refine ⟨u+z, by simpa using hzB, ?_⟩
    simp [he]

theorem upper_translateWindow (u : Lattice) {B : Finset Lattice} (hB : B.Nonempty) :
    upper (translateWindow u B) = u.2 + upper B := by
  apply upper_eq_of_bounds hB.map
  · intro z hz
    have h := le_upper_of_mem ((mem_translateWindow u B z).mp hz)
    simp only [Prod.snd_sub] at h
    omega
  · obtain ⟨z, hz⟩ := topEdge_nonempty hB
    obtain ⟨hzB, he⟩ := (mem_row B (upper B) z).mp hz
    refine ⟨u+z, by simpa using hzB, ?_⟩
    simp [he]

theorem row_translateWindow (u : Lattice) (B : Finset Lattice) (t : ℤ) :
    row (translateWindow u B) t = translateWindow u (row B (t-u.2)) := by
  ext z
  simp only [mem_row, mem_translateWindow, Prod.snd_sub]
  constructor <;> rintro ⟨h, he⟩ <;> exact ⟨h, by omega⟩

theorem topEdge_translateWindow (u : Lattice) {B : Finset Lattice} (hB : B.Nonempty) :
    topEdge (translateWindow u B) = translateWindow u (topEdge B) := by
  rw [topEdge, upper_translateWindow u hB, row_translateWindow]
  simp [topEdge]

theorem base_translateWindow (u : Lattice) {B : Finset Lattice} (hB : B.Nonempty) :
    base (translateWindow u B) = translateWindow u (base B) := by
  ext z
  simp only [base, Finset.mem_sdiff, topEdge_translateWindow u hB, mem_translateWindow]

theorem PlusBalanced.translate {A : Type*} [Fintype A] {θ : Lattice → A}
    {B : Finset Lattice} (h : PlusBalanced θ B) (u : Lattice) :
    PlusBalanced θ (translateWindow u B) := by
  refine ⟨h.nonempty.map, isLatticeConvex_translateWindow u h.latticeConvex, ?_, ?_, ?_⟩
  · simpa only [patternComplexity_translateWindow, card_translateWindow] using h.low
  · simpa only [patternComplexity_translateWindow, base_translateWindow u h.nonempty,
      topEdge_translateWindow u h.nonempty, card_translateWindow] using h.edge_budget
  · intro t htlo hthi
    rw [lower_translateWindow u h.nonempty] at htlo
    rw [upper_translateWindow u h.nonempty] at hthi
    simpa only [topEdge_translateWindow u h.nonempty, card_translateWindow,
      row_translateWindow] using h.row_card (t-u.2) (by omega) (by omega)

theorem lower_reflectY {B : Finset Lattice} (hB : B.Nonempty) :
    lower (mapWindow reflectY B) = -upper B := by
  apply lower_eq_of_bounds (mapWindow_nonempty reflectY hB)
  · intro z hz
    have h := le_upper_of_mem ((mem_mapWindow reflectY B z).mp hz)
    simp only [reflectY_symm_apply] at h
    omega
  · obtain ⟨z, hz⟩ := topEdge_nonempty hB
    obtain ⟨hzB, he⟩ := (mem_row B (upper B) z).mp hz
    refine ⟨reflectY z, by simpa using hzB, ?_⟩
    simp [he]

theorem upper_reflectY {B : Finset Lattice} (hB : B.Nonempty) :
    upper (mapWindow reflectY B) = -lower B := by
  apply upper_eq_of_bounds (mapWindow_nonempty reflectY hB)
  · intro z hz
    have h := lower_le_of_mem ((mem_mapWindow reflectY B z).mp hz)
    simp only [reflectY_symm_apply] at h
    omega
  · obtain ⟨z, hz⟩ := bottomEdge_nonempty hB
    obtain ⟨hzB, he⟩ := (mem_row B (lower B) z).mp hz
    refine ⟨reflectY z, by simpa using hzB, ?_⟩
    simp [he]

theorem row_reflectY (B : Finset Lattice) (t : ℤ) :
    row (mapWindow reflectY B) t = mapWindow reflectY (row B (-t)) := by
  ext z
  simp only [mem_row, mem_mapWindow, reflectY_symm_apply]
  constructor <;> rintro ⟨h, he⟩ <;> exact ⟨h, by omega⟩

theorem topEdge_reflectY {B : Finset Lattice} (hB : B.Nonempty) :
    topEdge (mapWindow reflectY B) = mapWindow reflectY (bottomEdge B) := by
  rw [topEdge, upper_reflectY hB, row_reflectY, neg_neg]
  rfl

theorem base_reflectY {B : Finset Lattice} (hB : B.Nonempty) :
    base (mapWindow reflectY B) = mapWindow reflectY (upperBase B) := by
  ext z
  simp only [base, upperBase, Finset.mem_sdiff, topEdge_reflectY hB, mem_mapWindow]

theorem complexity_reflectY {A : Type*} [Fintype A] (θ : Lattice → A) (B : Finset Lattice) :
    patternComplexity (θ ∘ reflectY) (mapWindow reflectY B) = patternComplexity θ B := by
  rw [patternComplexity_mapWindow]
  have he : (θ ∘ reflectY) ∘ reflectY = θ := by funext z; simp
  rw [he]

theorem MinusBalanced.reflect {A : Type*} [Fintype A] {θ : Lattice → A}
    {B : Finset Lattice} (h : MinusBalanced θ B) :
    PlusBalanced (θ ∘ reflectY) (mapWindow reflectY B) := by
  refine ⟨mapWindow_nonempty reflectY h.nonempty,
    isLatticeConvex_mapWindow reflectY h.latticeConvex, ?_, ?_, ?_⟩
  · simpa only [complexity_reflectY, card_mapWindow] using h.low
  · simpa only [complexity_reflectY, base_reflectY h.nonempty,
      topEdge_reflectY h.nonempty, card_mapWindow] using h.edge_budget
  · intro t htlo hthi
    rw [lower_reflectY h.nonempty] at htlo
    rw [upper_reflectY h.nonempty] at hthi
    simpa only [topEdge_reflectY h.nonempty, row_reflectY, card_mapWindow]
      using h.row_card (-t) (by omega) (by omega)

end
end NivatTrial.BalancedWindows
