import NivatTrial.ColleBoundaryPropagation
import NivatTrial.ColleBalancedRows

/-! A genuinely one-sided nonexpansive direction, a minimal generating
window, and its balanced edge budget produce an actual hull point whose
entire adjacent half-strip has one common eventual period. -/

namespace NivatTrial.ColleActualHalfStrip

open NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.BalancedWindows NivatTrial.ColleGenerating
open NivatTrial.ColleBoundaryPropagation NivatTrial.ColleBalancedRows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

variable {A : Type*} [Fintype A]

theorem exists_periodic_halfStrip_of_horizontal_ONED
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B) (hbalanced : MinusBalanced θ B)
    (honed : OneSidedNonexpansive θ (1,0)) :
    ∃ ξ ∈ languageHull θ, ∃ N Q : ℕ, 0 < Q ∧
      ∀ t : ℤ, lower B < t → t ≤ upper B →
        ∃ w : G, w.2 = t ∧
          ∀ i : ℤ, (N : ℤ) ≤ i →
            ξ (w+(i+Q) • ((1,0):G)) = ξ (w+i • ((1,0):G)) := by
  obtain ⟨ξ,hξ,hamb⟩ :=
    exists_fully_ambiguous_of_horizontal_ONED θ B hgen honed
  obtain ⟨N,Q,hQ,hperiod⟩ :=
    balanced_semi_ambiguous_halfStrip_period θ B hbalanced hξ 0 hamb
  refine ⟨ξ,hξ,N,Q,hQ,?_⟩
  intro t htl htu
  obtain ⟨w,hw,hp⟩ := hperiod t htl htu
  exact ⟨w,hw,fun i hi => hp i (by simpa using hi)⟩

end

end NivatTrial.ColleActualHalfStrip
