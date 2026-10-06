import NivatTrial.ColleReverseBalancedRows

/-! A real defect across a one-sided generated edge gives a single eventual
period throughout its adjacent finite-width band. The proof passes through
actual two-extension counts and finite-word complexity. -/

namespace NivatTrial.ColleSecondBoundaryPeriod

open NivatTrial.Dynamics NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating NivatTrial.ColleOneSidedAmbiguity
open NivatTrial.ColleReverseBalancedRows
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

theorem eventual_period_of_left_halfStrip_interface
    (θ : G → A) (B : Finset G)
    (hgen : GeneratingWindow θ B) (hbalanced : MinusBalanced θ B)
    {x y : G → A} (hx : x ∈ languageHull θ)
    (hy : y ∈ languageHull θ)
    (d : ℤ) (w : G) (hwrow : w.2 = d) (hbad : x w ≠ y w)
    (H L : ℤ) (hH : ∀ s ∈ B, s.1 ≤ H)
    (hL : ∀ s ∈ B, L ≤ s.1)
    (r : ℤ)
    (hr : ∃ l : ℤ, bottomEdge B =
      (Finset.Icc l r).image (fun j => (j,lower B)))
    (hagree : ∀ z : G, d < z.2 →
      z.2 ≤ d+upper B-lower B →
      z.1 ≤ w.1-r+H → x z = y z) :
    ∃ N Q : ℕ, 0 < Q ∧
      ∀ z : G, d < z.2 → z.2 ≤ d+upper B-lower B →
        z.1 ≤ L-(r-w.1+N) →
          x (z+(Q:ℤ) • ((-1,0):G))=x z := by
  have hsemi := semi_ambiguous_of_left_halfStrip θ B hgen hx hy d w
    hwrow hbad H hH r hr hagree
  obtain ⟨N,Q,hQ,hband⟩ :=
    reverse_semi_ambiguous_band_period θ B hbalanced
      (shift_mem_languageHull hx (0,d-lower B))
      (r-w.1) hsemi L hL
  refine ⟨N,Q,hQ,?_⟩
  intro z hzl hzu hzleft
  let z' : G := (z.1,z.2-(d-lower B))
  have hzlo : lower B<z'.2 := by dsimp [z']; omega
  have hzup : z'.2≤upper B := by dsimp [z']; omega
  have hzfirst : z'.1≤L-((r-w.1)+N) := by dsimp [z']; omega
  have hh := hband z' hzlo hzup hzfirst
  change x ((0,d-lower B)+(z'+(Q:ℤ) • ((-1,0):G))) =
    x ((0,d-lower B)+z') at hh
  have he : ((0,d-lower B):G)+z'=z := by
    ext <;> dsimp [z'] <;> simp <;> omega
  rw [← add_assoc,he] at hh
  exact hh

end
end NivatTrial.ColleSecondBoundaryPeriod
