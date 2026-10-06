import ConvexNivat.Colle.Shared.RowCoordinates
import ConvexNivat.CorePeriods

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

theorem double_common_component_period (v h₀ : Lattice) (hv : Primitive v)
    (hh₀ : h₀ ≠ 0) (htangent : det v h₀ = 0)
    (f xper : Configuration ℤ) (hf : HasPeriod f h₀) (hx : DoublyPeriodic xper) :
    ∃ a : ℤ, a ≠ 0 ∧ HasPeriod f (a • v) ∧ HasPeriod xper (a • v) := by
  have hrow := (primitive_row_coordinates v hv).2.1
  have hdet : det v (0 : Lattice) = det v h₀ := by simpa [det] using htangent.symm
  obtain ⟨k, hk⟩ := (hrow 0 h₀).mp hdet
  simp only [zero_add] at hk
  have hkne : k ≠ 0 := by
    intro hz
    simp [hz] at hk
    exact hh₀ hk
  obtain ⟨n, hn, hnx⟩ := doublyPeriodic_multiple_period xper hx h₀
  refine ⟨n*k, mul_ne_zero (by omega) hkne, ?_, ?_⟩
  · simpa only [hk, smul_smul] using hasPeriod_zsmul f h₀ hf n
  · simpa only [hk, smul_smul] using hnx


theorem double_period_avoiding_finite_directions (F : Configuration ℤ)
    (hF : DoublyPeriodic F) (H : Finset Lattice) (hne : ∀ h ∈ H, h ≠ 0) :
    ∃ h : Lattice, h ≠ 0 ∧ HasPeriod F h ∧ ∀ q ∈ H, det h q ≠ 0 := by
  classical
  let t : ℤ := (∑ q ∈ H, q.2.natAbs) + 1
  let r : Lattice := (1,t)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hr : r ≠ 0 := by
    intro hz
    have := congrArg Prod.fst hz
    norm_num [r] at this
  have havoid : ∀ q ∈ H, det r q ≠ 0 := by
    intro q hq hd
    have hsum : q.2.natAbs ≤ ∑ q ∈ H, q.2.natAbs := by
      apply Finset.single_le_sum (fun x hx => Nat.zero_le (x.2.natAbs)) hq
    have hb : |q.2| < t := by
      have : (q.2.natAbs : ℤ) ≤ (∑ q ∈ H, q.2.natAbs : ℕ) := by exact_mod_cast hsum
      rw [Int.natCast_natAbs] at this
      dsimp [t]
      omega
    have heq : q.2 = t*q.1 := by
      change 1*q.2-t*q.1=0 at hd
      linarith
    have hq1 : q.1 ≠ 0 := by
      intro hz
      have hq2 : q.2=0 := by simp [hz] at heq; exact heq
      exact hne q hq (Prod.ext hz hq2)
    have habs : 1 ≤ |q.1| := by
      rcases lt_or_gt_of_ne hq1 with hlt | hgt
      · rw [abs_of_neg hlt]
        omega
      · rw [abs_of_pos hgt]
        omega
    rw [heq,abs_mul,abs_of_pos ht] at hb
    nlinarith
  obtain ⟨N,hN,hper⟩ := (doublyPeriodic_iff_grid F).mp hF
  have hNz : (N:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  refine ⟨(N:ℤ) • r, ?_, hper r, ?_⟩
  · intro hz
    have hz1 := congrArg Prod.fst hz
    simp [r] at hz1
    exact hNz (by exact_mod_cast hz1)
  · intro q hq
    have hd : det ((N:ℤ) • r) q = (N:ℤ)*det r q := by
      simp [det]
      ring
    rw [hd]
    exact mul_ne_zero hNz (havoid q hq)



end
end ConvexNivat.Colle
