import NivatTrial.SpectralGeometry
import NivatTrial.StarRecurrence
import NivatTrial.AffineBudget

/-! Final window dimension accounting.  All inputs apart from confinement of
the displacement have been obtained from the original star data. -/

namespace NivatTrial.StarWindow

open NivatTrial.Algebra NivatTrial.Differences NivatTrial.Quadratic
open NivatTrial.GlobalSpectrum NivatTrial.SpectralGeometry NivatTrial.StarRecurrence
open NivatTrial.LatticePolygon
open scoped Classical Pointwise

noncomputable section

theorem twoPoint_shift (η : G → ℂ) (q₀ q₁ z : G) :
    twoPoint η q₀ q₁ z = twoPoint η 0 (q₁ - q₀) (z + q₀) := by
  simp only [twoPoint, add_zero]
  congr 1
  congr 1
  abel

theorem shifted_witness (D : Laurent) (η : G → ℂ) (q₀ q₁ z : G) :
    act D (twoPoint η q₀ q₁) z =
      BiRecursion.witness D η (q₁ - q₀) (z + q₀) := by
  rw [show twoPoint η q₀ q₁ = (fun x => twoPoint η 0 (q₁ - q₀) (x + q₀)) from
    funext (twoPoint_shift η q₀ q₁)]
  exact act_translate D _ q₀ z

theorem shifted_witness_nonzero (D : Laurent) (η : G → ℂ) (q₀ q₁ : G)
    (h : BiRecursion.witness D η (q₁ - q₀) ≠ 0) :
    act D (twoPoint η q₀ q₁) ≠ 0 := by
  intro hz
  apply h
  funext z
  have hzero := congrFun hz (z - q₀)
  simpa only [shifted_witness, sub_add_cancel, Pi.zero_apply] using hzero

variable {ι α : Type*} [Fintype ι] [Nontrivial ι] [AddCommGroup α] [Fintype α]
    (T : Star.Data ι α)

theorem affine_bound (S : Finset G) (hS : IsLatticeConvex S) :
    S.card + 1 ≤ Module.finrank ℂ (affineSpace T.total S (scalarEncoding T)) +
      (placementFinset (generators T) S hS).card :=
  AffineBudget.affine_dimension_budget T.total S (placementFinset (generators T) S hS)
    (scalarEncoding T) (polynomial T) (bounded_factorization T S hS)

/-- Once the displacement lies in the difference zonotope, there are no further
geometric, affine, or linear-independence hypotheses to discharge. -/
theorem complexity_of_confined_witness (S : Finset G) (hS : IsLatticeConvex S)
    (hD : act T.normalized.operator (encodedField T) = 0)
    (d : G) (hd : Zonotope.embed d ∈
      Zonotope.zonotope (generators T) - Zonotope.zonotope (generators T))
    (hnonzero : BiRecursion.witness T.normalized.operator (encodedField T) d ≠ 0) :
    S.card + 1 ≤ patternComplexity T.total S := by
  obtain ⟨q₀, q₁, hdq, h₀, h₁⟩ := witness_placements (generators T) S hS d hd
  apply AffineBudget.complexity_of_bounded_factorization_and_witness
    T.total S (placementFinset (generators T) S hS) (scalarEncoding T)
    (polynomial T) T.normalized.operator q₀ q₁ (bounded_factorization T S hS)
    h₀ h₁ T.normalized.operator_const hD
    (Witness.finite_support_twoPoint_difference T.normalized (scalarEncoding T) q₀ q₁)
  apply shifted_witness_nonzero
  rwa [← hdq]

end

end NivatTrial.StarWindow
