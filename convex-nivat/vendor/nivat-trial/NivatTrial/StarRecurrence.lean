import NivatTrial.GlobalSpectrum
import NivatTrial.SectorBackground

/-! Both recurrences of §5.1 for the polynomial and scalar encoding constructed
from the original star hypotheses. -/

namespace NivatTrial.StarRecurrence

open NivatTrial.Algebra NivatTrial.Periodicity NivatTrial.BiRecursion
open NivatTrial.GlobalSpectrum NivatTrial.SectorBackground
open scoped Classical

noncomputable section

variable {ι α : Type*} [Fintype ι] [AddCommGroup α] [Fintype α] (T : Star.Data ι α)

def scalarEncoding (a : α) : ℂ := (encoding T a : ℂ)

def encodedField (z : G) : ℂ := scalarEncoding T (T.total z)

theorem scalarEncoding_injective : Function.Injective (scalarEncoding T) :=
  Int.cast_injective.comp (encoding_injective T)

theorem killsIsolatedDefects : KillsIsolatedDefects T (polynomial T) (scalarEncoding T) := by
  intro i
  exact ⟨polynomial_annihilates_rightDefect T i true (encoding T),
    polynomial_annihilates_rightDefect T i false (encoding T)⟩

theorem background_periods (hD : act T.normalized.operator (encodedField T) = 0) :
    ∀ i, IsPeriod (act (polynomial T) (encodedField T)) (T.normalized.period i) :=
  polynomial_background_periods T (polynomial T) (scalarEncoding T) hD (killsIsolatedDefects T)

theorem background_doublyPeriodic [Nontrivial ι]
    (hD : act T.normalized.operator (encodedField T) = 0) :
    IsDoublyPeriodic (act (polynomial T) (encodedField T)) :=
  polynomial_background_doublyPeriodic T (polynomial T) (scalarEncoding T) hD
    (killsIsolatedDefects T)

theorem actual_bi_recursion (hD : act T.normalized.operator (encodedField T) = 0) :
    (∀ d z, displacementAction (polynomial T)
      (witness T.normalized.operator (encodedField T)) d z = 0) ∧
    (∀ d z, diagonalAction (polynomial T)
      (witness T.normalized.operator (encodedField T)) d z = 0) :=
  bi_recursion Finset.univ T.normalized.period (polynomial T) (encodedField T)
    (act (polynomial T) (encodedField T)) rfl hD (fun i _ => background_periods T hD i)

theorem witness_finite [Nonempty ι] (d : G) :
    (Function.support (witness T.normalized.operator (encodedField T) d)).Finite :=
  Witness.finite_support_twoPoint_difference T.normalized (scalarEncoding T) 0 d

theorem second_case_witness [Nontrivial ι]
    (hcase : ∀ a : α, act T.normalized.operator (Dichotomy.indicator T.total a) = 0) :
    ∃ d : G, d ≠ 0 ∧ witness T.normalized.operator (encodedField T) d ≠ 0 := by
  obtain ⟨d, hd, _, hnonzero⟩ := Dichotomy.second_case_witness T.normalized
    (scalarEncoding T) (scalarEncoding_injective T) T.component_ne_rightTail
    T.normalized_transverse hcase
  exact ⟨d, hd, hnonzero⟩

end

end NivatTrial.StarRecurrence
