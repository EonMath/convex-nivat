import ConvexNivat.ExceptionalActionHelpers
import ConvexNivat.ExceptionalPolynomialAlgebra

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

theorem exceptional_direction_annihilates {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) (a : ZMod p) :
    applyLaurent (exceptionalDirectionPolynomial star periods i)
      (exceptionalDifference star i σ side a) = 0 := by
  classical
  unfold exceptionalDirectionPolynomial
  apply exceptional_product_annihilates _ _ (periods.positive i) _
    (exceptional_difference_period star periods i σ side a)
  intro ζ hζ hocc
  exact Finset.mem_filter.mpr ⟨hζ, σ, side, a, hocc⟩

theorem exceptional_spectrum_card_pos {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    0 < (exceptionalSpectrum star periods i).card := by
  exact Finset.card_pos.mpr (exceptional_spectrum_nonempty star periods i)

def spectralZonotope {p : ℕ} (star : StarData p) (periods : StarCommonPeriods star) :
    IntegralZonotope star.m where
  direction := fun i => (star.component i).direction
  degree := fun i => (exceptionalSpectrum star periods i).card
  degree_pos := exceptional_spectrum_card_pos star periods

end
end ConvexNivat
