import ConvexNivat.SectorDefinitions
import ConvexNivat.SpectralFourier
import ConvexNivat.ExceptionalPolynomialDefinitions

open scoped BigOperators
namespace ConvexNivat
noncomputable section

/-- The actual b_a, defined from any realised sector used in its statements. -/
def appliedSectorBackground {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (ε : SectorSigns star) (a : ZMod p) : ScalarField :=
  applyLaurent (exceptionalPolynomial star periods)
    (colorIndicator (sectorBackground star ε) a)

/-- The actual encoded background b_η is A applied to encoded Θ_ε.
This equals the source's sum over colours without requiring an extra finite-alphabet instance. -/
def encodedSectorBackground {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (ε : SectorSigns star)
    (w : ZMod p → ℤ) : ScalarField :=
  applyLaurent (exceptionalPolynomial star periods)
    (fun z => (w (sectorBackground star ε z) : ℂ))


end
end ConvexNivat
