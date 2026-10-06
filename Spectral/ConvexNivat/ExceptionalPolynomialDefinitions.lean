import ConvexNivat.SpectralLaurentBridge
import ConvexNivat.Geometry.Definitions
import ConvexNivat.StarSpectral
import ConvexNivat.Operators

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

def exceptionalDirectionPolynomial {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) : LaurentPolynomial :=
  ∏ ζ ∈ exceptionalSpectrum star periods i,
    (translationMonomial (star.component i).direction - AddMonoidAlgebra.single 0 ζ)

def exceptionalPolynomial {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) : LaurentPolynomial :=
  ∏ i : Fin star.m, exceptionalDirectionPolynomial star periods i

def starDifferencePolynomial {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) : LaurentPolynomial :=
  differenceProduct Finset.univ periods.vector

def InCaseB {p : ℕ} (star : StarData p) (periods : StarCommonPeriods star) : Prop :=
  ∀ a : ZMod p, applyLaurent (starDifferencePolynomial star periods)
    (colorIndicator star.configuration a) = 0

def encodedStar {p : ℕ} (star : StarData p) (w : ZMod p → ℤ) : ScalarField :=
  fun z => (w (star.configuration z) : ℂ)

def newtonPolygon (f : LaurentPolynomial) : Set RealPlane := windowHull f.coeff.support

abbrev OccurringPattern {p : ℕ} (star : StarData p) (S : Finset Lattice) :=
  {γ : Pattern (ZMod p) S // γ ∈ patternSet star.configuration S}

def affineObservableSpace {p : ℕ} (star : StarData p) (w : ZMod p → ℤ)
    (S : Finset Lattice) : Submodule ℚ (OccurringPattern star S → ℚ) :=
  Submodule.span ℚ
    ({fun _ => 1} ∪ Set.range (fun s : {s : Lattice // s ∈ S} =>
      fun γ : OccurringPattern star S => (w (γ.val s) : ℚ)))

end
end ConvexNivat
