import ConvexNivat.Core
import ConvexNivat.Operators

/-!
Definition-only binding of the standalone Laurent operators to the actual star data.
The compatible-period hypotheses are precisely the preservation conditions used
in §§0.3–5; no downstream theorem is stored as a structure field.
-/

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

/-- The actual common tail-period set `Γ` of §0.3. -/
def commonTailPeriods {p : ℕ} (d : StarData p) : Set Lattice :=
  {h | ∀ j : Fin d.m,
    HasPeriod (d.component j).leftTail h ∧ HasPeriod (d.component j).rightTail h}

/-- An admissible choice of positive tangential periods preserving all tails.
Remark 1.4 explicitly permits any such choice. Minimality is not required by
any operator statement and is not asserted here. -/
structure StarPeriodData {p : ℕ} (d : StarData p) where
  multiplier : Fin d.m → ℕ
  multiplier_pos : ∀ i, 0 < multiplier i
  component_period : ∀ i,
    HasPeriod (d.component i).field ((multiplier i : ℤ) • (d.component i).direction)
  all_tail_periods : ∀ i,
    (multiplier i : ℤ) • (d.component i).direction ∈ commonTailPeriods d

/-- The actual vector `H_i = κ_i v_i`. -/
def StarPeriodData.vector {p : ℕ} {d : StarData p}
    (P : StarPeriodData d) (i : Fin d.m) : Lattice :=
  (P.multiplier i : ℤ) • (d.component i).direction

/-- The source difference operator `D = ∏_i (T^(H_i)-1)`. -/
def starDifference {p : ℕ} {d : StarData p} (P : StarPeriodData d) : LaurentPolynomial :=
  differenceProduct Finset.univ P.vector

/-- The source component-isolating operator `Q_i`. -/
def starOtherDifference {p : ℕ} {d : StarData p}
    (P : StarPeriodData d) (i : Fin d.m) : LaurentPolynomial :=
  otherDifferenceProduct Finset.univ P.vector i

/-- A completely arbitrary scalar function of the pattern on a finite window. -/
def starLocalFunction {p : ℕ} (d : StarData p) (W : Finset Lattice)
    (φ : Pattern (ZMod p) W → ℂ) : ScalarField :=
  fun z => φ (pattern d.configuration W z)

/-- The actual finite sampling set `M = E + W` in Lemma 1.1. -/
def localSamplingSet {p : ℕ} {d : StarData p}
    (P : StarPeriodData d) (W : Finset Lattice) : Finset Lattice :=
  formalExponentSet Finset.univ P.vector + W

/-- A natural bound on every absolute determinant height in the sampling set.
It is zero for the empty sampling set; this harmless convention handles `W=∅`. -/
def localSamplingRadius {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (W : Finset Lattice) (i : Fin d.m) : ℕ :=
  (localSamplingSet P W).sup (fun z => (height (d.component i).direction z).natAbs)

/-- The widened strip `Σ_i` in Lemma 1.1. -/
def localWidenedStrip {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (W : Finset Lattice) (i : Fin d.m) : Set Lattice :=
  {z | (d.component i).lower - (localSamplingRadius d P W i : ℤ) ≤
      height (d.component i).direction z ∧
    height (d.component i).direction z ≤
      (d.component i).upper + (localSamplingRadius d P W i : ℤ)}

/-- The integer-valued scalar encoding used in §§2–5, viewed in characteristic zero. -/
def integerScalarEncoding {p : ℕ} (d : StarData p) (w : ZMod p → ℤ) : ScalarField :=
  scalarEncoding d.configuration (fun a => (w a : ℂ))

/-- Source `f_i = Q_i η`, for the actual component index and scalar encoding. -/
def isolatedScalarField {p : ℕ} {d : StarData p}
    (P : StarPeriodData d) (η : ScalarField) (i : Fin d.m) : ScalarField :=
  applyLaurent (starOtherDifference P i) η

end

end ConvexNivat
