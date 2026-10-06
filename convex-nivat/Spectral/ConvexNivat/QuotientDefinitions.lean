import ConvexNivat.Geometry.Definitions
import ConvexNivat.Operators

open scoped BigOperators Pointwise

namespace ConvexNivat

noncomputable section

/-- The algebraic data actually used in Lemma 5.2, separated from its star
producer. Distinct nonzero roots suffice; the root-of-unity condition is unused
by this quotient argument. No quotient-spanning conclusion is a field. -/
structure FiniteSpectralFamily (m : ℕ) where
  direction : Fin m → Lattice
  primitive : ∀ i, Primitive (direction i)
  pairwise_nonparallel : ∀ i j, i ≠ j → Nonparallel (direction i) (direction j)
  spectrum : Fin m → Finset ℂ
  spectrum_nonempty : ∀ i, (spectrum i).Nonempty
  spectrum_nonzero : ∀ i ζ, ζ ∈ spectrum i → ζ ≠ 0

def FiniteSpectralFamily.directionPolynomial {m : ℕ} (family : FiniteSpectralFamily m)
    (i : Fin m) : LaurentPolynomial :=
  ∏ ζ ∈ family.spectrum i,
    (translationMonomial (family.direction i) - AddMonoidAlgebra.single 0 ζ)

def FiniteSpectralFamily.polynomial {m : ℕ} (family : FiniteSpectralFamily m) :
    LaurentPolynomial := ∏ i : Fin m, family.directionPolynomial i

/-- The actual zonotope from the degrees of the actual direction factors. -/
def FiniteSpectralFamily.zonotope {m : ℕ} (family : FiniteSpectralFamily m) :
    IntegralZonotope m where
  direction := family.direction
  degree := fun i => (family.spectrum i).card
  degree_pos := fun i => Finset.card_pos.mpr (family.spectrum_nonempty i)

/-- a_i=A_i(Y^{v_i}) in the genuine K-Laurent ring. -/
def FiniteSpectralFamily.secondPointFactor {m : ℕ} (family : FiniteSpectralFamily m)
    (i : Fin m) : WitnessLaurentAlgebra :=
  differenceRecursionPolynomial (family.directionPolynomial i)

/-- c_j=A_j(X^{v_j}Y^{-v_j}) in the genuine K-Laurent ring. -/
def FiniteSpectralFamily.firstPointFactor {m : ℕ} (family : FiniteSpectralFamily m)
    (j : Fin m) : WitnessLaurentAlgebra :=
  firstPointRecursionPolynomial (family.directionPolynomial j)

/-- The CRT pair-factor ideal (a_i,c_j), not the whole bi-recursion ideal. -/
def FiniteSpectralFamily.pairIdeal {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) : Ideal WitnessLaurentAlgebra :=
  Ideal.span {family.secondPointFactor i, family.firstPointFactor j}

abbrev FiniteSpectralFamily.PairQuotient {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) := WitnessLaurentAlgebra ⧸ family.pairIdeal i j

/-- The closed parallelogram P_ij in source (5.4). -/
def spectralPairParallelogram {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) : Set RealPlane :=
  {x | ∃ α β : ℝ, 0 ≤ α ∧ α ≤ ((family.spectrum i).card : ℝ) ∧
    0 ≤ β ∧ β ≤ ((family.spectrum j).card : ℝ) ∧
    x = α • embed (family.direction i) - β • embed (family.direction j)}

/-- E_ij in source Step 3: it projects onto only the pair factor (i,j). -/
def spectralPairSelector {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) : WitnessLaurentAlgebra :=
  (∏ k ∈ Finset.univ.erase i, family.secondPointFactor k) *
    (∏ l ∈ Finset.univ.erase j, family.firstPointFactor l)


end
end ConvexNivat
