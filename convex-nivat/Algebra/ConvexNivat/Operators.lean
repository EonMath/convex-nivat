import Mathlib

/-!
Actual Laurent operators for source §§0.3, 1, 4, and 5.
This module contains definitions only. Shared lattice and star definitions remain in Core.
The literal pair type used here is definitionally equal to `ConvexNivat.Lattice`.
-/

namespace ConvexNivat

open scoped BigOperators

noncomputable section

/-- Finite complex Laurent polynomials with arbitrary integer exponent pairs. -/
abbrev LaurentPolynomial := AddMonoidAlgebra ℂ (ℤ × ℤ)

/-- Characteristic-zero scalar fields; no boundedness or finiteness is implicit. -/
abbrev ScalarField := (ℤ × ℤ) → ℂ

/-- The monomial `T^u` with coefficient one. -/
def translationMonomial (u : ℤ × ℤ) : LaurentPolynomial :=
  AddMonoidAlgebra.single u 1

/-- The exact convention `p(T)f(z) = ∑_u p_u f(z+u)` from §0.3. -/
def applyLaurent (p : LaurentPolynomial) (f : ScalarField) : ScalarField :=
  fun z => p.coeff.sum (fun u c => c * f (z + u))

/-- A single finite difference `T^u - 1`. -/
def differencePolynomial (u : ℤ × ℤ) : LaurentPolynomial :=
  translationMonomial u - 1

/-- The finite product of differences, indexed by the actual component labels. -/
def differenceProduct {ι : Type*} (s : Finset ι) (H : ι → ℤ × ℤ) :
    LaurentPolynomial :=
  ∏ i ∈ s, differencePolynomial (H i)

/-- Source `Q_i`, with only component `i` removed from the index set. -/
def otherDifferenceProduct {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) (i : ι) : LaurentPolynomial :=
  differenceProduct (s.erase i) H

/-- The formal subset exponent `H_C`; different subsets may have equal sums. -/
def formalExponent {ι : Type*} (H : ι → ℤ × ℤ) (C : Finset ι) : ℤ × ℤ :=
  ∑ i ∈ C, H i

/-- The image exponent set `E`, used only for support bounds, never for signed expansion. -/
def formalExponentSet {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → ℤ × ℤ) : Finset (ℤ × ℤ) :=
  s.powerset.image (formalExponent H)

/-- The quotient in `(T^(nH)-1) = (T^H-1)(1+T^H+⋯+T^((n-1)H))`. -/
def geometricTranslationSum (u : ℤ × ℤ) (n : ℕ) : LaurentPolynomial :=
  ∑ k ∈ Finset.range n, translationMonomial (k • u)

/-- Actual finite support of a scalar field, rather than a support certificate in a structure. -/
def ScalarHasFiniteSupport (J : ScalarField) : Prop :=
  (Function.support J).Finite

/-- Convert an ordinary field with finite support into its actual finite coefficient function. -/
def fieldToFinsupp (J : ScalarField) (hJ : ScalarHasFiniteSupport J) :
    (ℤ × ℤ) →₀ ℂ :=
  Finsupp.ofSupportFinite J hJ

/-- Source Laurent transform `Ĵ(X) = ∑_z J(z) X^(-z)`; note the negative exponents. -/
def finiteLaurentTransform (J : (ℤ × ℤ) →₀ ℂ) : LaurentPolynomial :=
  AddMonoidAlgebra.ofCoeff (J.mapDomain (fun z => -z))

/-- The finite convolution constructed through the source Laurent transform. -/
def finiteConvolution (p : LaurentPolynomial) (J : (ℤ × ℤ) →₀ ℂ) :
    (ℤ × ℤ) →₀ ℂ :=
  (p * finiteLaurentTransform J).coeff.mapDomain (fun z => -z)

/-- Complex indicator values as required by §0.3, independently of the alphabet's arithmetic. -/
def scalarColourIndicator {A : Type*} [DecidableEq A]
    (θ : (ℤ × ℤ) → A) (a : A) : ScalarField :=
  fun z => if θ z = a then 1 else 0

/-- Scalar encoding by an arbitrary complex weight function. -/
def scalarEncoding {A : Type*} (θ : (ℤ × ℤ) → A) (w : A → ℂ) : ScalarField :=
  fun z => w (θ z)

/-- `J(d,z)` from Lemma 4.2 and §5.1. -/
def quadraticWitness (D : LaurentPolynomial) (η : ScalarField) :
    (ℤ × ℤ) → ScalarField :=
  fun d => applyLaurent D (fun z => η z * η (z + d))

/-- The action of `p(T_d)`: shift the difference variable, fixing the anchor. -/
def applyInDifference (p : LaurentPolynomial)
    (J : (ℤ × ℤ) → ScalarField) : (ℤ × ℤ) → ScalarField :=
  fun d z => p.coeff.sum (fun s c => c * J (d + s) z)

/-- The action of `p(T_z T_d^(-1))`: `(d,z) ↦ (d-s,z+s)`. -/
def applyAtFirstPoint (p : LaurentPolynomial)
    (J : (ℤ × ℤ) → ScalarField) : (ℤ × ℤ) → ScalarField :=
  fun d z => p.coeff.sum (fun s c => c * J (d - s) (z + s))

/-- The rational function field in the two independent Laurent indeterminates. -/
abbrev LaurentRationalField := FractionRing LaurentPolynomial

/-- The source's `R = ℂ(X_1,X_2)[Y_1^±,Y_2^±]`. -/
abbrev WitnessLaurentAlgebra := AddMonoidAlgebra LaurentRationalField (ℤ × ℤ)

/-- `A(Y)`, obtained by extending only the coefficient field. -/
def differenceRecursionPolynomial (A : LaurentPolynomial) : WitnessLaurentAlgebra :=
  AddMonoidAlgebra.ofCoeff
    (A.coeff.mapRange (algebraMap ℂ LaurentRationalField) (map_zero _))

/-- `A(X/Y) = ∑_s A_s X^s Y^(-s)` with the exact sign from §5.2. -/
def firstPointRecursionPolynomial (A : LaurentPolynomial) : WitnessLaurentAlgebra :=
  A.coeff.sum (fun s c => AddMonoidAlgebra.single (-s)
    ((algebraMap ℂ LaurentRationalField c) *
      algebraMap LaurentPolynomial LaurentRationalField (translationMonomial s)))

/-- The actual two-generator ideal `(A(Y), A(X/Y))`. -/
def biRecursionIdeal (A : LaurentPolynomial) : Ideal WitnessLaurentAlgebra :=
  Ideal.span {differenceRecursionPolynomial A, firstPointRecursionPolynomial A}

/-- The actual quotient from Lemma 5.2, with no spanning conclusion built into its type. -/
abbrev BiRecursionQuotient (A : LaurentPolynomial) :=
  WitnessLaurentAlgebra ⧸ biRecursionIdeal A

/-- The unique `K`-linear extension of the assigned monomial values.
This is bundled `K`-linearity, as required by the argument of Proposition 5.3. -/
def laurentBasisFunctional (values : (ℤ × ℤ) → LaurentRationalField) :
    WitnessLaurentAlgebra →ₗ[LaurentRationalField] LaurentRationalField :=
  (Finsupp.linearCombination LaurentRationalField values).comp
    (AddMonoidAlgebra.coeffLinearEquiv LaurentRationalField).toLinearMap

/-- The rational-function values `Ĵ(d;X)`, allowing the finite support to depend on `d`. -/
def witnessTransformValues (J : (ℤ × ℤ) → ScalarField)
    (hJ : ∀ d, ScalarHasFiniteSupport (J d)) :
    (ℤ × ℤ) → LaurentRationalField :=
  fun d => algebraMap LaurentPolynomial LaurentRationalField
    (finiteLaurentTransform (fieldToFinsupp (J d) (hJ d)))

/-- Proposition 5.3's actual `K`-linear functional `L(Y^d) = Ĵ(d;X)`. -/
def witnessTransformFunctional (J : (ℤ × ℤ) → ScalarField)
    (hJ : ∀ d, ScalarHasFiniteSupport (J d)) :
    WitnessLaurentAlgebra →ₗ[LaurentRationalField] LaurentRationalField :=
  laurentBasisFunctional (witnessTransformValues J hJ)

/-- The class of a Laurent monomial in the actual bi-recursion quotient. -/
def quotientMonomial (A : LaurentPolynomial) (d : ℤ × ℤ) : BiRecursionQuotient A :=
  Ideal.Quotient.mk (biRecursionIdeal A) (AddMonoidAlgebra.single d 1)

/-- Genuine spanning by the listed exponent set in the quotient. -/
def QuotientSpannedBy (A : LaurentPolynomial) (B : Set (ℤ × ℤ)) : Prop :=
  Submodule.span LaurentRationalField (quotientMonomial A '' B) = ⊤

end

end ConvexNivat
