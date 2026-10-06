import ConvexNivat.Colle.Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Span

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

def deletedReplacement (m : ℕ) (h : Fin m → Lattice) (k : Fin m)
    (a : Lattice) : IntegerLaurent :=
  ((AddMonoidAlgebra.single a (1 : ℤ) - AddMonoidAlgebra.single (0 : Lattice) (1 : ℤ)) *
    AddMonoidAlgebra.ofCoeff (differenceWithout m h k)).coeff

def realSegmentSum (h : Finset Lattice) : Set RealPlane :=
  {x | ∃ a : Lattice → ℝ, (∀ u ∈ h, 0 ≤ a u ∧ a u ≤ 1) ∧
    x = ∑ u ∈ h, a u • embed (-u)}

/-- RC22: component lookup and cancellation-aware convex support geometry. -/
abbrev ComplexLaurent := AddMonoidAlgebra ℂ Lattice

def complexAction (φ : ComplexLaurent) (f : Configuration ℂ) (z : Lattice) : ℂ :=
  φ.coeff.sum (fun u c => c * f (z - u))

def complexAnnihilatorIdeal (f : Configuration ℂ) : Ideal ComplexLaurent :=
  Ideal.span {φ | ∀ z, complexAction φ f z = 0}

def integerFieldComplex (ξ : Configuration ℤ) : Configuration ℂ := fun z => (ξ z : ℂ)

def integerPolynomialComplex (ψ : IntegerLaurent) : ComplexLaurent :=
  AddMonoidAlgebra.ofCoeff (ψ.mapRange (fun a : ℤ => (a : ℂ)) (Int.cast_zero))

def complexSupportWindow (φ : ComplexLaurent) : Finset Lattice :=
  convexLatticeWindow (φ.coeff.support.image Neg.neg)

/-- A line polynomial has at least two support points on one affine integer line. -/
def LinePolynomial (φ : ComplexLaurent) (v : Lattice) : Prop :=
  Primitive v ∧ 2 ≤ φ.coeff.support.card ∧
    ∃ u : Lattice, ∀ z ∈ φ.coeff.support, ∃ a : ℤ, z = u + a • v

end
end ConvexNivat.Colle
