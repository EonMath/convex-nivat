import ConvexNivat.Colle.Shared.Definitions
import ConvexNivat.Colle.Shared.AlgebraDefinitions
import ConvexNivat.Operators
import ConvexNivat.Geometry.Definitions

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

def primitiveSegment (a v : Lattice) (N : ℕ) : Finset Lattice :=
  (Finset.range (N + 1)).image (fun j : ℕ => a + (j : ℤ) • v)

def integerCoefficientCast : AddMonoidAlgebra ℤ Lattice →+* LaurentPolynomial :=
  AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℂ)

def reflectIntegerLaurent (φ : IntegerLaurent) : IntegerLaurent :=
  φ.mapDomain (fun z => -z)

def reflectedFactorHull (m : ℕ) (h : Fin m → Lattice) : Set RealPlane :=
  {x | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
    x = ∑ i, t i • embed (-h i)}

structure LabelledFactorOrder (m : ℕ) (h : Fin m → Lattice) where
  label : Fin m ≃ Fin m
  direction : Fin m → Lattice
  scale : Fin m → ℕ
  sign : Fin m → ℤ
  primitive : ∀ i, Primitive (direction i)
  scale_positive : ∀ i, 0 < scale i
  sign_unit : ∀ i, sign i = 1 ∨ sign i = -1
  factor_eq : ∀ i, h (label i) = (sign i * (scale i : ℤ)) • direction i
  ordered_turn : ∀ i j, i < j → 0 < det (direction i) (direction j)

def labelledCycleDirection {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) : Lattice :=
  if hm : 0 < m then
    let r := (j % (2 * (m : ℤ))).toNat
    if r < m then O.direction ⟨r % m, Nat.mod_lt _ hm⟩
    else -O.direction ⟨r % m, Nat.mod_lt _ hm⟩
  else 0

def labelledHullAnchor {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) : Lattice :=
  ∑ i, if O.sign i = 1 then -h (O.label i) else 0

def labelledCycleVertex {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) : Lattice :=
  let r := (j % (2 * (m : ℤ))).toNat
  labelledHullAnchor O +
    if r ≤ m then ∑ i : Fin m, if i.val < r then (O.scale i : ℤ) • O.direction i else 0
    else ∑ i : Fin m, if r - m ≤ i.val then (O.scale i : ℤ) • O.direction i else 0

def ambiguousRestrictions (ξ : Configuration ℤ) (S : Finset Lattice)
    (n : RealPlane) : Set (Pattern ℤ (offFace S n)) :=
  {γ | γ ∈ patternSet ξ (offFace S n) ∧ 1 < extensionCount ξ S n γ}

def ambiguousFullPatterns (ξ : Configuration ℤ) (S : Finset Lattice)
    (n : RealPlane) : Set (Pattern ℤ S) :=
  {δ | δ ∈ patternSet ξ S ∧ ∃ γ ∈ ambiguousRestrictions ξ S n,
    δ ∈ extensionSet ξ S n γ}

def integerWord {A : Type*} (g : ℤ → A) (n : ℕ) (t : ℤ) : Fin n → A :=
  fun j => g (t + (j.val : ℤ))

def latticeRowWord (ξ : Configuration ℤ) (v : Lattice) (N : ℕ)
    (z : Lattice) : Fin N → ℤ := fun j => ξ (z + (j.val : ℤ) • v)

def occurringRowStates (ξ : Configuration ℤ) (v : Lattice) (N : ℕ) :
    Set (Fin N → ℤ) := Set.range (latticeRowWord ξ v N)

def borderRowSamples (S : Finset Lattice) (v : Lattice) (a : ℤ → Lattice) :
    Finset Lattice :=
  S.image (fun z => a (det v z)) \ supportRow S v

def vectorRowWord (x : Configuration ℤ) (v : Lattice) (U : Finset Lattice)
    (t : ℤ) : {a : Lattice // a ∈ U} → ℤ := fun a => x (a.val + t • v)

def downwardBorder (v : Lattice) (μ M : ℤ) (j : ℕ) : Set Lattice :=
  latticeStrip v (μ + 1 - (j : ℤ)) (M - (j : ℤ))

end
end ConvexNivat.Colle
