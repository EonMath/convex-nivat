import Mathlib.Analysis.Convex.Hull
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Shared definitions for the source paper, §§0.1–0.3, 8.1, and Appendix D.1.
This module contains definitions and source-hypothesis bundles only.
-/

namespace ConvexNivat

open scoped BigOperators

/-- The integer lattice of the source. -/
abbrev Lattice := ℤ × ℤ

/-- The ambient real plane used for convex hulls and half-plane geometry. -/
abbrev RealPlane := ℝ × ℝ

/-- Coordinatewise inclusion of the integer lattice into the real plane. -/
def embed (z : Lattice) : RealPlane := ((z.1 : ℝ), (z.2 : ℝ))

/-- Oriented determinant in lattice coordinates. -/
def det (u v : Lattice) : ℤ := u.1 * v.2 - u.2 * v.1

/-- Primitive means coprime integer coordinates (§0.1). -/
def Primitive (v : Lattice) : Prop := Nat.Coprime v.1.natAbs v.2.natAbs

/-- Nonparallel lattice vectors, equivalently independent in the real plane. -/
def Nonparallel (u v : Lattice) : Prop := det u v ≠ 0

/-- The determinant height in direction `u`. -/
def height (u z : Lattice) : ℤ := det u z

abbrev Configuration (A : Type*) := Lattice → A

/-- Translation convention from §0.3: `T^u f(z) = f(z+u)`. -/
def translate {A : Type*} (u : Lattice) (f : Configuration A) : Configuration A :=
  fun z => f (z + u)

/-- A period is allowed to be zero; `Periodic` requires a nonzero period. -/
def HasPeriod {A : Type*} (f : Configuration A) (h : Lattice) : Prop :=
  ∀ z, f (z + h) = f z

/-- The actual period set. Its subgroup laws are separate proof obligations. -/
def periodSet {A : Type*} (f : Configuration A) : Set Lattice :=
  {h | HasPeriod f h}

/-- Periodicity in at least one lattice direction. -/
def Periodic {A : Type*} (f : Configuration A) : Prop :=
  ∃ h : Lattice, h ≠ 0 ∧ HasPeriod f h

/-- Doubly periodic in the source sense: two real-linearly independent periods. -/
def DoublyPeriodic {A : Type*} (f : Configuration A) : Prop :=
  ∃ h k : Lattice, Nonparallel h k ∧ HasPeriod f h ∧ HasPeriod f k

/-- Equality of configurations on a specified lattice region. -/
def AgreesOn {A : Type*} (f g : Configuration A) (U : Set Lattice) : Prop :=
  ∀ z ∈ U, f z = g z

/-- Real convex hull of a finite lattice window. -/
def windowHull (S : Finset Lattice) : Set RealPlane :=
  convexHull ℝ (embed '' (S : Set Lattice))

/-- `S = Conv(S) ∩ ℤ²`, including windows of lower affine dimension (§0.2). -/
def LatticeConvex (S : Finset Lattice) : Prop :=
  ∀ z : Lattice, embed z ∈ windowHull S ↔ z ∈ S

/-- Patterns are functions on the points of the actual finite window. -/
abbrev Pattern (A : Type*) (S : Finset Lattice) := {z : Lattice // z ∈ S} → A

/-- The translated window is reindexed onto `S`, as in §0.2 and Appendix D.1. -/
def pattern {A : Type*} (f : Configuration A) (S : Finset Lattice)
    (u : Lattice) : Pattern A S :=
  fun z => f (u + z.val)

/-- Actual set of patterns appearing in translated copies of `S`. -/
def patternSet {A : Type*} (f : Configuration A) (S : Finset Lattice) :
    Set (Pattern A S) :=
  Set.range (pattern f S)

/-- Number of actual occurring patterns. All uses in source theorems have finite alphabet.
`Set.ncard` uses zero on an infinite set; finite-alphabet finiteness is a separate lemma. -/
noncomputable def complexity {A : Type*} (f : Configuration A)
    (S : Finset Lattice) : ℕ :=
  (patternSet f S).ncard

/-- Finite-window characterization of product-topology orbit closure for a discrete alphabet.
Every finite restriction of `g` agrees with a translate of `f`; no conclusion is built in. -/
def OrbitClosure {A : Type*} (f : Configuration A) : Set (Configuration A) :=
  {g | ∀ S : Finset Lattice, ∃ u : Lattice, ∀ z ∈ S, g z = f (u + z)}

/-- The rectangle of Corollary 8.19: `[1,n] × [1,k]`, with inclusive integer intervals. -/
def rectangle (n k : ℕ) : Finset Lattice :=
  (Finset.Icc (1 : ℤ) (n : ℤ)).product (Finset.Icc (1 : ℤ) (k : ℤ))

/-- All data and exactly the defining source conditions (S1)–(S3) for one component. -/
structure StarComponent (p : ℕ) where
  direction : Lattice
  primitive : Primitive direction
  field : Configuration (ZMod p)
  tangential_period : ∃ k : ℤ, 1 ≤ k ∧ HasPeriod field (k • direction)
  not_doubly_periodic : ¬ DoublyPeriodic field
  leftTail : Configuration (ZMod p)
  rightTail : Configuration (ZMod p)
  left_doubly_periodic : DoublyPeriodic leftTail
  right_doubly_periodic : DoublyPeriodic rightTail
  lower : ℤ
  upper : ℤ
  bounds : lower ≤ upper + 1
  left_agreement : AgreesOn field leftTail {z | height direction z < lower}
  right_agreement : AgreesOn field rightTail {z | upper < height direction z}

/-- A prime-alphabet star family of arbitrary finite length at least two (§0.1). -/
structure StarData (p : ℕ) where
  prime : p.Prime
  m : ℕ
  two_le : 2 ≤ m
  component : Fin m → StarComponent p
  pairwise_nonparallel : ∀ i j : Fin m, i ≠ j →
    Nonparallel (component i).direction (component j).direction

/-- The source's actual sum in `𝔽_p`; only this summation is in characteristic `p`. -/
def StarData.configuration {p : ℕ} (d : StarData p) : Configuration (ZMod p) :=
  fun z => ∑ i : Fin d.m, (d.component i).field z

/-- A configuration is a star precisely when it is such a finite component sum. -/
def IsStarConfiguration {p : ℕ} (θ : Configuration (ZMod p)) : Prop :=
  ∃ d : StarData p, θ = d.configuration

end ConvexNivat
