import ConvexNivat.Core
import Mathlib

/-! Source definitions from §8.1–8.5 and Appendix D. These definitions contain
no theorem conclusions and no proof placeholders. -/
namespace ConvexNivat

def realDot (x y : RealPlane) : ℝ := x.1 * y.1 + x.2 * y.2
def realDet (x y : RealPlane) : ℝ := x.1 * y.2 - x.2 * y.1

/-- Both strict and weak half-planes, including irrational normals. -/
structure HalfPlane where
  normal : RealPlane
  normal_ne_zero : normal ≠ 0
  threshold : ℝ
  strict : Bool

def HalfPlane.carrier (H : HalfPlane) : Set Lattice :=
  {z | if H.strict then H.threshold < realDot (embed z) H.normal
    else H.threshold ≤ realDot (embed z) H.normal}

def ForwardInvariant (U : Set Lattice) (h : Lattice) : Prop :=
  ∀ z ∈ U, z + h ∈ U

def FullPeriods {A : Type*} (f : Configuration A) (U : Set Lattice)
    (h k : Lattice) : Prop :=
  U.Nonempty ∧ Nonparallel h k ∧ ForwardInvariant U h ∧ ForwardInvariant U k ∧
    (∀ z ∈ U, f (z + h) = f z) ∧ (∀ z ∈ U, f (z + k) = f z)

def FullyPeriodicOn {A : Type*} (f : Configuration A) (U : Set Lattice) : Prop :=
  ∃ h k, FullPeriods f U h k

/-- §8.2's actual extension construction with an explicit entrance witness. -/
noncomputable def extensionAlong {A : Type*} (G : Configuration A)
    (R : Set Lattice) (g : Lattice) (hentry : ∀ z, ∃ n : ℕ, z + (n : ℤ) • g ∈ R) :
    Configuration A := fun z => G (z + ((Classical.choose (hentry z) : ℕ) : ℤ) • g)

/-- The source uses a closed convex real set, not a finite convex window. -/
def LatticeConvexRegion (R : Set Lattice) : Prop :=
  ∃ C : Set RealPlane, IsClosed C ∧ Convex ℝ C ∧ R = embed ⁻¹' C

def closedRealHull (R : Set Lattice) : Set RealPlane :=
  closure (convexHull ℝ (embed '' R))

def recessionCone (C : Set RealPlane) : Set RealPlane :=
  {w | ∀ x ∈ C, x + w ∈ C}

def regionCone (R : Set Lattice) : Set RealPlane := recessionCone (closedRealHull R)

/-- For a convex cone in the real plane this expresses real dimension two. -/
def FullDimensional (K : Set RealPlane) : Prop := (interior K).Nonempty

/-- Exactly a closed sector with opening strictly between zero and π. -/
def ClosedSector (K : Set RealPlane) : Prop :=
  ∃ a b : RealPlane, realDet a b ≠ 0 ∧
    K = {x | ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ x = α • a + β • b}

def realLine (v : Lattice) : Set RealPlane := {x | ∃ t : ℝ, x = t • embed v}

structure LatticeBasis where
  first : Lattice
  second : Lattice
  unimodular : det first second = 1 ∨ det first second = -1

def LatticeBasis.row (B : LatticeBasis) (z : Lattice) : ℤ :=
  det B.first B.second * det B.first z

def latticeRow (v : Lattice) (t : ℤ) : Set Lattice := {z | det v z = t}
def latticeStrip (v : Lattice) (a b : ℤ) : Set Lattice := {z | a ≤ det v z ∧ det v z ≤ b}
def upperHalf (v : Lattice) (c : ℤ) : Set Lattice := {z | c ≤ det v z}
def lowerHalf (v : Lattice) (c : ℤ) : Set Lattice := {z | det v z ≤ c}
def signedUpperHalf (σ : ℤ) (v : Lattice) (c : ℤ) : Set Lattice :=
  {z | c ≤ σ * det v z}

/-- Finite-window product convergence for a discrete alphabet: eventual equality
at each lattice point. -/
def PointwiseLimit {A : Type*} (f : ℕ → Configuration A) (g : Configuration A) : Prop :=
  ∀ z, ∃ N : ℕ, ∀ n ≥ N, f n z = g z

def SubsequentialTranslateLimit {A : Type*} (f : Configuration A)
    (d : Lattice) (g : Configuration A) : Prop :=
  ∃ n : ℕ → ℕ, StrictMono n ∧
    PointwiseLimit (fun j => translate ((n j : ℤ) • d) f) g

def translateLimitSet {A : Type*} (f : Configuration A) (d : Lattice) :
    Set (Configuration A) := {g | SubsequentialTranslateLimit f d g}

def LowConvexComplexity {A : Type*} (f : Configuration A) : Prop :=
  ∃ S : Finset Lattice, S.Nonempty ∧ LatticeConvex S ∧ complexity f S ≤ S.card

/-- Integer/Fp decompositions permit unbounded component ranges over ℤ. -/
structure PeriodicDecomposition (A : Type*) [AddCommMonoid A]
    (f : Configuration A) (m : ℕ) where
  field : Fin m → Configuration A
  period : Fin m → Lattice
  period_nonzero : ∀ i, period i ≠ 0
  has_period : ∀ i, HasPeriod (field i) (period i)
  sum_eq : ∀ z, f z = ∑ i, field i z

def HasPeriodicDecomposition (A : Type*) [AddCommMonoid A]
    (f : Configuration A) (m : ℕ) : Prop := Nonempty (PeriodicDecomposition A f m)

def MinimalPeriodicOrder (A : Type*) [AddCommMonoid A]
    (f : Configuration A) (m : ℕ) : Prop :=
  HasPeriodicDecomposition A f m ∧
    ∀ n : ℕ, HasPeriodicDecomposition A f n → m ≤ n

/-- Every positive finite-alphabet low-convex-complexity counterexample is
included in the global order comparison; minimality is not omitted. -/
def MinimalOrderCounterexample (ξ : Configuration ℤ) (m : ℕ) : Prop :=
  (∃ A : Finset ℤ, (∀ a ∈ A, 0 < a) ∧ ∀ z, ξ z ∈ A) ∧
  ¬ Periodic ξ ∧ LowConvexComplexity ξ ∧ MinimalPeriodicOrder ℤ ξ m ∧
  ∀ (η : Configuration ℤ) (n : ℕ),
    (∃ A : Finset ℤ, (∀ a ∈ A, 0 < a) ∧ ∀ z, η z ∈ A) →
    ¬ Periodic η → LowConvexComplexity η → MinimalPeriodicOrder ℤ η n → m ≤ n

/-- A finite Laurent polynomial represented by its actual coefficient support. -/
abbrev IntegerLaurent := Lattice →₀ ℤ

def integerLaurentAction (a : IntegerLaurent) (f : Configuration ℤ)
    (z : Lattice) : ℤ := a.sum (fun h c => c * f (z + h))

def HasNontrivialIntegerAnnihilator (f : Configuration ℤ) : Prop :=
  ∃ a : IntegerLaurent, a ≠ 0 ∧ ∀ z, integerLaurentAction a f z = 0

/-- Product of differences, expanded with subset multiplicities retained. -/
noncomputable def mixedDifference {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (f : Configuration A) (z : Lattice) : A :=
  ∑ C ∈ I.powerset, (-1 : A) ^ (I.card - C.card) * f (z + ∑ j ∈ C, H j)

def rowMinimum (v : Lattice) (S : Finset Lattice) (hS : S.Nonempty) : ℤ :=
  S.inf' hS (det v)

def rowMaximum (v : Lattice) (S : Finset Lattice) (hS : S.Nonempty) : ℤ :=
  S.sup' hS (det v)

def rowHeight (v : Lattice) (S : Finset Lattice) (hS : S.Nonempty) : ℤ :=
  rowMaximum v S hS - rowMinimum v S hS

def extremeRow (σ : ℤ) (v : Lattice) (S : Finset Lattice)
    (hS : S.Nonempty) : Finset Lattice :=
  S.filter (fun z => det v z = if σ = 1 then rowMaximum v S hS else rowMinimum v S hS)

/-- Source D.4: convexity/nonemptiness, sign, both complexity bounds, and all
integer rows, including possibly empty intermediate rows. -/
structure BalancedSet {A : Type*} (θ : Configuration A) (v : Lattice)
    (σ : ℤ) (B : Finset Lattice) : Prop where
  nonempty : B.Nonempty
  convex : LatticeConvex B
  sign : σ = 1 ∨ σ = -1
  low_complexity : complexity θ B ≤ B.card
  strict_growth : complexity θ B < complexity θ (B \ extremeRow σ v B nonempty) +
    (extremeRow σ v B nonempty).card
  every_row : ∀ t : ℤ, rowMinimum v B nonempty ≤ t →
    t ≤ rowMaximum v B nonempty →
    (extremeRow σ v B nonempty).card - 1 ≤ (B.filter (fun z => det v z = t)).card

def AmbiguityStrip {A : Type*} (θ : Configuration A) (v : Lattice)
    (a b : ℤ) : Prop :=
  a ≤ b ∧ ∃ x ∈ OrbitClosure θ,
    AgreesOn x θ (latticeStrip v a (b - 1)) ∧
      ∃ z, det v z = b ∧ x z ≠ θ z

def PatternDetermines {A : Type*} (θ : Configuration A) (D : Finset Lattice)
    (e : Lattice) : Prop :=
  ∀ x ∈ OrbitClosure θ, ∀ y ∈ OrbitClosure θ, ∀ t : Lattice,
    (∀ z ∈ D, x (z + t) = y (z + t)) → x (e + t) = y (e + t)

/-- Colle [2, Definition 1.5]: the closed lattice half-plane on the left of
the oriented line fails to determine a point of the orbit closure. -/
def OneSidedNonexpansive (ξ : Configuration ℤ) (n : RealPlane) : Prop :=
  n ≠ 0 ∧ ∃ x ∈ OrbitClosure ξ, ∃ y ∈ OrbitClosure ξ,
    x ≠ y ∧ AgreesOn x y {z | 0 ≤ realDot (embed z) n}

/-- Unoriented nonexpansiveness of a line in the Boyle–Lind sense: every
finite-width band about that line admits two distinct agreeing fields. -/
def NonexpansiveLine (ξ : Configuration ℤ) (n : RealPlane) : Prop :=
  n ≠ 0 ∧ ∀ width : ℝ, 0 < width →
    ∃ x ∈ OrbitClosure ξ, ∃ y ∈ OrbitClosure ξ,
      x ≠ y ∧ AgreesOn x y {z | |realDot (embed z) n| ≤ width}

/-- Finite polygonal boundary with exactly two nonparallel unbounded rays.
The finite segments may include redundant subdivisions. -/
structure TwoRayPolygonalRegion (ξ : Configuration ℤ)
    (n : RealPlane) where
  carrier : Set RealPlane
  closed : IsClosed carrier
  convex : Convex ℝ carrier
  firstVertex : RealPlane
  secondVertex : RealPlane
  firstDirection : RealPlane
  secondDirection : RealPlane
  independent : realDet firstDirection secondDirection ≠ 0
  first_parallel : realDot firstDirection n = 0
  secondNormal : RealPlane
  second_parallel : realDot secondDirection secondNormal = 0
  first_nonexpansive : NonexpansiveLine ξ n
  second_nonexpansive : NonexpansiveLine ξ secondNormal
  boundedEdges : List (RealPlane × RealPlane)
  boundary_eq : frontier carrier =
    {x | ∃ t : ℝ, 0 ≤ t ∧ x = firstVertex + t • firstDirection} ∪
    {x | ∃ t : ℝ, 0 ≤ t ∧ x = secondVertex + t • secondDirection} ∪
    {x | ∃ e ∈ boundedEdges, x ∈ segment ℝ e.1 e.2}

structure AdmissibleDecomposition (p : ℕ) (θ : Configuration (ZMod p)) (m : ℕ)
    extends PeriodicDecomposition (ZMod p) θ m where
  left : Fin m → HalfPlane
  right : Fin m → HalfPlane
  disjoint : ∀ i, Disjoint (left i).carrier (right i).carrier
  full_left : ∀ i, FullyPeriodicOn (field i) (left i).carrier
  full_right : ∀ i, FullyPeriodicOn (field i) (right i).carrier

/-- First-half-plane output, retaining the full-dimensional common cone needed
by 8.15, and explicitly excluding doubly periodic components. -/
structure FirstHalfPlaneData (p : ℕ) (θ : Configuration (ZMod p)) where
  length : ℕ
  at_least_two : 2 ≤ length
  field : Fin length → Configuration (ZMod p)
  direction : Fin length → Lattice
  transverse : Fin length → Lattice
  basis : ∀ i, det (direction i) (transverse i) = 1
  primitive : ∀ i, Primitive (direction i)
  multiplier : Fin length → ℕ
  positive_multiplier : ∀ i, 0 < multiplier i
  has_period : ∀ i, HasPeriod (field i) ((multiplier i : ℤ) • direction i)
  distinct_directions : Pairwise (fun i j => Nonparallel (direction i) (direction j))
  not_double : ∀ i, ¬ DoublyPeriodic (field i)
  sum_eq : ∀ z, θ z = ∑ i, field i z
  threshold : Fin length → ℤ
  full_upper : ∀ i, FullyPeriodicOn (field i) (upperHalf (direction i) (threshold i))
  cone : Set RealPlane
  sector : ClosedSector cone
  full_dimensional : FullDimensional cone
  cone_upper : ∀ i, cone ⊆ {w | 0 ≤ realDet (embed (direction i)) w}
  avoids_directions : ∀ i, Disjoint (realLine (direction i)) (interior cone)

/-- §8.4 known upper tails plus the lower tails already constructed, with a
common lattice Nℤ² preserving every tail. O records the remaining indices. -/
structure TailInventory {p : ℕ} {θ : Configuration (ZMod p)}
    (D : FirstHalfPlaneData p θ) (O : Finset (Fin D.length)) where
  upperTail : Fin D.length → Configuration (ZMod p)
  upper_double : ∀ j, DoublyPeriodic (upperTail j)
  upper_agreement : ∀ j, AgreesOn (D.field j) (upperTail j)
    (upperHalf (D.direction j) (D.threshold j))
  lowerTail : (j : Fin D.length) → j ∉ O → Configuration (ZMod p)
  lowerThreshold : (j : Fin D.length) → j ∉ O → ℤ
  lower_double : ∀ j hj, DoublyPeriodic (lowerTail j hj)
  lower_disjoint : ∀ j hj, lowerThreshold j hj < D.threshold j
  lower_agreement : ∀ j hj, AgreesOn (D.field j) (lowerTail j hj)
    (lowerHalf (D.direction j) (lowerThreshold j hj))
  scale : ℕ
  positive_scale : 0 < scale
  divisible : ∀ j, D.multiplier j ∣ scale
  upper_periods : ∀ j z, HasPeriod (upperTail j) ((scale : ℤ) • z)
  lower_periods : ∀ j hj z, HasPeriod (lowerTail j hj) ((scale : ℤ) • z)

def SafeDirection {p : ℕ} {θ : Configuration (ZMod p)}
    (D : FirstHalfPlaneData p θ) (O : Finset (Fin D.length))
    (d : Lattice) (j : Fin D.length) : Prop :=
  0 < det (D.direction j) d ∨ (j ∉ O ∧ det (D.direction j) d < 0)

end ConvexNivat
