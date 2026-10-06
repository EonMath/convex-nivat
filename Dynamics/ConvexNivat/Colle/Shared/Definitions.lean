import ConvexNivat.Colle.Orbit
import ConvexNivat.Colle.GeneratingSupport
import ConvexNivat.Colle.GeneratingHalfPeriod
import ConvexNivat.CoreLattice

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

def twoRayCone (p q : Lattice) : Set RealPlane :=
  {x | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • embed p + b • embed q}

def realMinkowski (A B : Set RealPlane) : Set RealPlane :=
  {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}

def finiteRayHull (G : Finset Lattice) (p q : Lattice) : Set RealPlane :=
  realMinkowski (windowHull G) (twoRayCone p q)

def regionVertexHull {v w : Lattice} (P : Region v w) : Set RealPlane :=
  convexHull ℝ (Set.range (fun j => embed (P.vertex j)))

def regionSupportIntersection {v w : Lattice} (P : Region v w) : Set RealPlane :=
  {x | 0 ≤ realDet (embed v) (x - embed P.firstAnchor) ∧
    0 ≤ realDet (embed w) (x - embed P.secondAnchor) ∧
    ∀ j, 0 ≤ realDet (embed (P.boundedDirection j))
      (x - embed (P.vertex j.castSucc))}

def regionAnchorCell {v w : Lattice} (P : Region v w) : Set RealPlane :=
  {x | ∃ y ∈ regionVertexHull P, ∃ a b : ℝ,
    0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ x = y - a • embed v + b • embed w}

/-- Cyclic data describe the actual extreme points and complete real frontier. -/
structure WindowBoundary (B : Finset Lattice) where
  count : ℕ
  at_least_three : 3 ≤ count
  vertex : ℤ → Lattice
  direction : ℤ → Lattice
  length : ℤ → ℕ
  vertex_periodic : ∀ j, vertex (j + (count : ℤ)) = vertex j
  direction_periodic : ∀ j, direction (j + (count : ℤ)) = direction j
  length_periodic : ∀ j, length (j + (count : ℤ)) = length j
  distinct_vertices : Function.Injective (fun j : Fin count => vertex (j.val : ℤ))
  distinct_directions : Function.Injective (fun j : Fin count => direction (j.val : ℤ))
  extreme_points : (windowHull B).extremePoints ℝ =
    Set.range (fun j : Fin count => embed (vertex (j.val : ℤ)))
  vertex_mem : ∀ j, vertex j ∈ B
  primitive : ∀ j, Primitive (direction j)
  length_positive : ∀ j, 0 < length j
  edge_eq : ∀ j, vertex (j + 1) - vertex j = (length j : ℤ) • direction j
  turns : ∀ j, 0 < det (direction j) (direction (j + 1))
  support_segment : ∀ j, ∀ z : Lattice,
    z ∈ supportRow B (direction j) ↔
      embed z ∈ segment ℝ (embed (vertex j)) (embed (vertex (j + 1)))
  supports : ∀ j, ∀ x ∈ windowHull B,
    0 ≤ realDet (embed (direction j)) (x - embed (vertex j))
  hull_eq : windowHull B = {x | ∀ j,
    0 ≤ realDet (embed (direction j)) (x - embed (vertex j))}
  frontier_eq : frontier (windowHull B) = {x | ∃ j : Fin count,
    x ∈ segment ℝ (embed (vertex (j.val : ℤ))) (embed (vertex (j.val + 1 : ℤ)))}
  covers : edgeDirections B = Set.range (fun j : Fin count => direction (j.val : ℤ))

structure AlignedBoundary {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (B : Finset Lattice) where
  vertex : ℤ → Lattice
  length : ℤ → ℕ
  vertex_periodic : ∀ j, vertex (j + 2 * (m : ℤ)) = vertex j
  length_periodic : ∀ j, length (j + 2 * (m : ℤ)) = length j
  initial : ∀ j, vertex j ∈ supportRow B (C.direction j)
  terminal : ∀ j, vertex (j + 1) ∈ supportRow B (C.direction j)
  length_positive : ∀ j, 0 < length j
  edge_eq : ∀ j, vertex (j + 1) - vertex j = (length j : ℤ) • C.direction j
  segment_eq : ∀ j, ∀ z : Lattice, z ∈ supportRow B (C.direction j) ↔
    embed z ∈ segment ℝ (embed (vertex j)) (embed (vertex (j + 1)))
  hull_eq : windowHull B = {x | ∀ j,
    0 ≤ realDet (embed (C.direction j)) (x - embed (vertex j))}
  frontier_eq : frontier (windowHull B) = {x | ∃ j : Fin (2 * m),
    x ∈ segment ℝ (embed (vertex (j.val : ℤ))) (embed (vertex (j.val + 1 : ℤ)))}
  edge_eq_source : edgeDirections B = edgeDirections S
  source_length_le : ∀ j, (supportRow S (C.direction j)).card ≤ length j + 1

def integerSquare (R : ℕ) : Finset Lattice :=
  (Finset.Icc (-(R : ℤ)) (R : ℤ)).product (Finset.Icc (-(R : ℤ)) (R : ℤ))

def setTranslate (U : Set Lattice) (a : Lattice) : Set Lattice :=
  {z | ∃ q ∈ U, z = q + a}

def sweepDomain (U : Set Lattice) (steps : List (Lattice × Lattice)) : Set Lattice :=
  steps.foldl (fun V step => V ∪ {step.1 + step.2}) U

/-- Each placement is checked against the previously known sites. -/
inductive ValidGeneratingSweep (S : Finset Lattice) : Set Lattice →
    List (Lattice × Lattice) → Prop
  | nil (U) : ValidGeneratingSweep S U []
  | cons (U) (u z) (steps) (hvertex : WindowVertex S z)
      (hearlier : ∀ q ∈ S.erase z, u + q ∈ U)
      (hrest : ValidGeneratingSweep S (U ∪ {u + z}) steps) :
      ValidGeneratingSweep S U ((u, z) :: steps)

def HasFiniteSweep (S : Finset Lattice) (U : Set Lattice) (F : Finset Lattice) : Prop :=
  ∃ steps, ValidGeneratingSweep S U steps ∧ (F : Set Lattice) ⊆ sweepDomain U steps

def regionalSeed {v w : Lattice} (P : Region v w) (n R t : ℕ) : Set Lattice :=
  P.enlargement n ∪ (P.enlargement (n + 1) ∩
    (windowTranslate (integerSquare R) ((t : ℤ) • w) : Set Lattice))

def maximalAgreementWindow (S B A : Finset Lattice) (v : Lattice)
    (x y : Configuration ℤ) : Prop :=
  EnvelopedWindow S A ∧ B ⊆ A ∧ (A : Set Lattice) ⊆ halfStrip B v ∧
    AgreesOn x y (A : Set Lattice) ∧
    ∀ T : Finset Lattice, EnvelopedWindow S T → A ⊆ T →
      (T : Set Lattice) ⊆ halfStrip B v → AgreesOn x y (T : Set Lattice) → T = A

end
end ConvexNivat.Colle
