import ConvexNivat.Core
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Actual geometric definitions used in §§2.2,2.6,6,7 of the source.
There are no theorem proofs or theorem certificates in this module.
-/

namespace ConvexNivat

open scoped BigOperators Pointwise

/-- The integer lattice points of a real-plane set. -/
def latticePoints (P : Set RealPlane) : Set Lattice := embed ⁻¹' P

/-- A real set translated by an embedded lattice vector. -/
def latticeTranslate (r : Lattice) (P : Set RealPlane) : Set RealPlane :=
  (fun x => embed r + x) '' P

/-- `R_Z(S)` of §2.6: the translate of the entire real set fits in the real hull. -/
def erosion (P : Set RealPlane) (S : Finset Lattice) : Set Lattice :=
  {r | ∀ x ∈ P, embed r + x ∈ windowHull S}

/-- Integer endpoints and positive degrees for the Minkowski sum in (2.2).
Two-dimensionality is imposed separately where the source requires it. -/
structure IntegralZonotope (m : ℕ) where
  direction : Fin m → Lattice
  degree : Fin m → ℕ
  degree_pos : ∀ i, 0 < degree i

namespace IntegralZonotope

/-- The integer endpoint `dᵢvᵢ` of the `i`th generating segment. -/
def endpoint {m : ℕ} (Z : IntegralZonotope m) (i : Fin m) : Lattice :=
  Z.degree i • Z.direction i

/-- `Z = ∑ᵢ [0,dᵢvᵢ]` in the actual real plane, written using segment parameters. -/
def carrier {m : ℕ} (Z : IntegralZonotope m) : Set RealPlane :=
  {x | ∃ t : Fin m → ℝ,
    (∀ i, 0 ≤ t i ∧ t i ≤ (Z.degree i : ℝ)) ∧
    x = ∑ i : Fin m, t i • embed (Z.direction i)}

/-- All subset sums of the integer generating endpoints. -/
def subsetSums {m : ℕ} (Z : IntegralZonotope m) : Finset Lattice :=
  (Finset.univ : Finset (Fin m)).powerset.image
    (fun I => ∑ i ∈ I, Z.endpoint i)

/-- Twice the center: the lattice vector `c₀ = ∑ᵢ dᵢvᵢ`. -/
def centerSum {m : ℕ} (Z : IntegralZonotope m) : Lattice :=
  ∑ i : Fin m, Z.endpoint i

/-- The first direction, with the source's hypothesis `m ≥ 2`. -/
def firstDirection {m : ℕ} (Z : IntegralZonotope m) (h : 2 ≤ m) : Lattice :=
  Z.direction ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) h⟩

/-- The second direction, with the source's hypothesis `m ≥ 2`. -/
def secondDirection {m : ℕ} (Z : IntegralZonotope m) (h : 2 ≤ m) : Lattice :=
  Z.direction ⟨1, Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) h⟩

end IntegralZonotope

/-- A triangle whose three specified vertices are integer lattice points.
Degenerate triangles are allowed as data; unimodularity excludes them. -/
structure LatticeTriangle where
  a : Lattice
  b : Lattice
  c : Lattice
  deriving DecidableEq

namespace LatticeTriangle

def vertices (T : LatticeTriangle) : Finset Lattice := {T.a, T.b, T.c}

/-- The closed real triangle, including its boundary. -/
def carrier (T : LatticeTriangle) : Set RealPlane := windowHull T.vertices

/-- Determinant magnitude one, equivalently area `1/2` and a lattice basis. -/
def Unimodular (T : LatticeTriangle) : Prop :=
  (det (T.b - T.a) (T.c - T.a)).natAbs = 1

end LatticeTriangle

/-- A nonempty finite lattice generating set; the polygon is its real convex hull.
Full dimension is an explicit hypothesis on triangulation existence. -/
structure LatticePolygon where
  vertices : Finset Lattice
  vertices_nonempty : vertices.Nonempty

def LatticePolygon.carrier (P : LatticePolygon) : Set RealPlane :=
  windowHull P.vertices

/-- A genuine finite unimodular triangulation of a real-plane set.
Common-face intersection is imposed in addition to containment and coverage;
no integer decomposition conclusion is included in this definition. -/
structure UnimodularTriangulation (P : Set RealPlane) where
  triangles : Finset LatticeTriangle
  unimodular : ∀ T ∈ triangles, T.Unimodular
  contained : ∀ T ∈ triangles, T.carrier ⊆ P
  covers : ∀ x ∈ P, ∃ T ∈ triangles, x ∈ T.carrier
  common_face : ∀ T ∈ triangles, ∀ U ∈ triangles,
    T.carrier ∩ U.carrier = windowHull (T.vertices ∩ U.vertices)

end ConvexNivat
