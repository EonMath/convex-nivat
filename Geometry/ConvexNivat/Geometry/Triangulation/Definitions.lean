import ConvexNivat.Geometry.Definitions
import ConvexNivat.ReductionDefinitions

namespace ConvexNivat.PolygonTriangulation

open scoped BigOperators Pointwise

def delta (T : LatticeTriangle) : ℤ := det (T.b - T.a) (T.c - T.a)

def vertex (T : LatticeTriangle) : Fin 3 → Lattice := ![T.a, T.b, T.c]

def HasBarycentric (T : LatticeTriangle) (x : RealPlane) (w : Fin 3 → ℝ) : Prop :=
  (∑ i, w i) = 1 ∧ x = ∑ i, w i • embed (vertex T i)

noncomputable def barycentric (T : LatticeTriangle) (x : RealPlane) : Fin 3 → ℝ :=
  let d := realDet (embed (T.b - T.a)) (embed (T.c - T.a))
  let α := realDet (x - embed T.a) (embed (T.c - T.a)) / d
  let β := realDet (embed (T.b - T.a)) (x - embed T.a) / d
  ![1 - α - β, α, β]

def coneChild (T : LatticeTriangle) (q : Lattice) : Fin 3 → LatticeTriangle :=
  ![⟨q, T.b, T.c⟩, ⟨q, T.c, T.a⟩, ⟨q, T.a, T.b⟩]

def ND (ts : Finset LatticeTriangle) : Prop := ∀ T ∈ ts, delta T ≠ 0

def CF (ts : Finset LatticeTriangle) : Prop :=
  ∀ T ∈ ts, ∀ U ∈ ts,
    T.carrier ∩ U.carrier = windowHull (T.vertices ∩ U.vertices)

def V (ts : Finset LatticeTriangle) : Finset Lattice :=
  ts.biUnion LatticeTriangle.vertices

def Contained (P : Set RealPlane) (ts : Finset LatticeTriangle) : Prop :=
  ∀ T ∈ ts, T.carrier ⊆ P

def Covers (P : Set RealPlane) (ts : Finset LatticeTriangle) : Prop :=
  ∀ x ∈ P, ∃ T ∈ ts, x ∈ T.carrier

def Compatible (P : Set RealPlane) (ts : Finset LatticeTriangle) : Prop :=
  ND ts ∧ Contained P ts ∧ Covers P ts ∧ CF ts

def EmptyCells (ts : Finset LatticeTriangle) : Prop :=
  ∀ T ∈ ts, ∀ q : Lattice, embed q ∈ T.carrier → q ∈ T.vertices

noncomputable def R (T : LatticeTriangle) (q : Lattice) : Finset LatticeTriangle := by
  classical
  exact if embed q ∈ T.carrier then
    ((Finset.univ : Finset (Fin 3)).image (coneChild T q)).filter (fun U => delta U ≠ 0)
  else {T}

noncomputable def refine (ts : Finset LatticeTriangle) (q : Lattice) :
    Finset LatticeTriangle := ts.biUnion (fun T => R T q)

noncomputable def faceMask (F : Finset Lattice) (q : Lattice) : Finset Lattice := by
  classical
  exact if embed q ∈ windowHull F then insert q F else F

def edgeTraces (ts : Finset LatticeTriangle) (F : Finset Lattice) : Set (Set RealPlane) :=
  {C | ∃ T ∈ ts, C = T.carrier ∩ windowHull F ∧
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y}

def hullBound (S : Finset Lattice) : ℕ :=
  1 + ∑ z ∈ S, (z.1.natAbs + z.2.natAbs)

def integerBox (B : ℕ) : Finset Lattice :=
  (Finset.Icc (-(B : ℤ)) (B : ℤ)).product (Finset.Icc (-(B : ℤ)) (B : ℤ))

noncomputable def A (P : LatticePolygon) : Finset Lattice := by
  classical
  exact (integerBox (hullBound P.vertices)).filter (fun q => embed q ∈ P.carrier)

def missing (A : Finset Lattice) (ts : Finset LatticeTriangle) : Finset Lattice := A \ V ts

def Irredundant (Q : Finset Lattice) : Prop :=
  ∀ q ∈ Q, embed q ∉ windowHull (Q.erase q)

def ell (N : ℕ) (x : RealPlane) : ℝ := (N : ℝ) * x.1 + x.2

def kappa (x : RealPlane) : ℝ := -x.1

noncomputable def slope (N : ℕ) (x : RealPlane) : ℝ := kappa x / ell N x

def Anchor (Q : Finset Lattice) (p : Lattice) (N : ℕ) : Prop :=
  p ∈ Q ∧ ∀ q ∈ Q.erase p, 0 < ell N (embed (q - p))

structure RadialChain (Q : Finset Lattice) (p : Lattice) (N : ℕ) where
  length : ℕ
  point : Fin (length + 2) → Lattice
  range_eq : Set.range point = (Q.erase p : Set Lattice)
  injective : Function.Injective point
  slopes : StrictMono (fun i => slope N (embed (point i - p)))
  determinants : ∀ i j, i < j → 0 < det (point i - p) (point j - p)

def fanCell {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) (i : Fin (c.length + 1)) : LatticeTriangle :=
  ⟨p, c.point i.castSucc, c.point i.succ⟩

def fan {Q : Finset Lattice} {p : Lattice} {N : ℕ}
    (c : RadialChain Q p N) : Finset LatticeTriangle :=
  (Finset.univ : Finset (Fin (c.length + 1))).image (fanCell c)

end ConvexNivat.PolygonTriangulation
