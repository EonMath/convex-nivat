import ConvexNivat.StarSpectral

open scoped BigOperators
namespace ConvexNivat
noncomputable section

abbrev SectorSigns {p : ℕ} (star : StarData p) := Fin star.m → TailSide

/-- Determinant against a real point, extending the source's πᵢ. -/
def realHeight (v : Lattice) (x : RealPlane) : ℝ :=
  (v.1 : ℝ) * x.2 - (v.2 : ℝ) * x.1

/-- Actual strict-sign chamber, which is a sector exactly when it is nonempty. -/
def sectorCone {p : ℕ} (star : StarData p) (ε : SectorSigns star) : Set RealPlane :=
  {x | ∀ i, match ε i with
    | .left => realHeight (star.component i).direction x < 0
    | .right => 0 < realHeight (star.component i).direction x}

/-- Realised sign choices must have a point in their actual real sector. -/
def RealisedSector {p : ℕ} (star : StarData p) (ε : SectorSigns star) : Prop :=
  (sectorCone star ε).Nonempty

/-- Geometric adjacency at the specified ray: its nonzero direction point lies
in the closures of two distinct, nonempty sector cones. The sign conclusion of
Lemma 3.0 is not assumed in this definition. -/
def SectorsAdjacentAtRay {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) (ε ε' : SectorSigns star) : Prop :=
  RealisedSector star ε ∧ RealisedSector star ε' ∧ ε ≠ ε' ∧
    embed (σ.sign • (star.component i).direction) ∈ closure (sectorCone star ε) ∧
    embed (σ.sign • (star.component i).direction) ∈ closure (sectorCone star ε')

/-- Actual Θ_ε, with no assumption that ε is realised in its construction. -/
def sectorBackground {p : ℕ} (star : StarData p) (ε : SectorSigns star) :
    Configuration (ZMod p) := fun z => ∑ i : Fin star.m, componentTail star i (ε i) z

def raySide {p : ℕ} (star : StarData p) (i j : Fin star.m)
    (σ : RayOrientation) : TailSide :=
  if 0 < σ.sign * det (star.component j).direction (star.component i).direction
  then .right else .left


end
end ConvexNivat
