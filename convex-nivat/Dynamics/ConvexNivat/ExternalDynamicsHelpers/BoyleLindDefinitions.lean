import ConvexNivat.Colle.Orbit
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

/-- Coordinates in the actual L2 plane, rather than the product's sup norm. -/
def euclideanCoordinates (x : RealPlane) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x.1, x.2]

def planeNorm (x : RealPlane) : ℝ := ‖euclideanCoordinates x‖

def realQuarterTurn (n : RealPlane) : RealPlane := (-n.2, n.1)

def unitNormals : Set RealPlane := {n | planeNorm n = 1}

/-- V^t(r) for the line perpendicular to the unit normal n. -/
def lineBox (n : RealPlane) (r t : ℝ) : Set RealPlane :=
  {x | |realDot x (realQuarterTurn n)| ≤ r ∧ |realDot x n| ≤ t}

def realBand (n : RealPlane) (t : ℝ) : Set RealPlane :=
  {x | |realDot x n| ≤ t}

def realBall (r : ℝ) : Set RealPlane := {x | planeNorm x ≤ r}

def realTranslate (E : Set RealPlane) (a : RealPlane) : Set RealPlane :=
  {x | x - a ∈ E}

/-- Literal real-set Minkowski sum, used in Boyle--Lind equation (3--1). -/
def realMinkowskiSum (E F : Set RealPlane) : Set RealPlane :=
  {x | ∃ e ∈ E, ∃ f ∈ F, x = e + f}

/-- Symbolic exact-coordinate specialization of Definition 3.1, with real shifts. -/
def RealCodes (ξ : Configuration ℤ) (E F : Set RealPlane) : Prop :=
  ∀ a : RealPlane, ∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
    AgreesOn x y (embed ⁻¹' realTranslate E a) →
      AgreesOn x y (embed ⁻¹' realTranslate F a)

/-- The definition of an expansive line, with its actual finite-width band. -/
def BandDetermines (ξ : Configuration ℤ) (n : RealPlane) (t : ℝ) : Prop :=
  ∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
    AgreesOn x y (embed ⁻¹' realBand n t) → x = y

end
end ConvexNivat.ExternalDynamicsHelpers
