import ConvexNivat.Core

/-!
Trusted statement specification for the optional comparator check.
This module imports only the shared mathematical definitions and Mathlib.
The intentional placeholders specify proof obligations for `Solution.lean`;
this module must never enter the default proof library or Solution's imports.
-/

open ConvexNivat

namespace ConvexNivatComparator

/-- Theorem B / 8.18: the accepted convex Nivat statement. -/
theorem convexNivat {A : Type*} [Finite A] (ξ : Configuration A)
    (S : Finset Lattice) (hS : S.Nonempty) (hconv : LatticeConvex S)
    (hlow : complexity ξ S ≤ S.card) : Periodic ξ := by
  sorry

/-- Corollary 8.19: the accepted rectangular Nivat statement. -/
theorem nivatRectangles {A : Type*} [Finite A] (ξ : Configuration A)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlow : complexity ξ (rectangle n k) ≤ n * k) : Periodic ξ := by
  sorry

/-- Theorem A / T / 7.3: the accepted star-configuration lower bound. -/
theorem theoremT {p : ℕ} (θ : Configuration (ZMod p))
    (hθ : IsStarConfiguration θ) (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : LatticeConvex S) :
    S.card + 1 ≤ complexity θ S := by
  sorry

end ConvexNivatComparator
