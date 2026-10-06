import ConvexNivat.OriginalMain
import ConvexNivat.MainTheorem

open ConvexNivat

namespace ConvexNivatComparator

/-- Theorem B / 8.18: the accepted convex Nivat statement. -/
theorem convexNivat {A : Type*} [Finite A] (ξ : Configuration A)
    (S : Finset Lattice) (hS : S.Nonempty) (hconv : LatticeConvex S)
    (hlow : complexity ξ S ≤ S.card) : Periodic ξ := by
  exact ConvexNivat.convexNivat ξ S hS hconv hlow

/-- Corollary 8.19: the accepted rectangular Nivat statement. -/
theorem nivatRectangles {A : Type*} [Finite A] (ξ : Configuration A)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlow : complexity ξ (rectangle n k) ≤ n * k) : Periodic ξ := by
  exact ConvexNivat.nivatRectangles ξ n k hn hk hlow

/-- Theorem A / T / 7.3: the accepted star-configuration lower bound. -/
theorem theoremT {p : ℕ} (θ : Configuration (ZMod p))
    (hθ : IsStarConfiguration θ) (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : LatticeConvex S) :
    S.card + 1 ≤ complexity θ S := by
  exact ConvexNivat.theoremT θ hθ S hS hconv

end ConvexNivatComparator
