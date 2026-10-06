import ExternalNivatAdapters
import ConvexNivat.CoreLattice

namespace ConvexNivat

theorem convexNivat {A : Type*} [Finite A] (ξ : Configuration A)
    (S : Finset Lattice) (hS : S.Nonempty) (hconv : LatticeConvex S)
    (hlow : complexity ξ S ≤ S.card) : Periodic ξ := by
  exact ExternalNivatAdapters.periodic_of_low_convex_complexity ξ S hS hconv hlow

theorem nivatRectangles {A : Type*} [Finite A] (ξ : Configuration A)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlow : complexity ξ (rectangle n k) ≤ n * k) : Periodic ξ := by
  apply convexNivat ξ (rectangle n k) (rectangle_nonempty n k hn hk)
    (rectangle_latticeConvex n k)
  simpa only [rectangle_card] using hlow

end ConvexNivat
