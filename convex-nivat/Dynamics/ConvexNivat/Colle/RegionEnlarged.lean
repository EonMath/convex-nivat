import ConvexNivat.Colle.Shared.HullBoundary

namespace ConvexNivat.Colle

theorem region_enlargement_region {v w : Lattice} (P : Region v w) (n : ℕ) :
    ∃ Q : Region v w, Q.lattice = P.enlargement n := by
  obtain ⟨Q, hQ, _⟩ := region_enlargement_geometry_join P n
  exact ⟨Q, hQ⟩

end ConvexNivat.Colle
