import ConvexNivat.Colle.GP.ProductCycle
import ConvexNivat.Colle.GP.DirectionOrder

namespace ConvexNivat.Colle

theorem differenceFactors_edge_cycle (m : ℕ) (hm : 2 ≤ m) (h : Fin m → Lattice)
    (hnonzero : ∀ i, h i ≠ 0)
    (hpairwise : Pairwise (fun i j => Nonparallel (h i) (h j))) :
    Nonempty (AntipodalEdgeCycle (supportWindow (differenceFactors m h)) m) := by
  obtain ⟨O⟩ := generic_labelled_antipodal_direction_order m hm h hnonzero hpairwise
  obtain ⟨C, _, _⟩ := (antipodal_zonotope_actual_support_vertices m hm h hnonzero hpairwise O).2
  exact ⟨C⟩

end ConvexNivat.Colle
