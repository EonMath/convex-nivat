import ConvexNivat.Colle.Definitions

namespace ConvexNivat.Colle

/-- The complete consecutive boundary arc retained by the source construction.
The direction at offset `d` is the successor at exactly `i + 1 + d`, and
every intervening cycle index is represented by that same bounded edge. -/
structure RegionCompleteArc {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i J : ℤ) {v w : Lattice}
    (P : Region v w) : Prop where
  first_ray : v = C.direction i
  second_ray : w = C.direction J
  lower : i + 1 ≤ J
  upper : J ≤ i + (m : ℤ) - 1
  bounded_count : P.boundedCount = (J - i - 1).toNat
  ordered_directions : ∀ d : Fin P.boundedCount,
    P.boundedDirection d = C.direction (i + 1 + (d.val : ℤ))
  complete_coverage : ∀ j : ℤ, i + 1 ≤ j → j < J →
    ∃ d : Fin P.boundedCount, i + 1 + (d.val : ℤ) = j ∧
      P.boundedDirection d = C.direction j

/-- Geometric compatibility with the actual generating window. It asserts
no sweep, pattern agreement, period, or dynamical conclusion. -/
def RegionCompatibleArc (S : Finset Lattice) {v w : Lattice}
    (P : Region v w) : Prop :=
  ∃ m : ℕ, ∃ C : AntipodalEdgeCycle S m, ∃ i J : ℤ,
    RegionCompleteArc C i J P

/-- A pinned source arc supplies the existential geometry bundle for the
same region, without changing either ray or the generating window. -/
theorem region_complete_arc_compatible {S : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} {i J : ℤ} {v w : Lattice}
    {P : Region v w} (harc : RegionCompleteArc C i J P) :
    RegionCompatibleArc S P := by
  exact ⟨m, C, i, J, harc⟩

/-- The predecessor used in Definition 3.2 is the actual immediately
preceding cycle direction, including the case of no bounded edges. -/
theorem region_complete_arc_predecessor {S : Finset Lattice} {m : ℕ}
    {C : AntipodalEdgeCycle S m} {i J : ℤ} {v w : Lattice}
    {P : Region v w} (harc : RegionCompleteArc C i J P) :
    P.predecessor = C.direction (J - 1) := by
  unfold Region.predecessor
  split_ifs with h
  · rw [harc.ordered_directions]
    congr 1
    have hcount := harc.bounded_count
    have hlower := harc.lower
    simp only [Fin.val_mk]
    omega
  · rw [harc.first_ray]
    congr 1
    have hcount := harc.bounded_count
    have hlower := harc.lower
    omega

end ConvexNivat.Colle
