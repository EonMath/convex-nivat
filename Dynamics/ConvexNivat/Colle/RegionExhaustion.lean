import ConvexNivat.Colle.Shared.PositionedWindows

namespace ConvexNivat.Colle

theorem enveloped_window_exhaustion (S : Finset Lattice) (m : ℕ)
    (C : AntipodalEdgeCycle S m) (i : ℤ) (F : Finset Lattice)
    (hF : ∀ z ∈ F, -1 ≤ det (C.direction i) z) :
    ∃ B : Finset Lattice, EnvelopedWindow S B ∧ F ⊆ B ∧
      ∀ z ∈ supportRow B (C.direction i), det (C.direction i) z = -1 := by
  obtain ⟨e, he, hB, hmono, hrow, hlength, hleft, hright, hexhaust, hfinite⟩ :=
    positioned_integer_homothetic_windows C i
  obtain ⟨N, hN⟩ := hfinite F hF
  exact ⟨positionedHomothetyWindow C i e N, hB N, hN, hrow N⟩

end ConvexNivat.Colle
