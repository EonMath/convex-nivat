import ConvexNivat.Colle.Shared.NormalisedWindowLimit

namespace ConvexNivat.Colle
noncomputable section

/-- Fixed integer displacement of the J supporting row. -/
private def facetShiftDepth {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J : ℤ) : ℤ :=
  det (C.direction (J - 1)) (C.direction J) *
    det (C.direction J) (C.direction (J + 1))

/-- The actual normalized support intersection with only the J direction shifted. -/
private def facetShiftLattice {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) : Set Lattice :=
  {z | ∀ r : ℤ,
    det (C.direction r)
      ((W.boundary (G.subsequence (L.index j))).vertex r -
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i) -
      (if C.direction r = C.direction G.J then facetShiftDepth C G.J else 0)
      ≤ det (C.direction r) z}

end
end ConvexNivat.Colle
