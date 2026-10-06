import ConvexNivat.Colle.Shared.FacetShiftAssembly
import ConvexNivat.Colle.Shared.FacetSweepSupport

namespace ConvexNivat.Colle
noncomputable section

local macro "facetU" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftData).num 0 ++ `ConvexNivat.Colle.facetShiftLattice))
local macro "paidFacetAssembly" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftAssembly).num 0 ++ `ConvexNivat.Colle.independent_facet_X1_assembly))
local macro "paidFacetSweep" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetSweepSupport).num 0 ++ `ConvexNivat.Colle.independent_facet_uniform_sweep))

private theorem independent_facet_X1_of_geometry_halfstrip
(ξ xper : Configuration ℤ)
(alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet)
(S : Finset Lattice) (hS : GeneratingSet ξ S)
(m : ℕ) (C : AntipodalEdgeCycle S m) (i : ℤ)
(hxper : xper ∈ OrbitClosure ξ)
(hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
(W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
(P : Region (C.direction i) (C.direction G.J))
(hP : P.lattice = normalisedUnion W G)
(hcarrier : P.carrier = closedRealHull (normalisedUnion W G))
(hweak : WeaklyEnveloped S P) (harc : RegionCompleteArc C i G.J P)
(hanchor : det (C.direction i) P.firstAnchor = -1)
(L : NormalisedWindowLimit W G)
(hall : ∀ r : ℕ, AgreesOn L.field
  (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r))
    (hgeometry : ∃ E : ℕ → Finset Lattice,
      (∀ j : ℕ, (E j : Set Lattice) = facetU W G L j) ∧
      ∃ jG : ℕ, ∀ j ≥ jG, EnvelopedWindow S (E j) ∧
        W.normalised (G.subsequence (L.index j)) ⊂ E j)
    (hhalfstrip : ∃ jH : ℕ, ∀ j ≥ jH,
      facetU W G L j ⊆ halfStrip
        (W.normalisedBase (G.subsequence (L.index j))) (C.direction i))
 :
    ∃ N : ℕ, ∃ K : Finset Lattice,
      (K : Set Lattice) ⊆ P.enlargement N ∧
      ∀ I : ℕ, ∃ j : ℕ, I ≤ j ∧ ∃ T : Finset Lattice,
        EnvelopedWindow S T ∧ W.normalised (G.subsequence (L.index j)) ⊂ T ∧
        (T : Set Lattice) ⊆ halfStrip
          (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) ∧
        HasFiniteSweep S
          ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
            (K : Set Lattice)) T := by
  exact paidFacetAssembly ξ xper alphabet halphabet S hS m C i hxper hperiod
    W G P hP hcarrier hweak harc hanchor L hall hgeometry hhalfstrip
    (paidFacetSweep ξ xper alphabet halphabet S hS m C i hxper hperiod
      W G P hP hcarrier hweak harc hanchor L hall)

end
end ConvexNivat.Colle
