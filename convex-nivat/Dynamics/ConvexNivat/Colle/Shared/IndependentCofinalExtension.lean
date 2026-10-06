import ConvexNivat.Colle.Shared.FacetX1GeometryOnly
import ConvexNivat.Colle.Shared.FacetGeometry

namespace ConvexNivat.Colle
noncomputable section

local macro "paidGeometryOnlyX1" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetX1GeometryOnly).num 0 ++ `ConvexNivat.Colle.independent_facet_X1_of_geometry))
local macro "paidFacetGeometry" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetGeometry).num 0 ++ `ConvexNivat.Colle.independent_facet_geometry))
local macro "paidCofinalContradiction" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CofinalExtensionRoute).num 0 ++ `ConvexNivat.Colle.cofinal_extension_implies_false))

private theorem independent_cofinal_extension
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
  (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r)) :
    ∃ N : ℕ, ∃ K : Finset Lattice,
      (K : Set Lattice) ⊆ P.enlargement N ∧
      ∀ I : ℕ, ∃ j : ℕ, I ≤ j ∧ ∃ T : Finset Lattice,
        EnvelopedWindow S T ∧ W.normalised (G.subsequence (L.index j)) ⊂ T ∧
        (T : Set Lattice) ⊆ halfStrip
          (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) ∧
        HasFiniteSweep S
          ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
            (K : Set Lattice)) T := by
  exact paidGeometryOnlyX1 ξ xper alphabet halphabet S hS m C i hxper hperiod
    W G P hP hcarrier hweak harc hanchor L hall
    (paidFacetGeometry ξ xper alphabet halphabet S hS m C i hxper hperiod
      W G P hP hcarrier hweak harc hanchor L hall)

private theorem independent_full_context_contradiction
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
  (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r)) : False := by
  exact paidCofinalContradiction ξ xper alphabet halphabet S hS m C i hxper hperiod
    W G P hP hcarrier hweak harc hanchor L hall
    (independent_cofinal_extension ξ xper alphabet halphabet S hS m C i hxper hperiod
      W G P hP hcarrier hweak harc hanchor L hall)

end
end ConvexNivat.Colle
