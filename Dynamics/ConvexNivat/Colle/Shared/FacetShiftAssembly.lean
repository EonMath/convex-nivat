import ConvexNivat.Colle.Shared.FacetShiftData
import ConvexNivat.Colle.Shared.CofinalExtensionRoute

namespace ConvexNivat.Colle
noncomputable section

local macro "facetU" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftData).num 0 ++ `ConvexNivat.Colle.facetShiftLattice))

private theorem independent_facet_X1_assembly
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
    (hsweep : ∀ (E : ℕ → Finset Lattice)
    (hE : ∀ j : ℕ, (E j : Set Lattice) = facetU W G L j)
    (jG : ℕ)
    (hgeometry : ∀ j ≥ jG, EnvelopedWindow S (E j) ∧
      W.normalised (G.subsequence (L.index j)) ⊂ E j),
      ∃ N : ℕ, ∃ K : Finset Lattice,
      (K : Set Lattice) ⊆ P.enlargement N ∧
      ∃ jS : ℕ, ∀ j ≥ jS, HasFiniteSweep S
        ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
          (K : Set Lattice)) (E j)) :
    ∃ N : ℕ, ∃ K : Finset Lattice,
      (K : Set Lattice) ⊆ P.enlargement N ∧
      ∀ I : ℕ, ∃ j : ℕ, I ≤ j ∧ ∃ T : Finset Lattice,
        EnvelopedWindow S T ∧ W.normalised (G.subsequence (L.index j)) ⊂ T ∧
        (T : Set Lattice) ⊆ halfStrip
          (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) ∧
        HasFiniteSweep S
          ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
            (K : Set Lattice)) T := by
  obtain ⟨E, hE, jG, hgeom⟩ := hgeometry
  obtain ⟨jH, hH⟩ := hhalfstrip
  obtain ⟨N, K, hK, jS, hS⟩ := hsweep E hE jG hgeom
  refine ⟨N, K, hK, ?_⟩
  intro I
  let j := max I (max jG (max jH jS))
  have hjI : I ≤ j := le_max_left _ _
  have hjG : jG ≤ j := (le_max_left _ _).trans (le_max_right _ _)
  have hjH : jH ≤ j := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hjS : jS ≤ j := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨j, hjI, E j, (hgeom j hjG).1, (hgeom j hjG).2, ?_, hS j hjS⟩
  rw [hE j]
  exact hH j hjH

end
end ConvexNivat.Colle
