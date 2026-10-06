import ConvexNivat.Colle.Shared.IndependentCofinalExtension

namespace ConvexNivat.Colle
noncomputable section

local macro "paidFullContextContradiction" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.IndependentCofinalExtension).num 0 ++ `ConvexNivat.Colle.independent_full_context_contradiction))
local macro "paidFirstFailureIff" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchLimitSteps).num 0 ++ `ConvexNivat.Colle.limit_first_failure_iff_not_all))

theorem source_conditioned_fixed_patch_propagation (ξ xper : Configuration ℤ)
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
    ∃ n' : ℕ, ∃ E : ℕ → Finset Lattice, ∃ j₀ I₀ : ℕ,
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
        (P.enlargement n')) ∧
      (∀ j ≥ j₀, EnvelopedWindow S (E j) ∧
        W.normalised (G.subsequence (L.index j)) ⊂ E j ∧
        (E j : Set Lattice) ⊆ halfStrip
          (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) ∧
        HasFiniteSweep S ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
          (E j₀ : Set Lattice)) (E j)) ∧
      (∀ j ≥ I₀, AgreesOn L.field (W.shiftedField (G.subsequence (L.index j)))
        (E j₀ : Set Lattice)) ∧
      ∀ j ≥ max j₀ I₀, AgreesOn (W.shiftedField (G.subsequence (L.index j)))
        (translate ((G.phase : ℤ) • C.direction i) xper) (E j : Set Lattice) := by
  exact (paidFullContextContradiction ξ xper alphabet halphabet S hS m C i hxper hperiod
    W G P hP hcarrier hweak harc hanchor L hall).elim

theorem normalised_window_first_failing_enlargement (ξ xper : Configuration ℤ)
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
    (L : NormalisedWindowLimit W G) :
    ∃ n : ℕ, AgreesOn L.field (translate ((G.phase : ℤ) • C.direction i) xper)
      (P.enlargement n) ∧
      ¬ AgreesOn L.field (translate ((G.phase : ℤ) • C.direction i) xper)
        (P.enlargement (n + 1)) := by
  apply (paidFirstFailureIff W G P hP L).2
  intro hall
  exact paidFullContextContradiction ξ xper alphabet halphabet S hS m C i hxper hperiod
    W G P hP hcarrier hweak harc hanchor L hall

end
end ConvexNivat.Colle
