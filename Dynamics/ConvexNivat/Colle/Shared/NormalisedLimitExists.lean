import ConvexNivat.Colle.Shared.NormalisedWindowLimit
import ConvexNivat.Colle.ArcColle35

namespace ConvexNivat.Colle
noncomputable section

local macro "paidLimitSelection" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_limit_selection))
local macro "paidLimitSameUnion" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_same_union))

theorem normalised_window_limit_exists {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet)
    (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    Nonempty (NormalisedWindowLimit W G)  := by
  obtain ⟨s, hs, field, horbit, hconverges, hagrees⟩ := paidLimitSelection ξ alphabet halphabet W G
  exact ⟨{
    field := field
    index := s
    strict := hs
    orbit := horbit
    converges := hconverges
    agrees_union := hagrees
    same_union := paidLimitSameUnion W G s hs
  }⟩

end
end ConvexNivat.Colle
