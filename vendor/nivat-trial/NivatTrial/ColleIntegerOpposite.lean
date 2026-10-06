import NivatTrial.ColleRationalDirections

/-! Direct composition of the internally proved opposite-direction theorem
with the actual integer periodic decomposition and its coordinate alignment. -/

namespace NivatTrial.ColleIntegerOpposite

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.Dynamics NivatTrial.ExternalInputs
open NivatTrial.ColleOppositeDirections NivatTrial.ColleRationalDirections
open scoped Classical
noncomputable section

theorem opposite_component_of_low_complexity {M n : ℕ}
    (θ : Lattice → Fin M) (E : IntegerDecomposition (integerField θ) n)
    (S : Finset Lattice)
    (hlow : patternComplexity θ S ≤ S.card)
    (hnot : ¬IsPeriodic θ) :
    ∃ i : Fin n,
      OneSidedNonexpansive θ (embed (E.period i)) ∧
      OneSidedNonexpansive θ (-(embed (E.period i))) := by
  obtain ⟨v,hv,hp,hn⟩ :=
    exists_opposite_nonexpansive_of_low_complexity θ S hlow hnot
  exact opposite_nonexpansive_component_direction θ E v hv hp hn

theorem horizontal_opposite_of_low_complexity {M n : ℕ}
    (hn : 2 ≤ n) (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) n)
    (S : Finset Lattice)
    (hlow : patternComplexity θ S ≤ S.card)
    (hnot : ¬IsPeriodic θ) :
    ∃ i j : Fin n, ∃ c : ℕ, ∃ e : Lattice ≃+ Lattice,
      i ≠ j ∧ 0 < c ∧
      e (c • NivatTrial.RowDetermination.horizontal) = E.period i ∧
      (e.symm (E.period j)).2 ≠ 0 ∧
      OneSidedNonexpansive (θ ∘ e) (1, 0) ∧
      OneSidedNonexpansive (θ ∘ e) (-(1, 0)) := by
  obtain ⟨v,hv,hp,hneg⟩ :=
    exists_opposite_nonexpansive_of_low_complexity θ S hlow hnot
  exact exists_horizontal_opposite_nonexpansive hn θ E v hv hp hneg

end
end NivatTrial.ColleIntegerOpposite
