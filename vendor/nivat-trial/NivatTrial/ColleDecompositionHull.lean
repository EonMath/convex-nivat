import NivatTrial.ColleRegionalBranches

/-! Hull decompositions retaining the actual list of independent directions.
This supplies both the recurrence and the geometry in later region limits. -/

namespace NivatTrial.ColleDecompositionHull

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.ExternalInputs NivatTrial.OneSidedRecurrence NivatTrial.IncrementSupport
open NivatTrial.ColleZonotopeEnvelope
open scoped Classical
noncomputable section

theorem period_list_pairwise {M n : ℕ} {θ : Lattice → Fin M}
    (E : IntegerDecomposition (integerField θ) n) :
    (Finset.univ.toList.map E.period).Pairwise (fun u v => det u v ≠ 0) := by
  have hp : (Finset.univ.toList : List (Fin n)).Pairwise
      (fun i j => det (E.period i) (E.period j) ≠ 0) :=
    (Finset.nodup_toList (Finset.univ : Finset (Fin n))).pairwise_of_forall_ne
      (fun i _ j _ hij => E.independent i j hij)
  exact hp.map E.period (fun _ _ hij => hij)

theorem period_list_nonzero {M n : ℕ} {θ : Lattice → Fin M}
    (E : IntegerDecomposition (integerField θ) n) :
    ∀ d ∈ Finset.univ.toList.map E.period, d ≠ 0 := by
  intro d hd
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hd
  exact E.period_ne_zero i

theorem period_list_signed {M n : ℕ} {θ : Lattice → Fin M}
    (E : IntegerDecomposition (integerField θ) n) :
    ∀ d ∈ Finset.univ.toList.map E.period,
      d ∈ signedDirections E.period ∧ -d ∈ signedDirections E.period := by
  intro d hd
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hd
  exact ⟨(mem_signedDirections E.period _).mpr ⟨i,Or.inl rfl⟩,
    (mem_signedDirections E.period _).mpr ⟨i,Or.inr rfl⟩⟩

theorem actual_product_recurrence {M n : ℕ} {θ : Lattice → Fin M}
    (E : IntegerDecomposition (integerField θ) n) :
    iteratedIncrement (Finset.univ.toList.map E.period) (integerField θ) = 0 := by
  have he := congrArg (iteratedIncrement (Finset.univ.toList.map E.period)) E.sum_eq
  exact he.symm.trans (decomposition_annihilator E.component E.period E.component_period)

theorem exists_decomposition_with_same_periods {M n : ℕ}
    {θ x : Lattice → Fin M} (E : IntegerDecomposition (integerField θ) n)
    (hx : x ∈ languageHull θ) :
    ∃ E' : IntegerDecomposition (integerField x) n, E'.period = E.period := by
  have hann := iteratedIncrement_passes_to_languageHull _ (integerField θ) (integerField x)
    (encode_mem_languageHull integerCode hx) (actual_product_recurrence E)
  obtain ⟨F,hp,he⟩ := NivatTrial.IntegerDecomposition.product_decomposition n E.period
    E.period_ne_zero E.independent _ hann
  exact ⟨⟨F,E.period,E.period_ne_zero,E.independent,hp,he⟩,rfl⟩

end
end NivatTrial.ColleDecompositionHull
