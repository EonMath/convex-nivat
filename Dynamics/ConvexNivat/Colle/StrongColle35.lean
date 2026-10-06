import ConvexNivat.Colle.Shared.NormalisedLimitExists
import ConvexNivat.Colle.Shared.FixedPatchPropagation

namespace ConvexNivat.Colle
noncomputable section

theorem colle_3_5_with_arc (ξ : Configuration ℤ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) (m : ℕ)
    (C : AntipodalEdgeCycle S m) (i : ℤ)
    (xper : Configuration ℤ) (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ k : ℤ, k ≠ 0 ∧ HasPeriod xper (k • C.direction i))
    (hmismatch : UnboundedHalfStripMismatch ξ xper S (C.direction i)) :
    ∃ J : ℤ, i + 1 ≤ J ∧ J ≤ i + (m : ℤ) - 1 ∧
      ∃ P : Region (C.direction i) (C.direction J), WeaklyEnveloped S P ∧
        RegionCompleteArc C i J P ∧
        det (C.direction i) P.firstAnchor = -1 ∧
        ∃ ϑ ∈ OrbitClosure ξ, ∃ n k : ℕ,
          AgreesOn ϑ (translate ((k : ℤ) • C.direction i) xper) (P.enlargement n) ∧
            ¬ AgreesOn ϑ (translate ((k : ℤ) • C.direction i) xper)
              (P.enlargement (n + 1)) ∧
            ∃ W : AlternatingWindows ξ xper C i, ∃ G : GrowingSubsequence W,
              G.J = J ∧ k = G.phase ∧ P.lattice = normalisedUnion W G ∧
                P.carrier = closedRealHull (normalisedUnion W G) ∧
                ∃ s : ℕ → ℕ, StrictMono s ∧
                  PointwiseLimit (fun j => W.shiftedField (G.subsequence (s j))) ϑ := by
  obtain ⟨W⟩ := alternating_windows_terminal_normalisation
    ξ xper A hA S hS m C i hxper hperiod hmismatch
  obtain ⟨a, ha, hp⟩ := hperiod
  have hperiod : ∃ k : ℤ, k ≠ 0 ∧ HasPeriod xper (k • C.direction i) := ⟨a, ha, hp⟩
  obtain ⟨G⟩ := residue_and_first_growing_edge_subsequence W a ha hp
  obtain ⟨P, hP, hcarrier, hweak, harc, hanchor, _⟩ :=
    normalised_union_actual_region_with_arc W G
  obtain ⟨L⟩ := normalised_window_limit_exists A hA hxper hperiod W G
  obtain ⟨n, hagrees, hdisagrees⟩ := normalised_window_first_failing_enlargement
    ξ xper A hA S hS m C i hxper hperiod W G P hP hcarrier hweak harc hanchor L
  exact ⟨G.J, G.lower, G.upper, P, hweak, harc, hanchor,
    L.field, L.orbit, n, G.phase, hagrees, hdisagrees,
    W, G, rfl, rfl, hP, hcarrier, L.index, L.strict, L.converges⟩

end
end ConvexNivat.Colle
