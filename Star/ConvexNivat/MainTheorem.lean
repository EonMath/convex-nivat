import ConvexNivat.SourceGaps.QuadraticObservables
import ConvexNivat.SourceGaps.DimensionJoin
import ConvexNivat.StarFirstCase
import ConvexNivat.Geometry.ZonotopeDecomposition
import ConvexNivat.SpectralWitnessConsumers

namespace ConvexNivat

/-- Theorem T (§0.2), Theorem A (Introduction), and Theorem 7.3: the same claim. -/
theorem theoremT {p : ℕ} (θ : Configuration (ZMod p))
    (hθ : IsStarConfiguration θ) (S : Finset Lattice)
    (hS : S.Nonempty) (hconv : LatticeConvex S) :
    S.card + 1 ≤ complexity θ S := by
  classical
  obtain ⟨star, rfl⟩ := hθ
  let periods := chooseStarCommonPeriods star
  by_cases hB : InCaseB star periods
  · obtain ⟨w, hw⟩ := spectrum_preserving_integer_encoding star periods
    obtain ⟨d, hbody, hd, hJ⟩ :=
      quadratic_witness_in_spectral_difference_body star periods hB w hw
    have hdir : Nonparallel
        ((spectralZonotope star periods).firstDirection star.two_le)
        ((spectralZonotope star periods).secondDirection star.two_le) := by
      apply star.pairwise_nonparallel
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    obtain ⟨q, hq, hqd⟩ :=
      corollary6_2 (spectralZonotope star periods) star.two_le hdir d hbody
    exact caseB_complexity_from_quadratic_witness star periods hB w hw S hconv
      q d hd hq hqd hJ
  · unfold InCaseB at hB
    push Not at hB
    obtain ⟨a, ha⟩ := hB
    let P : StarPeriodData star :=
      { multiplier := periods.multiplier
        multiplier_pos := periods.positive
        component_period := periods.component_period
        all_tail_periods := fun i j => ⟨periods.left_period i j, periods.right_period i j⟩ }
    exact proposition_1_3 star P a ha S hS

end ConvexNivat
