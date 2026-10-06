import ConvexNivat.SpectralFamily
import ConvexNivat.QuotientSpanning
import ConvexNivat.SectorCaseB
import ConvexNivat.StarWitness
import ConvexNivat.OperatorWitnessQuotient

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

/-- Exact star-bound Lemma 5.2, including the actual source A and Z. -/
theorem spectral_quotient_spanning {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) :
    QuotientSpannedBy (exceptionalPolynomial star periods)
      (latticePoints ((spectralZonotope star periods).carrier -
        (spectralZonotope star periods).carrier)) := by
  exact quotient_spanned_by_spectral_difference_body (starSpectralFamily star periods) star.two_le

private lemma realised_sector_exists {p : ℕ} (star : StarData p) :
    ∃ ε : SectorSigns star, RealisedSector star ε := by
  classical
  let slopes : Finset ℝ := Finset.univ.image (fun i : Fin star.m =>
    ((star.component i).direction.2 : ℝ) / ((star.component i).direction.1 : ℝ))
  obtain ⟨t, ht⟩ := slopes.exists_notMem
  let x : RealPlane := (1, t)
  have hn (i : Fin star.m) : realHeight (star.component i).direction x ≠ 0 := by
    intro hi
    by_cases hfirst : (star.component i).direction.1 = 0
    · have hsecond : (star.component i).direction.2 = 0 := by
        simpa [realHeight, x, hfirst] using hi
      apply primitive_ne_zero _ (star.component i).primitive
      exact Prod.ext hfirst hsecond
    · apply ht
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
      have hf : ((star.component i).direction.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hfirst
      dsimp [realHeight, x] at hi
      apply (div_eq_iff hf).mpr
      nlinarith
  let ε : SectorSigns star := fun i =>
    if 0 < realHeight (star.component i).direction x then .right else .left
  refine ⟨ε, x, ?_⟩
  intro i
  dsimp [ε]
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) (hn i)

/-- Source Lemma 5.1 bound to its actual star inputs; no recursions are assumed. -/
theorem spectral_quadratic_birecursion {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (w : ZMod p → ℤ) :
    applyInDifference (exceptionalPolynomial star periods)
        (quadraticWitness (starDifferencePolynomial star periods) (encodedStar star w)) = 0 ∧
      applyAtFirstPoint (exceptionalPolynomial star periods)
        (quadraticWitness (starDifferencePolynomial star periods) (encodedStar star w)) = 0 := by
  classical
  let : NeZero p := ⟨star.prime.ne_zero⟩
  obtain ⟨ε, hε⟩ := realised_sector_exists star
  obtain ⟨hA, _, hperiod⟩ := encoded_star_applied_background star periods hB ε hε w
  refine lemma_5_1 Finset.univ periods.vector (exceptionalPolynomial star periods)
    (encodedStar star w) (encodedSectorBackground star periods ε w) ?_ hA ?_
  · exact indicators_killed_encoding_killed star.configuration
      (starDifferencePolynomial star periods) hB (fun a => (w a : ℂ))
  · intro i hi
    exact hperiod i

private def witnessPeriods {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) : StarPeriodData star where
  multiplier := periods.multiplier
  multiplier_pos := periods.positive
  component_period := periods.component_period
  all_tail_periods := fun i j => ⟨periods.left_period i j, periods.right_period i j⟩

/-- Source Proposition 5.3, including nonzero displacement and nonzero witness. -/
theorem quadratic_witness_in_spectral_difference_body {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (w : ZMod p → ℤ) (hw : SpectrumPreservingEncoding star periods w) :
    ∃ d : Lattice, embed d ∈
        (spectralZonotope star periods).carrier - (spectralZonotope star periods).carrier ∧
      d ≠ 0 ∧
      quadraticWitness (starDifferencePolynomial star periods) (encodedStar star w) d ≠ 0 := by
  classical
  let : NeZero p := ⟨star.prime.ne_zero⟩
  obtain ⟨hfin, hne⟩ := lemma_4_2 star (witnessPeriods star periods) w hw.1 hB
  obtain ⟨h₁, h₂⟩ := spectral_quadratic_birecursion star periods hB w
  obtain ⟨d, hd, hJ⟩ := witness_confined_by_quotient_span
    (exceptionalPolynomial star periods) _ (spectral_quotient_spanning star periods)
    (quadraticWitness (starDifferencePolynomial star periods) (encodedStar star w))
    hfin h₁ h₂ hne
  refine ⟨d, hd, ?_, hJ⟩
  intro hzero
  subst d
  apply hJ
  exact quadraticWitness_zero_displacement star.configuration
    (starDifferencePolynomial star periods) hB (fun a => (w a : ℂ))

end
end ConvexNivat
