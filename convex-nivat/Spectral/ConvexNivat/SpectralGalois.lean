import ConvexNivat.SpectralRoot

open scoped BigOperators

namespace ConvexNivat
noncomputable section

private lemma automorphism_difference {p : ℕ} (star : StarData p)
    (i : Fin star.m) (σ : RayOrientation) (side : TailSide) (a : ZMod p)
    (τ : ℂ ≃ₐ[ℚ] ℂ) (z : Lattice) :
    τ (exceptionalDifference star i σ side a z) =
      exceptionalDifference star i σ side a z := by
  simp only [exceptionalDifference, Pi.sub_apply, map_sub, colorIndicator]
  split_ifs <;> simp

private lemma automorphism_projection {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) (a : ZMod p) (τ : ℂ ≃ₐ[ℚ] ℂ) (ζ : ℂ) (z : Lattice) :
    τ (spectralProjection (star.component i).direction (periods.multiplier i) ζ
      (exceptionalDifference star i σ side a) z) =
    spectralProjection (star.component i).direction (periods.multiplier i) (τ ζ)
      (exceptionalDifference star i σ side a) z := by
  simp [spectralProjection, automorphism_difference]

private lemma automorphism_occurrence {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) (a : ZMod p) (τ : ℂ ≃ₐ[ℚ] ℂ) (ζ : ℂ) :
    spectralOccurs (star.component i).direction (periods.multiplier i) ζ
      (exceptionalDifference star i σ side a) →
    spectralOccurs (star.component i).direction (periods.multiplier i) (τ ζ)
      (exceptionalDifference star i σ side a) := by
  intro h hz
  apply h
  ext z
  apply τ.injective
  change τ (spectralProjection (star.component i).direction (periods.multiplier i) ζ
    (exceptionalDifference star i σ side a) z) = τ 0
  rw [map_zero, automorphism_projection]
  exact congrFun hz z

/-- Remark 2.1': every rationally fixing automorphism preserves the exceptional spectrum.
This implies the stated cyclotomic Galois stability without choosing a specific root field. -/
theorem exceptional_spectrum_galois_stable {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (τ : ℂ ≃ₐ[ℚ] ℂ) (ζ : ℂ) :
    ζ ∈ exceptionalSpectrum star periods i ↔
      τ ζ ∈ exceptionalSpectrum star periods i := by
  classical
  have forward (τ : ℂ ≃ₐ[ℚ] ℂ) (ζ : ℂ)
      (hζ : ζ ∈ exceptionalSpectrum star periods i) :
      τ ζ ∈ exceptionalSpectrum star periods i := by
    obtain ⟨hr, σ, side, a, ho⟩ := Finset.mem_filter.mp hζ
    exact Finset.mem_filter.mpr
      ⟨Polynomial.map_mem_nthRootsFinset_one hr τ,
        σ, side, a, automorphism_occurrence star periods i σ side a τ ζ ho⟩
  refine ⟨forward τ ζ, fun h => ?_⟩
  simpa using forward τ.symm (τ ζ) h

end
end ConvexNivat
