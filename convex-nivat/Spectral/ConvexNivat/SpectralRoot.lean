import ConvexNivat.StarSpectral

namespace ConvexNivat
noncomputable section

/-- Every exceptional root is a genuine root of the actual tangential period. -/
theorem exceptional_spectrum_root {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (ζ : ℂ)
    (hζ : ζ ∈ exceptionalSpectrum star periods i) :
    ζ ^ periods.multiplier i = 1 := by
  classical
  exact (Polynomial.mem_nthRootsFinset (periods.positive i) 1).mp
    ((Finset.mem_filter.mp hζ).1)

theorem exceptional_spectrum_root_nonzero {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (ζ : ℂ)
    (hζ : ζ ∈ exceptionalSpectrum star periods i) : ζ ≠ 0 := by
  classical
  exact Polynomial.ne_zero_of_mem_nthRootsFinset one_ne_zero
    ((Finset.mem_filter.mp hζ).1)


end
end ConvexNivat
