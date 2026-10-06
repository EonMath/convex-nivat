import ConvexNivat.SpectralRoot
import ConvexNivat.QuotientDefinitions

namespace ConvexNivat
noncomputable section

def starSpectralFamily {p : ℕ} (star : StarData p) (periods : StarCommonPeriods star) :
    FiniteSpectralFamily star.m where
  direction := fun i => (star.component i).direction
  primitive := fun i => (star.component i).primitive
  pairwise_nonparallel := star.pairwise_nonparallel
  spectrum := exceptionalSpectrum star periods
  spectrum_nonempty := exceptional_spectrum_nonempty star periods
  spectrum_nonzero := exceptional_spectrum_root_nonzero star periods


end
end ConvexNivat
