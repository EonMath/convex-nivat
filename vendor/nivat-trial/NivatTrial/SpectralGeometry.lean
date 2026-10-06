import NivatTrial.GlobalSpectrum
import NivatTrial.ConvexSupport

/-! The affine relations are divided by the polynomial constructed from the
star data, and the quotient support lies in the actual window erosion. -/

namespace NivatTrial.SpectralGeometry

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.Spectral
open NivatTrial.GlobalSpectrum NivatTrial.LatticePolygon
open scoped Classical

noncomputable section

variable {ι α : Type*} [Fintype ι] [AddCommGroup α] [Fintype α] (T : Star.Data ι α)

def generators (i : ι) : G := (eigenvalues T i).card • T.direction i

theorem quotient_support (g : Laurent) (S : Finset G) (hS : IsLatticeConvex S)
    (hbound : ((polynomial T) * g).coeff.support ⊆ S) :
    g.coeff.support ⊆ placementFinset (generators T) S hS := by
  intro z hz
  apply (mem_placementFinset (generators T) S hS z).mpr
  have h := ConvexSupport.grouped_product_support
    (β := fun i => {k : ZMod (T.commonMultiplier i) // k ∈ frequencies T i})
    T.direction (fun _ k => (eigenvalue k.val : ℂ)) T.direction_ne_zero
    (fun _ k => (eigenvalue k.val).ne_zero) g S
    (fun r hr => hbound (Finsupp.mem_support_iff.mpr hr)) z (Finsupp.mem_support_iff.mp hz)
  change z ∈ placementSet
    (Zonotope.zonotope (fun i => (eigenvalues T i).card • T.direction i)) S
  simpa only [Fintype.card_coe, eigenvalues_card] using h

/-- The bounded factorization hypothesis in the affine budget is now discharged
from the original star data and lattice convexity of the supplied window. -/
theorem bounded_factorization [Nontrivial ι] (S : Finset G) (hS : IsLatticeConvex S)
    (f : Laurent) (hf : f.coeff.support ⊆ S)
    (hrelation : ∃ c : ℂ, act f (fun z => (encoding T (T.total z) : ℂ)) = fun _ => c) :
    ∃ g : Laurent, g.coeff.support ⊆ placementFinset (generators T) S hS ∧
      f = polynomial T * g := by
  obtain ⟨c, hc⟩ := hrelation
  obtain ⟨g, hg⟩ := polynomial_dvd_relation T f c hc
  refine ⟨g, quotient_support T g S hS ?_, hg⟩
  rwa [← hg]

end

end NivatTrial.SpectralGeometry
