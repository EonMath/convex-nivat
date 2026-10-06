import ConvexNivat.SectorSpectralDefinitions
import ConvexNivat.ExceptionalAnnihilation
import ConvexNivat.SourceGaps.FullAWitness
import ConvexNivat.SourceGaps.FullAWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ConvexNivat
noncomputable section

structure FullARemarkSourceContext (p : ℕ) where
  star : StarData p
  tangentialStep : Fin star.m → ℕ
  tangential_positive : ∀ i, 0 < tangentialStep i
  tangential_period : ∀ i, HasPeriod (star.component i).field
    ((tangentialStep i : ℤ) • (star.component i).direction)
  commonScale : ℕ
  commonScale_positive : 0 < commonScale
  commonScale_period : ∀ j (z : Lattice),
    HasPeriod (star.component j).leftTail ((commonScale : ℤ) • z) ∧
    HasPeriod (star.component j).rightTail ((commonScale : ℤ) • z)
  periods : StarCommonPeriods star
  multiple : ∀ i, tangentialStep i ∣ periods.multiplier i
  least_common : ∀ i (κ : ℕ), 0 < κ → tangentialStep i ∣ κ →
    (∀ j, HasPeriod (star.component j).leftTail
      ((κ : ℤ) • (star.component i).direction) ∧
      HasPeriod (star.component j).rightTail
        ((κ : ℤ) • (star.component i).direction)) →
    periods.multiplier i ≤ κ
  transverse : Fin star.m → Lattice
  unimodular : ∀ i, det (star.component i).direction (transverse i) = 1
  caseB : InCaseB star periods
  encoding : ZMod p → ℤ
  encoding_spectrum : SpectrumPreservingEncoding star periods encoding
  window : Finset Lattice
  window_nonempty : window.Nonempty
  window_convex : LatticeConvex window
  erosion_nonempty : (erosion (spectralZonotope star periods).carrier window).Nonempty

def fullARemarkContextFromWindow (S : Finset Lattice) (hS : S.Nonempty)
    (hconv : LatticeConvex S)
    (herosion : (erosion (spectralZonotope FullAWitness.star FullAWitness.periods).carrier S).Nonempty) :
    FullARemarkSourceContext 2 where
  star := FullAWitness.star
  tangentialStep := fun _ => 2
  tangential_positive := by intro i; norm_num
  tangential_period := FullAWitness.field_period
  commonScale := 2
  commonScale_positive := by norm_num
  commonScale_period := fun j z => ⟨FullAWitness.grid_left j z, FullAWitness.grid_right j z⟩
  periods := FullAWitness.periods
  multiple := by intro i; exact dvd_refl 2
  least_common := FullAWitness.least_periods
  transverse := FullAWitness.transverse
  unimodular := by
    intro i
    change Fin 3 at i
    change det (FullAWitness.direction i) (FullAWitness.transverse i) = 1
    fin_cases i <;> norm_num [FullAWitness.direction, FullAWitness.transverse, det]
  caseB := FullAWitness.caseB
  encoding := Classical.choose (spectrum_preserving_integer_encoding FullAWitness.star FullAWitness.periods)
  encoding_spectrum := Classical.choose_spec
    (spectrum_preserving_integer_encoding FullAWitness.star FullAWitness.periods)
  window := S
  window_nonempty := hS
  window_convex := hconv
  erosion_nonempty := herosion

theorem remark3_1_prime_full_A_nonextension :
    ∃ p : ℕ, ∃ ctx : FullARemarkSourceContext p,
      ∃ ε ε' : SectorSigns ctx.star,
        (¬ RealisedSector ctx.star ε ∨ ¬ RealisedSector ctx.star ε') ∧
        ∃ a : ZMod p,
          appliedSectorBackground ctx.star ctx.periods ε a ≠
            appliedSectorBackground ctx.star ctx.periods ε' a := by
  obtain ⟨S, hS, hconv, herosion⟩ :=
    integralZonotope_window_exists (spectralZonotope FullAWitness.star FullAWitness.periods)
  refine ⟨2, fullARemarkContextFromWindow S hS hconv herosion,
    FullAWitness.signs0, FullAWitness.signs1, ?_, 0, ?_⟩
  · exact Or.inl FullAWitness.signs0_unrealised
  · exact FullAWitness.failure

end
end ConvexNivat
