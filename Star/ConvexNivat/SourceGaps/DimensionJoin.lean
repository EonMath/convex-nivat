import ConvexNivat.AffineDimensionConsumer
import ConvexNivat.Geometry.Basic
import ConvexNivat.Geometry.ZonotopeBasic

namespace ConvexNivat

noncomputable section
set_option linter.unusedVariables false

/-- The source's finite-pattern ambient bound dim_Q U_S ≤ |L|=P_θ(S). -/
theorem affineObservableSpace_finrank_le_complexity {p : ℕ} (star : StarData p)
    (w : ZMod p → ℤ) (S : Finset Lattice) :
    Module.finrank ℚ (affineObservableSpace star w S) ≤ complexity star.configuration S := by
  classical
  have : NeZero p := ⟨star.prime.ne_zero⟩
  let : Fintype (OccurringPattern star S) := Fintype.ofFinite _
  calc
    _ ≤ Module.finrank ℚ (OccurringPattern star S → ℚ) := Submodule.finrank_le _
    _ = complexity star.configuration S := by
      rw [Module.finrank_fintype_fun_eq_card]
      exact Set.fintypeCard_eq_ncard _

/-- Remark 2.6, exact dimension and complexity join when R_Z(S) is empty.
The geometric placement statement is already released in Geometry.Primitives. -/
theorem remark2_6_empty_erosion_dimension_join {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (hw : SpectrumPreservingEncoding star periods w)
    (S : Finset Lattice) (hS : S.Nonempty) (hconvex : LatticeConvex S)
    (hR : erosion (spectralZonotope star periods).carrier S = ∅) :
    S.card + 1 ≤ Module.finrank ℚ (affineObservableSpace star w S) ∧
      Module.finrank ℚ (affineObservableSpace star w S) ≤ complexity star.configuration S := by
  constructor
  · have h := affine_observable_dimension_budget star periods w hw S hconvex
    simpa [hR] using h
  · exact affineObservableSpace_finrank_le_complexity star w S

/-- Remark 2.6, the main theorem's actual empty-erosion branch. -/
theorem remark2_6_empty_erosion_complexity {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (hw : SpectrumPreservingEncoding star periods w)
    (S : Finset Lattice) (hS : S.Nonempty) (hconvex : LatticeConvex S)
    (hR : erosion (spectralZonotope star periods).carrier S = ∅) :
    S.card + 1 ≤ complexity star.configuration S := by
  obtain ⟨hlower, hupper⟩ :=
    remark2_6_empty_erosion_dimension_join star periods w hw S hS hconvex hR
  exact hlower.trans hupper

/-- Remark 2.6, point and segment windows expressed uniformly as windows
whose real hull has empty interior. The positive nonparallel star zonotope
cannot fit, so the main theorem follows without choosing a quadratic pair. -/
theorem remark2_6_empty_interior_complexity {p : ℕ} (star : StarData p)
    (S : Finset Lattice) (hS : S.Nonempty) (hconvex : LatticeConvex S)
    (hinterior : interior (windowHull S) = ∅) :
    S.card + 1 ≤ complexity star.configuration S := by
  let periods := chooseStarCommonPeriods star
  obtain ⟨w, hw⟩ := spectrum_preserving_integer_encoding star periods
  have hdir : Nonparallel
      ((spectralZonotope star periods).firstDirection star.two_le)
      ((spectralZonotope star periods).secondDirection star.two_le) := by
    apply star.pairwise_nonparallel
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have hZ := IntegralZonotope.interior_nonempty (spectralZonotope star periods) star.two_le hdir
  exact remark2_6_empty_erosion_complexity star periods w hw S hS hconvex
    (erosion_eq_empty_of_empty_interior hZ hinterior)

end
end ConvexNivat
