import ConvexNivat.Colle.RegionClaim36
import ConvexNivat.Colle.RegionExhaustion

namespace ConvexNivat.Colle
noncomputable section

/-- Claim 3.6 supplies one of the actual unbounded mismatch orientations.
This pays the case split before Lemma 3.5 rather than assuming a producer. -/
theorem double_member_unbounded_mismatch (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hξ : ¬ Periodic ξ)
    (m : ℕ) (D : PeriodicDecomposition ℤ ξ m) (hminimal : MinimalPeriodicOrder ℤ ξ m)
    (C : AntipodalEdgeCycle (supportWindow (differenceFactors m D.period)) m)
    (i : ℤ) (xper : Configuration ℤ) (hxper : xper ∈ OrbitClosure ξ)
    (hdouble : DoublyPeriodic xper) :
    UnboundedHalfStripMismatch ξ xper (supportWindow (differenceFactors m D.period)) (C.direction i) ∨
      UnboundedOppositeHalfStripMismatch ξ xper (supportWindow (differenceFactors m D.period)) (C.direction i) := by
  classical
  let S := supportWindow (differenceFactors m D.period)
  let v := C.direction i
  have hrow_lower (B : Finset Lattice) (hB : B.Nonempty)
      (hrow : ∀ z ∈ supportRow B v, det v z = -1) : ∀ z ∈ B, -1 ≤ det v z := by
    obtain ⟨z₀, hz₀, hmin⟩ := B.exists_min_image (det v) hB
    have hzface : z₀ ∈ supportRow B v := by
      refine Finset.mem_filter.mpr ⟨hz₀, ?_⟩
      intro q hq
      rw [normal_height, normal_height]
      exact_mod_cast hmin q hq
    intro z hz
    rw [← hrow z₀ hzface]
    exact hmin z hz
  by_cases hplus : UnboundedHalfStripMismatch ξ xper S v
  · exact Or.inl hplus
  · apply Or.inr
    unfold UnboundedHalfStripMismatch at hplus
    push Not at hplus
    obtain ⟨F, hF, hFrow, hFmax⟩ := hplus
    intro B₀ hB₀ hrow₀
    have hUF : ∀ z ∈ B₀ ∪ F, -1 ≤ det (C.direction i) z := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact hrow_lower B₀ hB₀.1 hrow₀ z hz
      · exact hrow_lower F hF.1 hFrow z hz
    obtain ⟨B, hB, hsub, hrow⟩ := enveloped_window_exhaustion S m C i (B₀ ∪ F) hUF
    have hFB : F ⊆ B := fun z hz => hsub (Finset.mem_union_right B₀ hz)
    have hB₀B : B₀ ⊆ B := fun z hz => hsub (Finset.mem_union_left F hz)
    obtain ⟨u, hag, hbad⟩ := colle_claim3_6 ξ A hA hξ m D hminimal C i xper hxper hdouble B hB
    refine ⟨B, hB₀B, hB, hrow, u, hag, ?_⟩
    rcases hbad with hbad | hbad
    · exact False.elim (hbad (hFmax B hFB hB hrow u hag))
    · exact hbad

end
end ConvexNivat.Colle
