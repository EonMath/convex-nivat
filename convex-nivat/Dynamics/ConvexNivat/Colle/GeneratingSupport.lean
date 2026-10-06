import ConvexNivat.Colle.GeneratingBand
import ConvexNivat.Colle.Orbit

namespace ConvexNivat.Colle
open scoped BigOperators

private theorem convex_window_mem (T : Finset Lattice) (z : Lattice) :
    z ∈ convexLatticeWindow T ↔ embed z ∈ windowHull T := by
  exact (lattice_windowHull_finite T).mem_toFinset

private theorem convex_window_hull (T : Finset Lattice) :
    windowHull (convexLatticeWindow T) = windowHull T := by
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨z, hz, rfl⟩
    exact (convex_window_mem T z).mp hz
  · apply convexHull_mono
    apply Set.image_mono
    intro z hz
    exact (convex_window_mem T z).mpr (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)

/-- Colle Lemma 2.7 (Szabados), using the actual reflected convex support.
The source's nonzero polynomial convention is explicit: zero has empty support
and cannot be a nonempty generating set. -/
theorem colle_2_7 (ξ : Configuration ℤ) (φ : IntegerLaurent) (hφ : φ ≠ 0)
    (hann : Annihilates φ ξ) : GeneratingSet ξ (supportWindow φ) := by
  classical
  let T := reflectedSupport φ
  let S := supportWindow φ
  have hS : windowHull S = windowHull T := convex_window_hull T
  have hmem (z : Lattice) : z ∈ S ↔ embed z ∈ windowHull T := convex_window_mem T z
  have hTsub : T ⊆ S := by
    intro z hz
    exact (hmem z).mpr (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)
  have hSne : S.Nonempty := by
    obtain ⟨u, hu⟩ := Finsupp.support_nonempty_iff.mpr hφ
    refine ⟨-u, hTsub (Finset.mem_image.mpr ⟨u, hu, rfl⟩)⟩
  have hconvex : LatticeConvex S := by
    intro z
    rw [hS]
    exact (hmem z).symm
  refine ⟨hSne, hconvex, ?_⟩
  intro z hz
  have hzT : z ∈ T := by
    by_contra hnot
    have hTsub' : T ⊆ S.erase z := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, hTsub hw⟩
      intro he
      exact hnot (he ▸ hw)
    have hHull : windowHull T ⊆ windowHull (S.erase z) := by
      apply convexHull_mono
      exact Set.image_mono (by exact_mod_cast hTsub')
    have hzerase := (hz.2 z).mp (hHull ((hmem z).mp hz.1))
    exact (Finset.mem_erase.mp hzerase).1 rfl
  obtain ⟨u, hu, hzu⟩ := Finset.mem_image.mp hzT
  have hucoeff : φ u ≠ 0 := Finsupp.mem_support_iff.mp hu
  intro x hx y hy t he
  have hxa := orbitClosure_annihilator_inheritance ξ x hx φ hann t
  have hya := orbitClosure_annihilator_inheritance ξ y hy φ hann t
  have hother : ∀ w ∈ φ.support.erase u, x (t - w) = y (t - w) := by
    intro w hw
    have hwnu := (Finset.mem_erase.mp hw).1
    have hwS : -w ∈ S := hTsub (Finset.mem_image.mpr ⟨w, (Finset.mem_erase.mp hw).2, rfl⟩)
    have hwnz : -w ≠ z := by
      intro hwz
      apply hwnu
      apply neg_injective
      exact hwz.trans hzu.symm
    simpa [sub_eq_add_neg, add_comm] using he (-w) (Finset.mem_erase.mpr ⟨hwnz, hwS⟩)
  have hrest : (∑ w ∈ φ.support.erase u, φ w * x (t - w)) =
      ∑ w ∈ φ.support.erase u, φ w * y (t - w) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [hother w hw]
  unfold Annihilates laurentAction at hxa hya
  rw [Finsupp.sum, ← Finset.sum_erase_add _ _ hu] at hxa hya
  have hmul : φ u * x (t - u) = φ u * y (t - u) := by
    rw [hrest] at hxa
    linarith
  have hletter := mul_left_cancel₀ hucoeff hmul
  simpa [← hzu, sub_eq_add_neg, add_comm] using hletter

end ConvexNivat.Colle
