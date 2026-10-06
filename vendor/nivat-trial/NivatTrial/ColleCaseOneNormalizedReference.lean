import NivatTrial.ColleWedgeReference
import NivatTrial.ColleDecompositionHull

/-! Normalize the actual periodic reference of a periodic wedge.  Only the
first component period is enlarged; the transverse boundary direction and
the original aperiodic hull point are retained. -/

namespace NivatTrial.ColleCaseOneNormalizedReference

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.Nonexpansive NivatTrial.ExternalInputs
open NivatTrial.ColleCaseOne NivatTrial.ColleRegionalBranches
open NivatTrial.ColleWedgeReference NivatTrial.ColleDecompositionHull
open NivatTrial.ColleDecompositionTransforms NivatTrial.ColleZonotopeEnvelope
open scoped Classical
noncomputable section

theorem wedge_nsmul_first (u k : Lattice) (c : ℤ) (P : ℕ) (hP : 0 < P) :
    wedge (P•u) k c = wedge u k c := by
  have hPz : (0:ℤ) < P := by exact_mod_cast hP
  ext z
  change (0 ≤ det (P•u) z ∧ det k z ≤ c) ↔
    (0 ≤ det u z ∧ det k z ≤ c)
  rw [← natCast_zsmul,det_zsmul_left]
  constructor
  · rintro ⟨hz,hk⟩
    exact ⟨by nlinarith,hk⟩
  · rintro ⟨hz,hk⟩
    exact ⟨mul_nonneg hPz.le hz,hk⟩

theorem transverse_signed_direction_preserved
    {n : ℕ} (v w : Fin n → Lattice) (i : Fin n)
    (hother : ∀ j, j ≠ i → w j = v j)
    (k : Lattice) (hk : k ∈ signedDirections v) (hik : det (v i) k ≠ 0) :
    k ∈ signedDirections w := by
  obtain ⟨j,hj⟩ := (mem_signedDirections v k).mp hk
  have hji : j ≠ i := by
    intro he
    subst j
    rcases hj with hj | hj
    · exact hik (by rw [hj,det_self])
    · exact hik (by rw [hj,det_neg_right,det_self,neg_zero])
  apply (mem_signedDirections w k).mpr
  refine ⟨j,?_⟩
  simpa only [hother j hji] using hj

/-- The periodic wedge branch supplies an actual aperiodic field, its own
integer decomposition, and a reference in its actual language hull whose
global period equals the selected component period. -/
theorem exists_normalized_reference_of_periodic_wedge
    {M n : ℕ} (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) n) (i : Fin n)
    (hcase : HasPeriodicWedge θ E.period (E.period i)) :
    ∃ x ∈ languageHull θ, ¬IsPeriodic x ∧
      ∃ Ex : IntegerDecomposition (integerField x) n,
      ∃ p ∈ languageHull x, p ∈ languageHull θ ∧
      ∃ k ∈ signedDirections Ex.period, ∃ c : ℤ,
        0 < det (Ex.period i) k ∧ IsPeriod p (Ex.period i) ∧
        AgreeOn x p (wedge (Ex.period i) k c) := by
  obtain ⟨x,hx,hnot,k,hk,c,Q,hik,hQ,_,_,hper,_⟩ := hcase
  obtain ⟨E₀,hE₀⟩ := exists_decomposition_with_same_periods E hx
  obtain ⟨p,hpx,_,hxp,P,hP,hp⟩ := exists_periodic_reference_for_wedge
    x E₀ (E.period i) k hik c Q hQ hper
  have hp₀ : IsPeriod p (P•E₀.period i) := by simpa only [hE₀] using hp
  obtain ⟨Ex,_,hEx,hfirst,hother⟩ := exists_reference_normalized E₀ p i P hP hp₀
  have hfirst' : Ex.period i = P•E.period i := by simpa only [hE₀] using hfirst
  have hkEx : k ∈ signedDirections Ex.period := by
    apply transverse_signed_direction_preserved E.period Ex.period i _ k hk (ne_of_gt hik)
    intro j hji
    simpa only [hE₀] using hother j hji
  refine ⟨x,hx,hnot,Ex,p,hpx,languageHull_trans hx hpx,k,hkEx,c,?_,hEx,?_⟩
  · rw [hfirst',← natCast_zsmul,det_zsmul_left]
    exact mul_pos (by exact_mod_cast hP) hik
  · rw [hfirst',wedge_nsmul_first _ _ _ P hP]
    exact hxp

end
end NivatTrial.ColleCaseOneNormalizedReference
