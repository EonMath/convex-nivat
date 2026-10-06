import ConvexNivat.Colle.Shared.SourceDeletedPolygon
import ConvexNivat.Colle.Shared.StripRows
import ConvexNivat.Colle.Shared.StripSweep
import ConvexNivat.Colle.Shared.RowPeriods
import ConvexNivat.Colle.Shared.FiniteAction
import ConvexNivat.Colle.Shared.PeriodDifference
import ConvexNivat.Colle.GeneratingAlgebra

namespace ConvexNivat.Colle
noncomputable section

private theorem difference_is_action (x : Configuration ℤ) (h : Lattice) :
    periodDifference x h = laurentAction
      (Finsupp.single h 1 - Finsupp.single 0 1) x := by
  funext z
  simp [periodDifference, laurentAction, Finsupp.sum_sub_index,
    Finsupp.sum_single_index, sub_mul]

theorem colle_claim3_6 (ξ : Configuration ℤ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hnotperiodic : ¬ Periodic ξ) (m : ℕ)
    (D : PeriodicDecomposition ℤ ξ m) (hminimal : MinimalPeriodicOrder ℤ ξ m)
    (C : AntipodalEdgeCycle (supportWindow (differenceFactors m D.period)) m)
    (i : ℤ) (xper : Configuration ℤ) (hxper : xper ∈ OrbitClosure ξ)
    (hxdouble : DoublyPeriodic xper)
    (B : Finset Lattice) (hB : EnvelopedWindow (supportWindow (differenceFactors m D.period)) B) :
    ∃ u : Lattice, AgreesOn (translate u ξ) xper (B : Set Lattice) ∧
      (¬ AgreesOn (translate u ξ) xper (halfStrip B (C.direction i)) ∨
        ¬ AgreesOn (translate u ξ) xper (halfStrip B (-C.direction i))) := by
  classical
  obtain ⟨k, hk, _⟩ := component_direction_and_deleted_polygon ξ A hA
    hnotperiodic m D hminimal C i
  rcases hk with ⟨htangent, hpoly, _, hplus, hminus, hfaceplus, hfaceminus, hfit⟩
  obtain ⟨a, ha, hcomponent, hbackground⟩ := double_common_component_period
    (C.direction i) (D.period k) (C.primitive i) (D.period_nonzero k)
    htangent (D.field k) xper (D.has_period k) hxdouble
  let h := a • C.direction i
  change HasPeriod xper h at hbackground
  have hh : h ≠ 0 := by
    exact smul_ne_zero ha (primitive_ne_zero _ (C.primitive i))
  let δ := periodDifference ξ h
  let G := supportWindow (differenceWithout m D.period k)
  have hgen : GeneratingSet δ G := colle_2_7 δ _ hpoly
    (colle_claim4_7_deleted_annihilator ξ m D k h hcomponent)
  obtain ⟨hlohi, hstrip⟩ := enveloped_two_sided_strip_row_complete C i hB
  let U := halfStrip B (C.direction i) ∪ halfStrip B (-C.direction i)
  have hdetermine := (no_parallel_edge_two_sided_strip_sweep δ G B hgen
    (C.direction i) (C.primitive i) ⟨hplus, hminus⟩ ⟨hfaceplus, hfaceminus⟩
    ⟨_, _, hlohi, hstrip⟩ (hfit B hB)).2
  let φ : IntegerLaurent := Finsupp.single h 1 - Finsupp.single 0 1
  have hzero : (fun _ => 0) ∈ OrbitClosure δ := by
    have hz : periodDifference xper h = (fun _ => 0) := by
      funext z
      exact sub_eq_zero.mpr (by simpa only [sub_add_cancel] using (hbackground (z - h)).symm)
    have hx := (finite_action_and_difference_orbit_transports φ ξ).2.2 xper hxper
    dsimp only [φ] at hx
    dsimp only [δ]
    simpa only [← difference_is_action, hz] using hx
  obtain ⟨u, hu⟩ := hxper B
  refine ⟨u, ?_, ?_⟩
  · intro z hz
    simpa [translate, add_comm] using (hu z hz).symm
  · by_contra hfailure
    simp only [not_or, not_not] at hfailure
    have hagree : AgreesOn (translate u ξ) xper U := by
      intro z hz
      rcases hz with hz | hz
      · exact hfailure.1 z hz
      · exact hfailure.2 z hz
    have hinvariant : ForwardInvariant U (-h) := by
      intro z hz
      dsimp only [U] at hz ⊢
      rw [hstrip] at hz ⊢
      have he : det (C.direction i) (z + -h) = det (C.direction i) z := by
        simp [h, det]
        ring
      simpa only [latticeStrip, Set.mem_ofPred_eq, he] using hz
    have hδagree := periodDifference_zero_on_invariant_agreement
      (translate u ξ) xper U h hinvariant hbackground hagree
    have hδtranslate : periodDifference (translate u ξ) h = translate u δ := by
      funext z
      dsimp [δ, periodDifference, translate]
      congr 1
      congr 1
      abel
    have hδorbit : periodDifference (translate u ξ) h ∈ OrbitClosure δ := by
      rw [hδtranslate]
      exact orbitClosure_translate_member δ δ (orbitClosure_self δ) u
    have hall := hdetermine _ hδorbit _ hzero hδagree
    have hp : HasPeriod (translate u ξ) h := by
      intro z
      have hz := congrFun hall (z + h)
      exact (sub_eq_zero.mp (by simpa only [periodDifference, add_sub_cancel_right]
        using hz)).symm
    exact hnotperiodic ⟨h, hh, (hasPeriod_translate_iff ξ u h).mp hp⟩

end
end ConvexNivat.Colle
