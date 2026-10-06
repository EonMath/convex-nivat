import ConvexNivat.Colle.ExternalDynamicsFoundation
import ConvexNivat.Colle.ExternalDynamicsPeriodic
import ConvexNivat.Colle.GeneratingAlgebra
import ConvexNivat.Colle.GeneratingTransverse
import ConvexNivat.ExternalDynamicsHelpers.KariMoutot

namespace ConvexNivat.Colle
open ConvexNivat.ExternalDynamicsHelpers

theorem kariMoutot_primary_proposition13 (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ)
    (u : Lattice) (hu : u ≠ 0)
    (hone : StrictDeterministic ξ u) (hopposite : ¬ StrictDeterministic ξ (-u)) :
    ∃ x ∈ OrbitClosure ξ, StrictDeterministic x u ∧ StrictDeterministic x (-u) := by
  classical
  have hn : OneSidedNonexpansive ξ (embed u) := by
    have h := strict_determinism_iff_closed_expansive ξ (-u) (neg_ne_zero.mpr hu)
    have he : -embed (-u) = embed u := by ext <;> simp [embed]
    rw [he] at h
    exact not_not.mp (fun hnot => hopposite (h.mpr hnot))
  have hnonperiodic : ¬ Periodic ξ := by
    intro hp
    have hline := oneSidedNonexpansive_implies_band ξ (embed u) hn
    have hpair := (periodic_nonexpansive_iff_opposite_pair ξ A hA hp (embed u)).mp hline
    exact ((strict_determinism_iff_closed_expansive ξ u hu).mp hone) hpair.2
  obtain ⟨m, hm, D, hminimal, hpair⟩ := annihilator_minimal_decomposition ξ A hA hann hnonperiodic
  have hprod := decomposition_differenceFactors_annihilate ξ m D
  obtain ⟨i₀, hi₀⟩ := colle_2_8_nonexpansive ξ A hA m D.period D.period_nonzero hpair hprod (embed u) hn
  have hperp : latticeDot u (D.period i₀) = 0 := by
    rw [← latticeDot_cast] at hi₀
    have h : latticeDot (D.period i₀) u = 0 := by exact_mod_cast hi₀
    simpa [latticeDot, mul_comm] using h
  have htransverse : ∀ i, i ≠ i₀ → latticeDot u (D.period i) ≠ 0 := by
    intro i hi hz
    apply hpair hi
    have hfirst : u.1 * det (D.period i) (D.period i₀) = 0 := by
      have he : u.1 * det (D.period i) (D.period i₀) =
          (D.period i₀).2 * latticeDot u (D.period i) -
            (D.period i).2 * latticeDot u (D.period i₀) := by
        simp [det, latticeDot]; ring
      rw [he, hperp, hz]; ring
    have hsecond : u.2 * det (D.period i) (D.period i₀) = 0 := by
      have he : u.2 * det (D.period i) (D.period i₀) =
          (D.period i).1 * latticeDot u (D.period i₀) -
            (D.period i₀).1 * latticeDot u (D.period i) := by
        simp [det, latticeDot]; ring
      rw [he, hperp, hz]; ring
    by_cases hu1 : u.1 = 0
    · exact (mul_eq_zero.mp hsecond).resolve_left (fun hu2 => hu (Prod.ext hu1 hu2))
    · exact (mul_eq_zero.mp hfirst).resolve_left hu1
  let lower := (latticeDot (quarterTurn u) (D.period i₀)).natAbs
  obtain ⟨k, hk, B, hB, hcode⟩ := strict_determinism_finite_box ξ A hA u hu hone lower
  have hk' : |latticeDot (quarterTurn u) (D.period i₀)| < (k : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hk
  obtain ⟨n, hnpos, c, hc, hinj, himage, hmax⟩ := maximal_factor_fibre_tuple ξ A hA
    u (D.period i₀) hu (D.period_nonzero i₀) hperp k hk' B hB hcode
  obtain ⟨s, hs, d, hd, hlim⟩ := finite_tuple_joint_subsequence ξ A hA n
    (fun j i => translate (-((j : ℤ) • u)) (c i))
    (fun j i => orbitClosure_translate_member ξ (c i) (hc i) _)
  obtain ⟨hdimage, hdsep⟩ := kariMoutot_lemma11 ξ u (D.period i₀) hu (D.period_nonzero i₀)
    hperp k hk' B hB hcode n c d hc hinj himage s hs hlim
  let j₀ : Fin n := ⟨0, hnpos⟩
  refine ⟨d j₀, hd j₀, ?_, ?_⟩
  · intro x hx y hy hag
    exact hone x (orbitClosure_transitive ξ (d j₀) (hd j₀) hx)
      y (orbitClosure_transitive ξ (d j₀) (hd j₀) hy) hag
  · exact kariMoutot_lemma12 ξ A hA m D.period i₀ hprod u hu hperp htransverse
      n d j₀ hd hdimage B hdsep
      (fun b => (factor_fibre_finite_bound ξ A hA u (D.period i₀) hu
        (D.period_nonzero i₀) hperp k hk' B hB hcode b).1) hmax

theorem kariMoutot_primary_theorem3 (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ) :
    ∃ x ∈ OrbitClosure ξ, ∀ u : Lattice, u ≠ 0 →
      (StrictDeterministic x u ↔ StrictDeterministic x (-u)) := by
  classical
  obtain ⟨x, hx, hrec⟩ := uniformly_recurrent_orbit_member ξ A hA
  have hAx := orbitClosure_alphabet ξ x A hA hx
  have hannx := orbitClosure_nontrivial_annihilator ξ x hx hann
  have hforward : ∀ u : Lattice, u ≠ 0 → StrictDeterministic x u →
      StrictDeterministic x (-u) := by
    intro u hu hone
    by_contra hopposite
    obtain ⟨y, hy, _, hneg⟩ :=
      kariMoutot_primary_proposition13 x A hAx hannx u hu hone hopposite
    apply hopposite
    unfold StrictDeterministic at hneg ⊢
    simpa only [hrec y hy] using hneg
  refine ⟨x, hx, fun u hu => ⟨hforward u hu, ?_⟩⟩
  simpa only [neg_neg] using hforward (-u) (neg_ne_zero.mpr hu)

end ConvexNivat.Colle
