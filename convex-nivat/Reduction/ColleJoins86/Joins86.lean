import ConvexNivat.Colle.JoinMismatch
import ConvexNivat.Colle.RegionEnlarged
import ConvexNivat.Colle.DynamicsJoin
import ConvexNivat.Colle.GeneratingCycle
import ConvexNivat.Colle.GeneratingHalfPlane
import ConvexNivat.Colle.CasesRay
import ConvexNivat.Colle.Reflection
import ConvexNivat.Colle.StrongColle35
import ConvexNivat.Colle.RegionArcClaim37

namespace ConvexNivat.Colle
noncomputable section

/-- Source §3.1 assembled intermediate producer requested for source 8.6.
It produces an actual singly periodic orbit member from a double-periodic
orbit member of a nonperiodic annihilated configuration. -/
theorem periodic_not_double_orbit_from_double (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ)
    (hnotperiodic : ¬ Periodic ξ)
    (hdouble : ∃ x ∈ OrbitClosure ξ, DoublyPeriodic x) :
    ∃ x ∈ OrbitClosure ξ, Periodic x ∧ ¬ DoublyPeriodic x := by
  classical
  have hcase (η : Configuration ℤ) (B : Finset ℤ) (hB : ∀ z, η z ∈ B)
      (hannη : HasNontrivialIntegerAnnihilator η) (S : Finset Lattice)
      (hS : GeneratingSet η S) (r : ℕ) (C : AntipodalEdgeCycle S r) (i : ℤ)
      (xper : Configuration ℤ) (hxper : xper ∈ OrbitClosure η)
      (hxdouble : DoublyPeriodic xper)
      (hmismatch : UnboundedHalfStripMismatch η xper S (C.direction i)) :
      ∃ x ∈ OrbitClosure η, Periodic x ∧ ¬ DoublyPeriodic x := by
    have hmult (x : Configuration ℤ) (hx : DoublyPeriodic x) (v : Lattice) :
        ∃ k : ℤ, k ≠ 0 ∧ HasPeriod x (k • v) := by
      obtain ⟨k, hk, hp⟩ := doublyPeriodic_multiple_period x hx v
      exact ⟨k, by omega, hp⟩
    obtain ⟨J, hJlo, hJhi, P, hweak, harc, hanchor, ϑ, hϑ, n, k, hag, hbad, _⟩ :=
      colle_3_5_with_arc η B hB S hS r C i xper hxper (hmult xper hxdouble _) hmismatch
    let q := translate ((k : ℤ) • C.direction i) xper
    have hq : q ∈ OrbitClosure η := orbitClosure_translate_member η xper hxper _
    have hqdouble : DoublyPeriodic q := (doublyPeriodic_translate_iff xper _).mpr hxdouble
    have hexclude := colle_claim3_7_with_arc η B hB S hS (C.direction i) (C.direction J)
      P hweak (region_complete_arc_compatible harc) ϑ q hϑ hq (hmult q hqdouble _) n hag hbad
    obtain ⟨Q, hQ⟩ := region_enlargement_region P n
    have hQnonempty : Q.lattice.Nonempty := by
      refine ⟨Q.firstAnchor, ?_⟩
      have hb : embed Q.firstAnchor ∈ frontier Q.carrier := by
        rw [Q.boundary_eq]
        exact Or.inl (Or.inl ⟨0, le_rfl, by simp [Region.firstAnchor]⟩)
      change embed Q.firstAnchor ∈ Q.carrier
      simpa only [Q.closed.closure_eq] using frontier_subset_closure hb
    obtain ⟨b, hb, hpb⟩ := hmult q hqdouble (C.direction J)
    have hdir : DirectionalPeriod ϑ Q.lattice (C.direction J) := by
      refine ⟨hQnonempty, b, hb, ?_⟩
      intro z hz hz'
      rw [hQ] at hz hz'
      rw [hag _ hz', hag _ hz]
      exact hpb z
    have hBϑ := orbitClosure_alphabet η ϑ B hB hϑ
    obtain ⟨x, hx, hlim⟩ := ray_translate_accumulation ϑ B hBϑ (C.direction J)
    have hxη := orbitClosure_transitive η ϑ hϑ hx
    have hBx := orbitClosure_alphabet η x B hB hxη
    have hhalf := regional_ray_limit_halfplane ϑ x (C.direction i) (C.direction J) Q hdir hlim
    have hannx := orbitClosure_nontrivial_annihilator η x hxη hannη
    obtain ⟨a, ha, hpa⟩ := colle_2_14 x B hBx hannx (C.direction J) (C.primitive J)
      (det (C.direction J) Q.secondAnchor) hhalf
    refine ⟨x, hxη, ⟨a • C.direction J, ?_, hpa⟩, hexclude x hlim⟩
    exact smul_ne_zero ha (primitive_ne_zero _ (C.primitive J))
  obtain ⟨m, hm, D, hminimal, hpairwise⟩ :=
    annihilator_minimal_decomposition ξ A hA hann hnotperiodic
  obtain ⟨C⟩ := differenceFactors_edge_cycle m hm D.period D.period_nonzero hpairwise
  have hφ : differenceFactors m D.period ≠ 0 := by
    unfold differenceFactors
    simp only [ne_eq, AddMonoidAlgebra.coeff_eq_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _ hz
    have heq := sub_eq_zero.mp hz
    have hc := congrArg (fun a : AddMonoidAlgebra ℤ Lattice => a.coeff (D.period j)) heq
    simp [D.period_nonzero j] at hc
  have hS := colle_2_7 ξ (differenceFactors m D.period) hφ
    (decomposition_differenceFactors_annihilate ξ m D)
  obtain ⟨xper, hxper, hxdouble⟩ := hdouble
  rcases double_member_unbounded_mismatch ξ A hA hnotperiodic m D hminimal C 0 xper hxper hxdouble
    with hplus | hminus
  · exact hcase ξ A hA hann _ hS m C 0 xper hxper hxdouble hplus
  · obtain ⟨C', hC'⟩ := reflection_edge_cycle _ m C
    have hmismatch := opposite_mismatch_reflection ξ xper _ (C.direction 0) hminus
    have hdir : C'.direction 0 = -reflect (C.direction 0) := by simpa using hC' 0
    rw [← hdir] at hmismatch
    obtain ⟨x, hx, hper, hnotdouble⟩ := hcase (reflectedConfiguration ξ) A
      (fun z => hA (reflect z)) (reflection_annihilator ξ hann) _
      (reflection_generating ξ _ hS) m C' 0 (reflectedConfiguration xper)
      ((reflection_orbitClosure ξ xper).mp hxper) ((reflection_doublyPeriodic xper).mpr hxdouble)
      hmismatch
    refine ⟨reflectedConfiguration x, ?_, (reflection_periodic x).mpr hper, ?_⟩
    · have ht := (reflection_orbitClosure (reflectedConfiguration ξ) x).mp hx
      simpa [reflectedConfiguration, reflect] using ht
    · intro hd
      exact hnotdouble ((reflection_doublyPeriodic x).mp hd)


/-- Published Theorem 1.9/source 8.6 joined from the independent compactness,
paired-member, generating-polygon and singly-periodic-member obligations. -/
theorem colle_theorem1_9 (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ)
    (hnoPair : ∀ n : RealPlane, n ≠ 0 →
      ¬ OneSidedNonexpansive ξ n ∨ ¬ OneSidedNonexpansive ξ (-n)) :
    DoublyPeriodic ξ := by
  classical
  by_contra hnotdouble
  have hnotperiodic : ¬ Periodic ξ := by
    intro hp
    obtain ⟨n, hplus, hminus⟩ := periodic_not_double_opposite_pair ξ A hA hp hnotdouble
    exact (hnoPair n hplus.1).elim (fun h => h hplus) (fun h => h hminus)
  obtain ⟨xper, hxper, hdouble⟩ := no_opposite_pair_double_orbit_member ξ A hA hann hnoPair
  obtain ⟨x, hx, hperiod, hnotdoublex⟩ := periodic_not_double_orbit_from_double ξ A hA hann
    hnotperiodic ⟨xper, hxper, hdouble⟩
  have hAx := orbitClosure_alphabet ξ x A hA hx
  obtain ⟨n, hplus, hminus⟩ := periodic_not_double_opposite_pair x A hAx hperiod hnotdoublex
  have hplus' := oneSidedNonexpansive_inheritance ξ x hx n hplus
  have hminus' := oneSidedNonexpansive_inheritance ξ x hx (-n) hminus
  exact (hnoPair n hplus'.1).elim (fun h => h hplus') (fun h => h hminus')

theorem colle_theorem1_9_opposite_pair (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ)
    (hξ : ¬ Periodic ξ) :
    ∃ n : RealPlane, OneSidedNonexpansive ξ n ∧ OneSidedNonexpansive ξ (-n) := by
  classical
  by_contra hnone
  have hnoPair : ∀ n : RealPlane, n ≠ 0 →
      ¬ OneSidedNonexpansive ξ n ∨ ¬ OneSidedNonexpansive ξ (-n) := by
    intro n _
    by_cases hplus : OneSidedNonexpansive ξ n
    · exact Or.inr (fun hminus => hnone ⟨n, hplus, hminus⟩)
    · exact Or.inl hplus
  exact hξ (ConvexNivat.doublyPeriodic_periodic ξ (colle_theorem1_9 ξ A hA hann hnoPair))

end
end ConvexNivat.Colle
