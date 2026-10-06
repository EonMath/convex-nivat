import ConvexNivat.Colle.Shared.Definitions

namespace ConvexNivat.Colle
noncomputable section

theorem generating_one_point (ξ x y : Configuration ℤ) (S : Finset Lattice)
    (hS : GeneratingSet ξ S) (hx : x ∈ OrbitClosure ξ) (hy : y ∈ OrbitClosure ξ)
    (U : Set Lattice) (u z : Lattice) (hz : WindowVertex S z)
    (hearlier : ∀ q ∈ S.erase z, u + q ∈ U) (hagrees : AgreesOn x y U) :
    AgreesOn x y (U ∪ {u + z}) := by
  intro p hp
  rcases hp with hp | hp
  · exact hagrees p hp
  · obtain rfl := Set.mem_singleton_iff.mp hp
    have hletter := hS.2.2 z hz x hx y hy u (by
      intro q hq
      simpa only [add_comm] using hagrees (u + q) (hearlier q hq))
    simpa only [add_comm] using hletter

theorem generating_one_point_and_finite_sweep (ξ x y : Configuration ℤ)
    (S : Finset Lattice) (hS : GeneratingSet ξ S)
    (hx : x ∈ OrbitClosure ξ) (hy : y ∈ OrbitClosure ξ)
    (U : Set Lattice) (steps : List (Lattice × Lattice))
    (hvalid : ValidGeneratingSweep S U steps) (hagrees : AgreesOn x y U) :
    AgreesOn x y (sweepDomain U steps) := by
  revert hagrees
  induction hvalid with
  | nil U =>
      intro hagrees
      exact hagrees
  | cons U u z steps hvertex hearlier hrest ih =>
      intro hagrees
      exact ih (generating_one_point ξ x y S hS hx hy U u z hvertex hearlier hagrees)

theorem first_failing_agreement_and_period_rows (U : ℕ → Set Lattice)
    (hmono : Monotone U) (x y : Configuration ℤ)
    (hzero : AgreesOn x y (U 0)) (hfailure : ¬ AgreesOn x y (⋃ n, U n)) :
    ∃ n : ℕ, AgreesOn x y (U n) ∧ ¬ AgreesOn x y (U (n + 1)) := by
  classical
  have hex : ∃ n, ¬ AgreesOn x y (U n) := by
    by_contra hn
    push_neg at hn
    apply hfailure
    intro z hz
    obtain ⟨n, hnz⟩ := Set.mem_iUnion.mp hz
    exact hn n z hnz
  let k := Nat.find hex
  have hk : ¬ AgreesOn x y (U k) := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hn
    have heq : k = 0 := by omega
    exact hk (heq ▸ hzero)
  refine ⟨k - 1, ?_, ?_⟩
  · exact of_not_not (Nat.find_min hex (show k - 1 < k by omega))
  · have heq : k - 1 + 1 = k := by omega
    simpa only [heq] using hk

theorem first_failing_fixed_period_rows (U : ℕ → Set Lattice)
    (hmono : Monotone U) (x : Configuration ℤ) (h : Lattice) (hne : h ≠ 0)
    (hzero : OverlapHasPeriod x (U 0) h)
    (hfailure : ¬ OverlapHasPeriod x (⋃ n, U n) h) :
    ∃ n : ℕ, OverlapHasPeriod x (U n) h ∧ ¬ OverlapHasPeriod x (U (n + 1)) h := by
  classical
  have hex : ∃ n, ¬ OverlapHasPeriod x (U n) h := by
    by_contra hn
    push_neg at hn
    apply hfailure
    intro z hz hzh
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hzh
    exact hn (max i j) z (hmono (le_max_left i j) hi)
      (hmono (le_max_right i j) hj)
  let k := Nat.find hex
  have hk : ¬ OverlapHasPeriod x (U k) h := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hn
    have heq : k = 0 := by omega
    exact hk (heq ▸ hzero)
  refine ⟨k - 1, ?_, ?_⟩
  · exact of_not_not (Nat.find_min hex (show k - 1 < k by omega))
  · have heq : k - 1 + 1 = k := by omega
    simpa only [heq] using hk

end
end ConvexNivat.Colle
