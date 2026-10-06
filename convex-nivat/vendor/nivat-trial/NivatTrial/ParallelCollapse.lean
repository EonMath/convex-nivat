import NivatTrial.IntegerPowerReduction
import NivatTrial.IntegerDecomposition

/-!
# Collapse of parallel difference factors on a finite-range integer field

Two parallel translation differences whose product annihilates a finite-range
integer field can be replaced by one difference in a nonzero common multiple
of their direction. This is the finite-range step behind direction grouping;
the field's values need not form a finite additive group.
-/

namespace NivatTrial.ParallelCollapse

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.IntegerPowerReduction
open NivatTrial.OneSidedRecurrence

open scoped Classical

noncomputable section

theorem period_of_parallel_pair (f : Lattice → ℤ)
    (hf : (Set.range f).Finite) (h k : Lattice) (hk : k ≠ 0)
    (hparallel : det k h = 0)
    (hann : increment (increment f h) k = 0) :
    ∃ M : ℕ, 0 < M ∧ IsPeriod f (M • h) := by
  have hperiod : IsPeriod (increment f h) k := by
    intro z
    have hz := congrFun hann z
    exact sub_eq_zero.mp hz
  obtain ⟨M, hM, hperiodM⟩ :=
    parallel_direction_period hperiod hk h hparallel
  have hdelta : IsPeriod (increment f (M • h)) h :=
    increment_commute_period f h (M • h) hperiodM
  have hdeltaM : IsPeriod (increment f (M • h)) (M • h) := hdelta.nsmul M
  exact ⟨M, hM, period_of_periodic_increment f (M • h) hf hdeltaM⟩

private theorem det_ne_zero_swap {h k : Lattice} (hdet : det h k ≠ 0) :
    det k h ≠ 0 := by
  rw [det_swap]
  exact neg_ne_zero.mpr hdet

private theorem nsmul_ne_zero (M : ℕ) (hM : 0 < M)
    (h : Lattice) (hh : h ≠ 0) : M • h ≠ 0 := by
  exact fun heq => hh ((nsmul_eq_zero_iff_right (Nat.ne_of_gt hM)).mp heq)

/-- Normalize any finite list of nonzero directions on a finite-range field:
the product difference relation can be replaced by one with pairwise
independent directions. No uniqueness of the resulting periods is claimed. -/
theorem independent_annihilator_of_list (hs : List Lattice)
    (hnonzero : ∀ h ∈ hs, h ≠ 0) (f : Lattice → ℤ)
    (hf : (Set.range f).Finite) (hann : iteratedIncrement hs f = 0) :
    ∃ ks : List Lattice,
      ks.Pairwise (fun h k => det h k ≠ 0) ∧
      (∀ k ∈ ks, k ≠ 0) ∧ iteratedIncrement ks f = 0 := by
  induction hs generalizing f with
  | nil => exact ⟨[], by simp, by simp, hann⟩
  | cons h hs ih =>
    have hh : h ≠ 0 := hnonzero h (List.mem_cons_self)
    have htailnonzero : ∀ k ∈ hs, k ≠ 0 := by
      intro k hk
      exact hnonzero k (List.mem_cons_of_mem _ hk)
    have htailann : iteratedIncrement hs (increment f h) = 0 := by
      rw [iteratedIncrement_commute]
      exact hann
    obtain ⟨ks, hpair, hksnz, hksann⟩ :=
      ih htailnonzero (increment f h) (finite_range_increment f hf h) htailann
    have hwhole : iteratedIncrement (h :: ks) f = 0 := by
      calc
        iteratedIncrement (h :: ks) f = increment (iteratedIncrement ks f) h := rfl
        _ = iteratedIncrement ks (increment f h) :=
          (iteratedIncrement_commute ks f h).symm
        _ = 0 := hksann
    by_cases htrans : ∀ k ∈ ks, det h k ≠ 0
    · exact ⟨h :: ks, List.pairwise_cons.mpr ⟨htrans, hpair⟩,
        by intro k hk; rcases List.mem_cons.mp hk with rfl | hk; exact hh; exact hksnz k hk,
        hwhole⟩
    · push Not at htrans
      obtain ⟨k, hk, hparallel⟩ := htrans
      obtain ⟨pre, post, hks⟩ := List.mem_iff_append.mp hk
      let rest := pre ++ post
      have hperm : (h :: ks).Perm (h :: k :: rest) := by
        rw [hks]
        exact List.perm_middle.cons h
      have hpair' : (k :: rest).Pairwise (fun a b => det a b ≠ 0) := by
        apply hpair.perm
        · rw [hks]
          exact List.perm_middle
        · intro a b hab
          exact det_ne_zero_swap hab
      obtain ⟨htransRest, hpairRest⟩ := List.pairwise_cons.mp hpair'
      have hannPair : increment (increment (iteratedIncrement rest f) k) h = 0 := by
        have he := iteratedIncrement_perm hperm f
        rw [he] at hwhole
        simpa only [iteratedIncrement_cons] using hwhole
      obtain ⟨M, hM, hperiod⟩ := period_of_parallel_pair
        (iteratedIncrement rest f) (finite_range_iterated rest f hf)
        k h hh hparallel hannPair
      have hnonzeroNew : M • k ≠ 0 :=
        nsmul_ne_zero M hM k (hksnz k hk)
      have hpairNew : (M • k :: rest).Pairwise (fun a b => det a b ≠ 0) := by
        apply List.pairwise_cons.mpr
        constructor
        · intro t ht
          rw [← natCast_zsmul, Geometry.det_zsmul_left]
          exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hM) (htransRest t ht)
        · exact hpairRest
      have hrestnonzero : ∀ t ∈ rest, t ≠ 0 := by
        intro t ht
        have hmem : t ∈ ks := by
          rw [hks]
          exact List.mem_append.mpr (List.mem_append.mp ht |>.elim
            (fun ht => Or.inl ht) (fun ht => Or.inr (List.mem_cons_of_mem _ ht)))
        exact hksnz t hmem
      refine ⟨M • k :: rest, hpairNew, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hnonzeroNew
        · exact hrestnonzero t ht
      · funext z
        have hz := hperiod z
        simpa only [iteratedIncrement_cons, increment, Pi.zero_apply]
          using sub_eq_zero.mpr hz

end

end NivatTrial.ParallelCollapse
