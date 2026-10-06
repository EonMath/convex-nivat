import NivatTrial.ColleOrbitCofactor
import NivatTrial.ParallelCollapse

/-!
# Minimal integer decomposition and component-direction orbit limits

This avoids a general Newton-polygon edge theorem. A doubly periodic limit
along one component period makes the complementary difference cofactor
doubly periodic. Its period in one remaining component direction allows two
parallel differences to collapse, yielding one fewer periodic summand.
-/

namespace NivatTrial.ColleMinimality

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.IncrementSupport
open NivatTrial.IntegerPowerReduction NivatTrial.IntegerDecomposition
open NivatTrial.ParallelCollapse NivatTrial.ExternalInputs
open NivatTrial.ColleOrbitCofactor
open NivatTrial.Dynamics

open scoped Classical
noncomputable section

/-- The list form of integer decomposition, retaining its exact number of
factors for minimality arguments. -/
theorem decomposition_at_list_length (ks : List Lattice)
    (hpair : ks.Pairwise (fun h k => det h k ≠ 0))
    (hnonzero : ∀ h ∈ ks, h ≠ 0) (x : Lattice → ℤ)
    (hann : iteratedIncrement ks x = 0) :
    HasIntegerDecomposition x ks.length := by
  let h : Fin ks.length → Lattice := fun i => ks[i.val]
  have hFn : List.ofFn h = ks := by
    simpa only [h] using (List.ofFn_getElem (xs := ks))
  have hnonzero' : ∀ i, h i ≠ 0 := by
    intro i
    exact hnonzero (h i) (List.getElem_mem i.isLt)
  have hpair' : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0 := by
    intro i j hij
    have hp : (List.ofFn h).Pairwise (fun a b => det a b ≠ 0) := by
      rwa [hFn]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact List.pairwise_ofFn.mp hp hlt
    · have ht := List.pairwise_ofFn.mp hp hgt
      rw [det_swap]
      exact neg_ne_zero.mpr ht
  have hindexPerm :
      (Finset.univ.toList : List (Fin ks.length)).Perm (List.finRange ks.length) :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList Finset.univ)
      (List.nodup_finRange ks.length)).mpr (by intro i; simp)
  have hfinRange : (List.finRange ks.length).map h = ks := by
    simpa [List.finRange, List.map_ofFn, Function.comp_def] using hFn
  have hperm : (Finset.univ.toList.map h).Perm ks := by
    simpa only [hfinRange] using hindexPerm.map h
  have hann' : iteratedIncrement (Finset.univ.toList.map h) x = 0 := by
    rw [iteratedIncrement_perm hperm x]
    exact hann
  obtain ⟨F, hperiod, hsum⟩ :=
    IntegerDecomposition.product_decomposition ks.length h hnonzero' hpair' x hann'
  exact ⟨⟨F, h, hnonzero', hpair', hperiod, hsum⟩⟩

/-- Colle's Lemma 4.4, in finite-window rather than topological language:
no limit of translates along a component period of a minimal integer periodic
decomposition can be doubly periodic. -/
theorem no_doublyPeriodic_direction_limit {n : ℕ} (x y : Lattice → ℤ)
    (hx : (Set.range x).Finite) (hnot : ¬IsPeriodic x)
    (D : IntegerDecomposition x n)
    (hmin : ∀ m, HasIntegerDecomposition x m → n ≤ m)
    (i : Fin n) (hy : DirectionOrbitHull x y (D.period i)) :
    ¬IsDoublyPeriodic y := by
  intro hydp
  let : DecidableEq (Fin n) := Classical.decEq _
  let R := cofactorDirections D.period i
  have hRlen : R.length = n - 1 := by
    simp [R, cofactorDirections]
  have hpairR : R.Pairwise (fun h k => det h k ≠ 0) := by
    dsimp [R, cofactorDirections]
    change ((Finset.univ.erase i).toList.map D.period).Pairwise
      (fun h k => det h k ≠ 0)
    have hpidx : ((Finset.univ.erase i).toList).Pairwise
        (fun j k => det (D.period j) (D.period k) ≠ 0) :=
      (Finset.nodup_toList _).pairwise_of_forall_ne
        (fun j _ k _ hjk => D.independent j k hjk)
    exact hpidx.map D.period (fun _ _ hp => hp)
  have hnonzeroR : ∀ h ∈ R, h ≠ 0 := by
    intro h hh
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hh
    exact D.period_ne_zero j
  have hcofactor : iteratedIncrement R x = iteratedIncrement R y :=
    cofactor_eq_of_directionOrbitHull D i hy
  have hcofactorDP : IsDoublyPeriodic (iteratedIncrement R x) := by
    rw [hcofactor]
    obtain ⟨a, b, hab, hpa, hpb⟩ := hydp
    exact ⟨a, b, hab, iteratedIncrement_period R hpa,
      iteratedIncrement_period R hpb⟩
  cases hR : R with
  | nil =>
    have hxy : x = y := by
      simpa only [hR, iteratedIncrement_nil] using hcofactor
    exact hnot (hxy ▸ hydp.isPeriodic)
  | cons h rest =>
    have hpairCons : (h :: rest).Pairwise (fun a b => det a b ≠ 0) := by
      simpa only [hR] using hpairR
    obtain ⟨htrans, hpairRest⟩ := List.pairwise_cons.mp hpairCons
    have hh : h ≠ 0 := hnonzeroR h (by rw [hR]; simp)
    have hrestNZ : ∀ k ∈ rest, k ≠ 0 := by
      intro k hk
      exact hnonzeroR k (by rw [hR]; simp [hk])
    have hgDP : IsDoublyPeriodic
        (increment (iteratedIncrement rest x) h) := by
      simpa only [hR, iteratedIncrement_cons] using hcofactorDP
    obtain ⟨q, hq, hqper⟩ :=
      direction_period_of_finite_orbit
        (increment (iteratedIncrement rest x) h) h
        (finite_orbit_of_doublyPeriodic _ hgDP)
    have hqNZ : q • h ≠ 0 :=
      fun he => hh ((nsmul_eq_zero_iff_right (Nat.ne_of_gt hq)).mp he)
    have hparallel : det (q • h) h = 0 := by
      rw [← natCast_zsmul, det_zsmul_left, det_self, mul_zero]
    have hannPair : increment (increment (iteratedIncrement rest x) h)
        (q • h) = 0 := by
      funext z
      exact sub_eq_zero.mpr (hqper z)
    obtain ⟨M, hM, hMper⟩ :=
      period_of_parallel_pair (iteratedIncrement rest x)
        (finite_range_iterated rest x hx) h (q • h) hqNZ
        hparallel hannPair
    have hMnonzero : M • h ≠ 0 :=
      fun he => hh ((nsmul_eq_zero_iff_right (Nat.ne_of_gt hM)).mp he)
    have hpairNew : (M • h :: rest).Pairwise (fun a b => det a b ≠ 0) := by
      apply List.pairwise_cons.mpr
      constructor
      · intro k hk
        rw [← natCast_zsmul, det_zsmul_left]
        exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hM) (htrans k hk)
      · exact hpairRest
    have hnonzeroNew : ∀ k ∈ M • h :: rest, k ≠ 0 := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hMnonzero
      · exact hrestNZ k hk
    have hannNew : iteratedIncrement (M • h :: rest) x = 0 := by
      rw [iteratedIncrement_cons]
      funext z
      exact sub_eq_zero.mpr (hMper z)
    have hshort : (M • h :: rest).length < n := by
      rw [hR] at hRlen
      simp only [List.length_cons] at hRlen ⊢
      omega
    have hDnew : HasIntegerDecomposition x (M • h :: rest).length :=
      decomposition_at_list_length _ hpairNew hnonzeroNew x hannNew
    exact (not_lt_of_ge (hmin _ hDnew)) hshort

/-- Colle's uniform-order hypothesis applies the integer lemma to any
nonperiodic point of the original finite-alphabet language hull, including
translates and subsequent orbit limits. -/
theorem no_doublyPeriodic_direction_limit_in_uniform_hull
    {M n : ℕ} {θ x y : Lattice → Fin M}
    (huniform : UniformOrder θ n) (hx : x ∈ languageHull θ)
    (hnotx : ¬IsPeriodic x)
    (D : IntegerDecomposition (integerField x) n)
    (i : Fin n) (hy : DirectionOrbitHull x y (D.period i)) :
    ¬IsDoublyPeriodic y := by
  have hfinite : (Set.range (integerField x)).Finite := by
    apply (Set.finite_range integerCode).subset
    rintro a ⟨z, rfl⟩
    exact ⟨x z, rfl⟩
  have hnotCode : ¬IsPeriodic (integerField x) := by
    intro hp
    exact hnotx ((isPeriodic_encode_iff (integerCode_injective M) x).mp hp)
  have hmin : ∀ m, HasIntegerDecomposition (integerField x) m → n ≤ m :=
    (huniform x hx hnotx).2
  have hcodeOrbit : DirectionOrbitHull (integerField x)
      (integerField y) (D.period i) := hy.encode integerCode
  have hnotCodeLimit := no_doublyPeriodic_direction_limit
    (integerField x) (integerField y) hfinite hnotCode D hmin i hcodeOrbit
  intro hydp
  exact hnotCodeLimit (hydp.encode integerCode)

end
end NivatTrial.ColleMinimality
