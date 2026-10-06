import ConvexNivat.Colle.GeneratingOrder

namespace ConvexNivat.Colle
open scoped BigOperators
open Nivat.Algebra

private theorem source_product_action {ι : Type*} [DecidableEq ι]
    (h : ι → Lattice) (I : Finset ι) (ξ : Configuration ℤ) (z : Lattice) :
    laurentAction (∏ i ∈ I, (AddMonoidAlgebra.single (h i) (1 : ℤ) -
      AddMonoidAlgebra.single (0 : Lattice) (1 : ℤ))).coeff ξ z =
        mixedDifference h I (fun w => ξ (-w)) (-z) := by
  classical
  have he : laurentAction (∏ i ∈ I, (AddMonoidAlgebra.single (h i) (1 : ℤ) -
      AddMonoidAlgebra.single (0 : Lattice) (1 : ℤ))).coeff ξ z =
      coefficientAct (∏ i ∈ I, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1))
        (fun w => ξ (-w)) (-z) := by
    rw [coefficientAct_apply]
    unfold laurentAction
    apply Finsupp.sum_congr
    intro u hu
    simp [sub_eq_add_neg, add_comm]
  rw [he]
  simp_rw [sub_eq_add_neg]
  rw [Finset.prod_add, coefficientAct_finset_sum]
  simp only [Finset.sum_apply, mixedDifference]
  apply Finset.sum_congr rfl
  intro C hC
  have hCI : C ⊆ I := Finset.mem_powerset.mp hC
  have hprod : (∏ i ∈ C, AddMonoidAlgebra.single (h i) (1 : ℤ)) =
      AddMonoidAlgebra.single (∑ i ∈ C, h i) (1 : ℤ) := by
    simp [AddMonoidAlgebra.prod_single]
  rw [hprod, Finset.prod_const, Finset.card_sdiff_of_subset hCI]
  have hneg (n : ℕ) : (-1 : Nivat.Algebra.IntegerLaurent) ^ n =
      AddMonoidAlgebra.single 0 ((-1 : ℤ) ^ n) := by
    change (-(AddMonoidAlgebra.single 0 (1 : ℤ))) ^ n = _
    rw [← AddMonoidAlgebra.single_neg, AddMonoidAlgebra.single_pow, nsmul_zero]
  rw [hneg]
  simp [coefficientAct_single, Nivat.shift]

private theorem md_insert {ι : Type*} [DecidableEq ι]
    (H : ι → Lattice) (I : Finset ι) (j : ι) (hj : j ∉ I)
    (f : Configuration ℤ) (z : Lattice) :
    mixedDifference H (insert j I) f z =
      mixedDifference H I f (z + H j) - mixedDifference H I f z := by
  unfold mixedDifference
  rw [Finset.sum_powerset_insert hj, sub_eq_add_neg, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro C hC
    have hjC : j ∉ C := fun h => hj (Finset.mem_powerset.mp hC h)
    rw [Finset.card_insert_of_notMem hj, Finset.card_insert_of_notMem hjC,
      Nat.add_sub_add_right, Finset.sum_insert hjC]
    congr 2
    abel
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro C hC
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hC)
    rw [Finset.card_insert_of_notMem hj]
    have he : I.card + 1 - C.card = (I.card - C.card) + 1 := by omega
    rw [he, pow_succ]
    simp

private theorem md_kills_period {ι : Type*} [DecidableEq ι]
    (H : ι → Lattice) (I : Finset ι) (j : ι) (hj : j ∈ I)
    (f : Configuration ℤ) (hf : HasPeriod f (H j)) (z : Lattice) :
    mixedDifference H I f z = 0 := by
  rw [← Finset.insert_erase hj, md_insert H _ _ (Finset.notMem_erase _ _)]
  apply sub_eq_zero.mpr
  unfold mixedDifference
  apply Finset.sum_congr rfl
  intro C hC
  congr 1
  simpa only [add_assoc, add_left_comm, add_comm] using hf (z + ∑ j ∈ C, H j)

private theorem reflection_period (f : Configuration ℤ) (h : Lattice)
    (hf : HasPeriod f h) : HasPeriod (fun z => f (-z)) h := by
  intro z
  simpa only [neg_add] using (Function.Periodic.neg hf) (-z)

theorem decomposition_differenceFactors_annihilate (ξ : Configuration ℤ) (m : ℕ)
    (D : PeriodicDecomposition ℤ ξ m) : Annihilates (differenceFactors m D.period) ξ := by
  let E : PeriodicDecomposition ℤ (fun z => ξ (-z)) m :=
    { field := fun i z => D.field i (-z)
      period := D.period
      period_nonzero := D.period_nonzero
      has_period := fun i => reflection_period (D.field i) (D.period i) (D.has_period i)
      sum_eq := fun z => D.sum_eq (-z) }
  intro z
  rw [differenceFactors, source_product_action]
  exact mixedDifference_periodicDecomposition _ m E (-z)

/-- Prescribed-period orbit transport: the components are produced, not supplied
as a hypothesis on the limit. Source Theorem 1.4 and reviewed source 8.5. -/
theorem orbit_decomposition_same_periods (ξ x : Configuration ℤ) (m : ℕ)
    (D : PeriodicDecomposition ℤ ξ m)
    (hpairwise : Pairwise (fun i j => Nonparallel (D.period i) (D.period j)))
    (hx : x ∈ OrbitClosure ξ) :
    ∃ E : PeriodicDecomposition ℤ x m, E.period = D.period := by
  have hξ := mixedDifference_periodicDecomposition ξ m D
  have hxann := orbitClosure_preserves_mixedDifference ξ x hx m D.period hξ
  obtain ⟨f, hf, hs⟩ := external8_4b_decomposition_obligation m D.period
    D.period_nonzero hpairwise x hxann
  let E : PeriodicDecomposition ℤ x m :=
    { field := f
      period := D.period
      period_nonzero := D.period_nonzero
      has_period := hf
      sum_eq := hs }
  exact ⟨E, rfl⟩

/-- The factor-deletion annihilator of Claim 4.7 is derived from the original
decomposition and a common period, retaining the actual polynomial product. -/
theorem colle_claim4_7_deleted_annihilator (ξ : Configuration ℤ) (m : ℕ)
    (D : PeriodicDecomposition ℤ ξ m) (k : Fin m) (h : Lattice)
    (hh : HasPeriod (D.field k) h) :
    Annihilates (differenceWithout m D.period k) (periodDifference ξ h) := by
  classical
  let f : Fin m → Configuration ℤ := fun i z => D.field i (z - h) - D.field i z
  have hs (z : Lattice) : periodDifference ξ h z = ∑ i, f i z := by
    rw [periodDifference, D.sum_eq, D.sum_eq, Finset.sum_sub_distrib]
  have hk (z : Lattice) : f k z = 0 := by
    dsimp [f]
    have he := hh (z - h)
    simpa only [sub_add_cancel, sub_self] using congrArg (fun a => a - D.field k z) he.symm
  have hp (i : Fin m) : HasPeriod (f i) (D.period i) := by
    intro z
    dsimp [f]
    rw [show z + D.period i - h = (z - h) + D.period i by abel,
      D.has_period i, D.has_period i]
  intro z
  rw [differenceWithout, source_product_action]
  unfold mixedDifference
  simp_rw [hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hik : i = k
  · subst i
    simp only [hk, mul_zero, Finset.sum_const_zero]
  · exact md_kills_period D.period (Finset.univ.erase k) i
      (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
      (fun w => f i (-w)) (reflection_period (f i) (D.period i) (hp i)) (-z)

end ConvexNivat.Colle
