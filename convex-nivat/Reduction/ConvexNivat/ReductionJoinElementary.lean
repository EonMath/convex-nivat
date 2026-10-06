import ConvexNivat.ReductionAlgebra

namespace ConvexNivat
open scoped BigOperators

theorem integer_orbitClosure_range (ξ η : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hη : η ∈ OrbitClosure ξ) : ∀ z, η z ∈ A := by
  intro z
  obtain ⟨u, hu⟩ := hη {z}
  rw [hu z (Finset.mem_singleton_self z)]
  exact hA (u + z)

theorem finiteRange_patternSet_finite (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (S : Finset Lattice) : (patternSet ξ S).Finite := by
  classical
  let ξA : Configuration A := fun z => ⟨ξ z, hA z⟩
  let decode : Pattern A S → Pattern ℤ S := fun q z => (q z).val
  have heq : patternSet ξ S = decode '' patternSet ξA S := by
    ext q
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨pattern ξA S u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  rw [heq]
  exact (patternSet_finite ξA S).image decode

theorem lowConvexComplexity_integer_orbitClosure (ξ η : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (hη : η ∈ OrbitClosure ξ)
    (hlow : LowConvexComplexity ξ) : LowConvexComplexity η := by
  obtain ⟨S, hS, hc, hl⟩ := hlow
  refine ⟨S, hS, hc, le_trans ?_ hl⟩
  exact Set.ncard_le_ncard (orbitClosure_patternSet_subset ξ η hη S)
    (finiteRange_patternSet_finite ξ A hA S)

theorem modPrime_alphabet_injective (p : ℕ) (A : Finset ℤ)
    (hpositive : ∀ a ∈ A, 0 < a) (hlarge : ∀ a ∈ A, a < (p : ℤ)) :
    ∀ a ∈ A, ∀ b ∈ A, (a : ZMod p) = (b : ZMod p) → a = b := by
  intro a ha b hb hab
  have heq := (ZMod.intCast_eq_intCast_iff' a b p).mp hab
  simpa only [Int.emod_eq_of_lt (le_of_lt (hpositive a ha)) (hlarge a ha),
    Int.emod_eq_of_lt (le_of_lt (hpositive b hb)) (hlarge b hb)] using heq

theorem modPrime_periodic_iff_on_alphabet (p : ℕ) (η : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, η z ∈ A)
    (hinjective : ∀ a ∈ A, ∀ b ∈ A, (a : ZMod p) = (b : ZMod p) → a = b) :
    Periodic (fun z => (η z : ZMod p)) ↔ Periodic η := by
  constructor
  · rintro ⟨h, hh, hperiod⟩
    exact ⟨h, hh, fun z => hinjective _ (hA _) _ (hA _) (hperiod z)⟩
  · rintro ⟨h, hh, hperiod⟩
    exact ⟨h, hh, modPrime_preserves_period p η h hperiod⟩

theorem modPrime_complexity_eq_on_alphabet (p : ℕ) (η : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, η z ∈ A)
    (hinjective : ∀ a ∈ A, ∀ b ∈ A, (a : ZMod p) = (b : ZMod p) → a = b)
    (S : Finset Lattice) : complexity (fun z => (η z : ZMod p)) S = complexity η S := by
  classical
  let ηA : Configuration A := fun z => ⟨η z, hA z⟩
  let enc : A → ZMod p := fun a => (a.val : ZMod p)
  have henc : Function.Injective enc := by
    intro a b h
    apply Subtype.ext
    exact hinjective _ a.property _ b.property h
  calc
    complexity (fun z => (η z : ZMod p)) S = complexity ηA S :=
      complexity_injective_encoding ηA enc henc S
    _ = complexity η S := (complexity_injective_encoding ηA Subtype.val
      Subtype.val_injective S).symm

theorem orbitClosure_preserves_mixedDifference (ξ η : Configuration ℤ)
    (hη : η ∈ OrbitClosure ξ) (m : ℕ) (h : Fin m → Lattice)
    (hann : ∀ z, mixedDifference h Finset.univ ξ z = 0) :
    ∀ z, mixedDifference h Finset.univ η z = 0 := by
  classical
  intro z
  obtain ⟨u, hu⟩ := hη ((Finset.univ.powerset).image (fun C => z + ∑ j ∈ C, h j))
  calc
    mixedDifference h Finset.univ η z = mixedDifference h Finset.univ ξ (u + z) := by
      unfold mixedDifference
      apply Finset.sum_congr rfl
      intro C hC
      rw [hu _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)]
      simp only [add_assoc]
    _ = 0 := hann (u + z)

theorem periodicDecomposition_at_least_two {A : Type*} [AddCommMonoid A]
    (η : Configuration A) (m : ℕ) (D : PeriodicDecomposition A η m)
    (haperiodic : ¬ Periodic η) : 2 ≤ m := by
  by_contra h
  have hm : m = 0 ∨ m = 1 := by omega
  rcases hm with rfl | rfl
  · apply haperiodic
    refine ⟨(1, 0), by norm_num, ?_⟩
    intro z
    simp only [D.sum_eq, Fin.sum_univ_zero]
  · apply haperiodic
    refine ⟨D.period 0, D.period_nonzero 0, ?_⟩
    intro z
    simpa only [D.sum_eq, Fin.sum_univ_one] using D.has_period 0 z

theorem minimalPeriodicOrder_exists_of_decomposition {A : Type*} [AddCommMonoid A]
    (η : Configuration A) (m : ℕ) (hdecomp : HasPeriodicDecomposition A η m) :
    ∃ n : ℕ, MinimalPeriodicOrder A η n := by
  classical
  have hexists : ∃ n, HasPeriodicDecomposition A η n := ⟨m, hdecomp⟩
  exact ⟨Nat.find hexists, Nat.find_spec hexists,
    fun n hn => Nat.find_min' hexists hn⟩

theorem minimalOrderCounterexample_exists_of_order (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hpositive : ∀ a ∈ A, 0 < a)
    (haperiodic : ¬ Periodic ξ) (hlow : LowConvexComplexity ξ)
    (m : ℕ) (horder : MinimalPeriodicOrder ℤ ξ m) :
    ∃ η : Configuration ℤ, ∃ n : ℕ, MinimalOrderCounterexample η n := by
  classical
  let P : ℕ → Prop := fun n => ∃ η : Configuration ℤ,
    (∃ B : Finset ℤ, (∀ a ∈ B, 0 < a) ∧ ∀ z, η z ∈ B) ∧
      ¬ Periodic η ∧ LowConvexComplexity η ∧ MinimalPeriodicOrder ℤ η n
  have hexists : ∃ n, P n := ⟨m, ξ, ⟨A, hpositive, hA⟩, haperiodic, hlow, horder⟩
  obtain ⟨η, hηA, hηaperiodic, hηlow, hηorder⟩ := Nat.find_spec hexists
  refine ⟨η, Nat.find hexists, hηA, hηaperiodic, hηlow, hηorder, ?_⟩
  intro ζ n hζA hζaperiodic hζlow hζorder
  exact Nat.find_min' hexists ⟨ζ, hζA, hζaperiodic, hζlow, hζorder⟩

private theorem md_insert {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (j : ι) (hj : j ∉ I)
    (f : Configuration A) (z : Lattice) :
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

private theorem md_kills_period {ι A : Type*} [DecidableEq ι] [Ring A]
    (H : ι → Lattice) (I : Finset ι) (j : ι) (hj : j ∈ I)
    (f : Configuration A) (hf : HasPeriod f (H j)) (z : Lattice) :
    mixedDifference H I f z = 0 := by
  rw [← Finset.insert_erase hj, md_insert H _ _ (Finset.notMem_erase _ _)]
  apply sub_eq_zero.mpr
  unfold mixedDifference
  apply Finset.sum_congr rfl
  intro C hC
  congr 1
  simpa only [add_assoc, add_left_comm, add_comm] using hf (z + ∑ j ∈ C, H j)

theorem mixedDifference_periodicDecomposition {A : Type*} [CommRing A]
    (η : Configuration A) (m : ℕ) (D : PeriodicDecomposition A η m) :
    ∀ z, mixedDifference D.period Finset.univ η z = 0 := by
  classical
  intro z
  unfold mixedDifference
  simp_rw [D.sum_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  exact md_kills_period D.period Finset.univ i (Finset.mem_univ i)
    (D.field i) (D.has_period i) z

private theorem merge_sum {A : Type*} [AddCommMonoid A] {n : ℕ}
    (f : Fin (n + 1) → A) (i : Fin (n + 1)) (k : Fin n) :
    (∑ a : Fin n, (if a = k then f (i.succAbove a) + f i else f (i.succAbove a))) =
      ∑ a, f a := by
  classical
  have heq : ∀ a : Fin n,
      (if a = k then f (i.succAbove a) + f i else f (i.succAbove a)) =
        f (i.succAbove a) + if a = k then f i else 0 := by
    intro a
    split_ifs <;> simp
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Fin.sum_univ_succAbove f i]
  exact add_comm _ _

theorem minimalPeriodicOrder_pairwise_periods {A : Type*} [AddCommMonoid A]
    (η : Configuration A) (m : ℕ) (hminimal : MinimalPeriodicOrder A η m)
    (D : PeriodicDecomposition A η m) :
    Pairwise (fun i j => Nonparallel (D.period i) (D.period j)) := by
  classical
  by_contra hpair
  dsimp [Pairwise, Nonparallel] at hpair
  push Not at hpair
  obtain ⟨i, j, hij, hparallel⟩ := hpair
  have hdet : det (D.period j) (D.period i) = 0 := by
    simp only [det] at hparallel ⊢
    nlinarith
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    obtain ⟨q, hq, _, hperiod⟩ := parallel_periodic_sum (D.field j) (D.field i)
      (D.period j) (D.period i) (D.period_nonzero j) (D.period_nonzero i)
      hdet (D.has_period j) (D.has_period i)
    have hperiod' : HasPeriod (fun z => D.field (i.succAbove k) z + D.field i z) q := by
      simpa only [hk] using hperiod
    have hshort : HasPeriodicDecomposition A η n := by
      refine ⟨{
        field := fun a z => if a = k then D.field (i.succAbove a) z + D.field i z
          else D.field (i.succAbove a) z
        period := fun a => if a = k then q else D.period (i.succAbove a)
        period_nonzero := ?_
        has_period := ?_
        sum_eq := ?_ }⟩
      · intro a
        split_ifs <;> first | exact hq | exact D.period_nonzero _
      · intro a
        by_cases ha : a = k
        · subst a
          simpa only [ite_true] using hperiod'
        · simpa only [ha, ite_false] using D.has_period (i.succAbove a)
      · intro z
        exact (D.sum_eq z).trans (merge_sum (fun a => D.field a z) i k).symm
    exact (Nat.not_succ_le_self n) (hminimal.2 n hshort)

theorem prime_above_positive_alphabet (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hpositive : ∀ a ∈ A, 0 < a) :
    ∃ p : ℕ, p.Prime ∧ (∀ a ∈ A, a < (p : ℤ)) ∧
      ∀ z, 0 ≤ ξ z ∧ ξ z < (p : ℤ) := by
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (A.sup Int.natAbs + 1)
  have hlarge : ∀ a ∈ A, a < (p : ℤ) := by
    intro a ha
    have hsmall : a.natAbs < p := lt_of_le_of_lt (Finset.le_sup ha) (by omega)
    have hle : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
    exact lt_of_le_of_lt hle (by exact_mod_cast hsmall)
  exact ⟨p, hp, hlarge, fun z => ⟨le_of_lt (hpositive _ (hA z)), hlarge _ (hA z)⟩⟩

theorem fullyPeriodicOn_modPrime (p : ℕ) (η : Configuration ℤ) (R : Set Lattice)
    (hfull : FullyPeriodicOn η R) : FullyPeriodicOn (fun z => (η z : ZMod p)) R := by
  obtain ⟨h, k, hne, hind, hforward, kforward, hperiod, kperiod⟩ := hfull
  exact ⟨h, k, hne, hind, hforward, kforward,
    fun z hz => congrArg (fun a : ℤ => (a : ZMod p)) (hperiod z hz),
    fun z hz => congrArg (fun a : ℤ => (a : ZMod p)) (kperiod z hz)⟩

end ConvexNivat
