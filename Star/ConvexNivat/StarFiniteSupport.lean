import ConvexNivat.StarPeriods
import ConvexNivat.OperatorDifferences

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

theorem starDifference_ne_zero {p : ℕ} (d : StarData p) (P : StarPeriodData d) :
    starDifference P ≠ 0 := by
  exact differenceProduct_ne_zero Finset.univ P.vector
    (fun i _ => StarPeriodData.vector_ne_zero d P i)

theorem starDifference_kills_constant {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (c : ℂ) :
    applyLaurent (starDifference P) (fun _ => c) = 0 := by
  have hi : Nonempty (Fin d.m) := ⟨⟨0, by have := d.two_le; omega⟩⟩
  exact differenceProduct_kills_constant Finset.univ Finset.univ_nonempty P.vector c

/-- The geometric boundedness step in the last paragraph of Lemma 1.1. -/
theorem nonparallel_strip_intersection_finite (u v : Lattice) (huv : Nonparallel u v)
    (a b c e : ℤ) :
    {z : Lattice | (a ≤ height u z ∧ height u z ≤ b) ∧
      (c ≤ height v z ∧ height v z ≤ e)}.Finite := by
  apply Set.Finite.of_injOn (f := fun z : Lattice => (height u z, height v z))
    (t := Set.Icc a b ×ˢ Set.Icc c e)
  · intro z hz
    exact hz
  · intro x _ y _ hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    dsimp [height, det] at h1 h2
    have hx : det u v * (x.1 - y.1) = 0 := by
      dsimp [det]
      linear_combination v.1 * h1 - u.1 * h2
    have hy : det u v * (x.2 - y.2) = 0 := by
      dsimp [det]
      linear_combination v.2 * h1 - u.2 * h2
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left huv))
      (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left huv))
  · exact (Set.finite_Icc a b).prod (Set.finite_Icc c e)

private theorem localSampling_height_bounds {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (W : Finset Lattice) (i : Fin d.m)
    (s : Lattice) (hs : s ∈ localSamplingSet P W) :
    -(localSamplingRadius d P W i : ℤ) ≤ height (d.component i).direction s ∧
      height (d.component i).direction s ≤ (localSamplingRadius d P W i : ℤ) := by
  have hn : (height (d.component i).direction s).natAbs ≤ localSamplingRadius d P W i :=
    Finset.le_sup (f := fun s => (height (d.component i).direction s).natAbs) hs
  have hi : ((height (d.component i).direction s).natAbs : ℤ) ≤
      (localSamplingRadius d P W i : ℤ) := by exact_mod_cast hn
  have hhi : height (d.component i).direction s ≤
      ((height (d.component i).direction s).natAbs : ℤ) := Int.le_natAbs
  have hlo : -height (d.component i).direction s ≤
      ((height (d.component i).direction s).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using
      (Int.le_natAbs (a := -height (d.component i).direction s))
  constructor <;> omega

/-- Away from a widened strip, a component agrees with one fixed pure tail
throughout every sampled point. The tail is preserved by each chosen vector. -/
private theorem inactive_component_pair {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (W : Finset Lattice) (i j : Fin d.m) (z s t : Lattice)
    (hj : z ∉ localWidenedStrip d P W j)
    (hs : s ∈ localSamplingSet P W) (ht : t ∈ localSamplingSet P W)
    (hst : z + t = (z + s) + P.vector i) :
    (d.component j).field (z + t) = (d.component j).field (z + s) := by
  have hsB := localSampling_height_bounds d P W j s hs
  have htB := localSampling_height_bounds d P W j t ht
  have hp := P.all_tail_periods i j
  change HasPeriod (d.component j).leftTail (P.vector i) ∧
    HasPeriod (d.component j).rightTail (P.vector i) at hp
  change ¬ ((d.component j).lower - (localSamplingRadius d P W j : ℤ) ≤
    height (d.component j).direction z ∧
    height (d.component j).direction z ≤
      (d.component j).upper + (localSamplingRadius d P W j : ℤ)) at hj
  by_cases hl : height (d.component j).direction z <
      (d.component j).lower - (localSamplingRadius d P W j : ℤ)
  · have hsL : height (d.component j).direction (z + s) < (d.component j).lower := by
      rw [height_add]
      omega
    have htL : height (d.component j).direction (z + t) < (d.component j).lower := by
      rw [height_add]
      omega
    rw [(d.component j).left_agreement (z + t) htL,
      (d.component j).left_agreement (z + s) hsL, hst]
    exact hp.1 (z + s)
  · have hsR : (d.component j).upper < height (d.component j).direction (z + s) := by
      rw [height_add]
      omega
    have htR : (d.component j).upper < height (d.component j).direction (z + t) := by
      rw [height_add]
      omega
    rw [(d.component j).right_agreement (z + t) htR,
      (d.component j).right_agreement (z + s) hsR, hst]
    exact hp.2 (z + s)

/-- Formal subset labels are retained even when their exponent sums coincide. -/
private theorem paired_local_patterns {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (W : Finset Lattice) (z : Lattice) (i : Fin d.m)
    (hi : ∀ j : Fin d.m, j ≠ i → z ∉ localWidenedStrip d P W j)
    (C : Finset (Fin d.m)) (hC : C ∈ (Finset.univ.erase i).powerset) :
    pattern d.configuration W ((z + formalExponent P.vector C) + P.vector i) =
      pattern d.configuration W (z + formalExponent P.vector C) := by
  classical
  have hCs := Finset.mem_powerset.mp hC
  have hni : i ∉ C := fun h => (Finset.mem_erase.mp (hCs h)).1 rfl
  have hE : formalExponent P.vector C ∈ formalExponentSet Finset.univ P.vector := by
    apply Finset.mem_image.mpr
    exact ⟨C, Finset.mem_powerset.mpr (fun j _ => Finset.mem_univ j), rfl⟩
  have hEi : formalExponent P.vector C + P.vector i ∈
      formalExponentSet Finset.univ P.vector := by
    apply Finset.mem_image.mpr
    refine ⟨insert i C, Finset.mem_powerset.mpr (fun j _ => Finset.mem_univ j), ?_⟩
    simp [formalExponent, hni, add_comm]
  funext y
  change (∑ j, (d.component j).field (((z + formalExponent P.vector C) + P.vector i) + y.val)) =
    ∑ j, (d.component j).field ((z + formalExponent P.vector C) + y.val)
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simpa only [StarPeriodData.vector, add_assoc, add_left_comm, add_comm] using
      P.component_period i ((z + formalExponent P.vector C) + y.val)
  · have hs : formalExponent P.vector C + y.val ∈ localSamplingSet P W :=
      Finset.add_mem_add hE y.property
    have ht : (formalExponent P.vector C + P.vector i) + y.val ∈ localSamplingSet P W :=
      Finset.add_mem_add hEi y.property
    have hst : z + ((formalExponent P.vector C + P.vector i) + y.val) =
        (z + (formalExponent P.vector C + y.val)) + P.vector i := by abel
    have h := inactive_component_pair d P W i j z _ _ (hi j hji) hs ht hst
    simpa only [add_assoc] using h

/-- The source's precise support bound, including the empty-window case. -/
theorem lemma_1_1_support_bound {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (W : Finset Lattice) (φ : Pattern (ZMod p) W → ℂ) :
    Function.support (applyLaurent (starDifference P) (starLocalFunction d W φ)) ⊆
      {z | ∃ i j : Fin d.m, i ≠ j ∧
        z ∈ localWidenedStrip d P W i ∧ z ∈ localWidenedStrip d P W j} := by
  classical
  intro z hz
  by_contra hbad
  have hi : ∃ i : Fin d.m, ∀ j : Fin d.m, j ≠ i →
      z ∉ localWidenedStrip d P W j := by
    by_cases ha : ∃ i : Fin d.m, z ∈ localWidenedStrip d P W i
    · obtain ⟨i, hi⟩ := ha
      refine ⟨i, fun j hji hj => ?_⟩
      exact hbad ⟨j, i, hji, hj, hi⟩
    · refine ⟨⟨0, by have := d.two_le; omega⟩, ?_⟩
      intro j _ hj
      exact ha ⟨j, hj⟩
  obtain ⟨i, hi⟩ := hi
  have hzero : applyLaurent (starDifference P) (starLocalFunction d W φ) z = 0 := by
    rw [starDifference, differenceProduct_split Finset.univ P.vector i (Finset.mem_univ i),
      mul_comm, applyLaurent_mul, otherDifferenceProduct_expansion]
    apply Finset.sum_eq_zero
    intro C hC
    have hpat := paired_local_patterns d P W z i hi C hC
    simp only [apply_difference, starLocalFunction, hpat, sub_self, mul_zero]
  exact hz hzero

/-- Lemma 1.1: differencing any actual finite-window function has finite support. -/
theorem lemma_1_1 {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (W : Finset Lattice) (φ : Pattern (ZMod p) W → ℂ) :
    ScalarHasFiniteSupport
      (applyLaurent (starDifference P) (starLocalFunction d W φ)) := by
  have hf : {z : Lattice | ∃ i j : Fin d.m, i ≠ j ∧
      z ∈ localWidenedStrip d P W i ∧ z ∈ localWidenedStrip d P W j}.Finite := by
    have hpair : ∀ i j : Fin d.m, {z : Lattice | i ≠ j ∧
        z ∈ localWidenedStrip d P W i ∧ z ∈ localWidenedStrip d P W j}.Finite := by
      intro i j
      by_cases hij : i = j
      · simp [hij]
      · exact (nonparallel_strip_intersection_finite _ _
          (d.pairwise_nonparallel i j hij) _ _ _ _).subset (fun z hz => hz.2)
    simpa only [Set.ofPred_exists] using
      Set.finite_iUnion (fun i => Set.finite_iUnion (hpair i))
  exact hf.subset (lemma_1_1_support_bound d P W φ)

end

end ConvexNivat
