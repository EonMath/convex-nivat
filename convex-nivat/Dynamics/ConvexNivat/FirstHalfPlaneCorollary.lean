import ConvexNivat.FirstHalfPlane

namespace ConvexNivat
open scoped BigOperators

private theorem fc_two_le {A : Type*} [AddCommMonoid A]
    {θ : Configuration A} {m : ℕ} (D : PeriodicDecomposition A θ m)
    (haperiodic : ¬ Periodic θ) : 2 ≤ m := by
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

private theorem fc_merge_sum {A : Type*} [AddCommMonoid A] {n : ℕ}
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

private theorem fc_absorb {A : Type*} [AddCommMonoid A]
    (θ : Configuration A) (n : ℕ) (hn : 0 < n)
    (D : PeriodicDecomposition A θ (n + 1))
    (hpair : Pairwise (fun i j => Nonparallel (D.period i) (D.period j)))
    (i : Fin (n + 1)) (hi : DoublyPeriodic (D.field i)) :
    ∃ E : PeriodicDecomposition A θ n,
      Pairwise (fun i j => Nonparallel (E.period i) (E.period j)) := by
  classical
  obtain ⟨N, hN, hNP⟩ := (doublyPeriodic_iff_grid (D.field i)).mp hi
  let k : Fin n := ⟨0, hn⟩
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  let E : PeriodicDecomposition A θ n := {
    field := fun a z => if a = k then D.field (i.succAbove a) z + D.field i z
      else D.field (i.succAbove a) z
    period := fun a => (if a = k then (N : ℤ) else 1) • D.period (i.succAbove a)
    period_nonzero := by
      intro a
      apply smul_ne_zero
      · split_ifs <;> simp_all
      · exact D.period_nonzero _
    has_period := by
      intro a
      by_cases hak : a = k
      · simp only [hak, ite_true]
        exact hasPeriod_add_fields _ _ _ (hasPeriod_zsmul _ _ (D.has_period _) N) (hNP _)
      · simp only [hak, ite_false, one_smul]
        exact D.has_period _
    sum_eq := by
      intro z
      exact (D.sum_eq z).trans (fc_merge_sum (fun a => D.field a z) i k).symm }
  refine ⟨E, ?_⟩
  intro a b hab
  have hsc : ∀ c : Fin n, (if c = k then (N : ℤ) else 1) ≠ 0 := by
    intro c
    split_ifs
    · exact hNz
    · norm_num
  have hiab : i.succAbove a ≠ i.succAbove b := fun h => hab (Fin.succAbove_right_injective h)
  change det ((if a = k then (N : ℤ) else 1) • D.period (i.succAbove a))
    ((if b = k then (N : ℤ) else 1) • D.period (i.succAbove b)) ≠ 0
  have heq : det ((if a = k then (N : ℤ) else 1) • D.period (i.succAbove a))
      ((if b = k then (N : ℤ) else 1) • D.period (i.succAbove b)) =
      (if a = k then (N : ℤ) else 1) * (if b = k then (N : ℤ) else 1) *
        det (D.period (i.succAbove a)) (D.period (i.succAbove b)) := by
    split_ifs <;> simp [det] <;> ring
  rw [heq]
  exact mul_ne_zero (mul_ne_zero (hsc a) (hsc b)) (hpair hiab)

private theorem fc_remove_double {A : Type*} [AddCommMonoid A]
    (θ : Configuration A) (haperiodic : ¬ Periodic θ) (m : ℕ)
    (D : PeriodicDecomposition A θ m)
    (hpair : Pairwise (fun i j => Nonparallel (D.period i) (D.period j))) :
    ∃ n : ℕ, ∃ E : PeriodicDecomposition A θ n,
      Pairwise (fun i j => Nonparallel (E.period i) (E.period j)) ∧
      (∀ i, ¬ DoublyPeriodic (E.field i)) := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hd : ∀ i, ¬ DoublyPeriodic (D.field i)
    · exact ⟨m, D, hpair, hd⟩
    push Not at hd
    obtain ⟨i, hi⟩ := hd
    have hm : 2 ≤ m := fc_two_le D haperiodic
    cases m with
    | zero => omega
    | succ n =>
      obtain ⟨E, hE⟩ := fc_absorb θ n (by omega) D hpair i hi
      exact ih n (Nat.lt_succ_self n) E hE

private theorem fc_primitive_factor (h : Lattice) (hh : h ≠ 0) :
    ∃ v : Lattice, Primitive v ∧ ∃ k : ℕ, 0 < k ∧ h = (k : ℤ) • v := by
  have hg : 0 < Int.gcd h.1 h.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp hz
    exact hh (Prod.ext hx hy)
  obtain ⟨x, y, hxy, hx, hy⟩ := Int.exists_gcd_one hg
  refine ⟨(x, y), hxy, Int.gcd h.1 h.2, hg, ?_⟩
  exact Prod.ext (hx.trans (mul_comm _ _)) (hy.trans (mul_comm _ _))

theorem corollary8_10 (p : ℕ) (hp : p.Prime) (θ : Configuration (ZMod p))
    (haperiodic : ¬ Periodic θ) (m : ℕ) (d : PeriodicDecomposition (ZMod p) θ m)
    (hpairwise : Pairwise (fun i j => Nonparallel (d.period i) (d.period j)))
    (R : Set Lattice) (hR : LatticeConvexRegion R) (hfull : FullyPeriodicOn θ R) :
    ∃ D : FirstHalfPlaneData p θ, D.cone = regionCone R := by
  classical
  obtain ⟨n, E, hEpair, hEnot⟩ := fc_remove_double θ haperiodic m d hpairwise
  have hn : 2 ≤ n := fc_two_le E haperiodic
  choose v hv k hk hfactor using fun i => fc_primitive_factor (E.period i) (E.period_nonzero i)
  have hperiod : ∀ i, HasPeriod (E.field i) ((k i : ℤ) • v i) := by
    intro i
    rw [← hfactor i]
    exact E.has_period i
  have hvpair : Pairwise (fun i j => Nonparallel (v i) (v j)) := by
    intro i j hij hzero
    apply hEpair hij
    rw [hfactor i, hfactor j]
    have heq : det ((k i : ℤ) • v i) ((k j : ℤ) • v j) =
        (k i : ℤ) * (k j : ℤ) * det (v i) (v j) := by simp [det]; ring
    rw [heq, hzero, mul_zero]
  obtain ⟨a, b, hperiodR⟩ := hfull
  have hsum : θ = fun z => ∑ i, E.field i z := funext E.sum_eq
  have hfullE : FullPeriods (fun z => ∑ i, E.field i z) R a b := by
    rwa [← hsum]
  have hprop := proposition8_9 p hp n hn E.field v hv k hk hperiod hvpair R hR a b hfullE
  have hhalves : ∀ i, Disjoint (realLine (v i)) (interior (regionCone R)) ∧
      ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∃ t : ℤ,
        regionCone R ⊆ {w | 0 ≤ (σ : ℝ) * realDet (embed (v i)) w} ∧
          FullyPeriodicOn (E.field i) (signedUpperHalf σ (v i) t) := by
    intro i
    rcases hprop.2.2.2.1 i with hi | hi
    · exact False.elim (hEnot i hi.2)
    · exact hi
  choose havoid σ hσ t hcone hupper using hhalves
  choose u hu using fun i => primitive_height_surjective (v i) (hv i) 1
  have hσ0 : ∀ i, σ i ≠ 0 := by intro i; rcases hσ i with h | h <;> rw [h] <;> norm_num
  have hσsq : ∀ i, σ i * σ i = 1 := by intro i; rcases hσ i with h | h <;> rw [h] <;> norm_num
  have hdet_smul : ∀ (v w : Lattice) (a b : ℤ), det (a • v) (b • w) = a * b * det v w := by
    intros
    simp [det]
    ring
  let D : FirstHalfPlaneData p θ := {
    length := n
    at_least_two := hn
    field := E.field
    direction := fun i => σ i • v i
    transverse := fun i => σ i • u i
    basis := by
      intro i
      rw [hdet_smul, hσsq]
      simpa only [one_mul, height] using hu i
    primitive := by
      intro i
      rcases hσ i with hi | hi
      · simpa only [hi, one_smul] using hv i
      · simpa [hi, Primitive] using hv i
    multiplier := k
    positive_multiplier := hk
    has_period := by
      intro i
      have h := hasPeriod_zsmul _ _ (hperiod i) (σ i)
      convert h using 1
      rw [smul_smul, smul_smul, mul_comm]
    distinct_directions := by
      intro i j hij
      change det (σ i • v i) (σ j • v j) ≠ 0
      rw [hdet_smul]
      exact mul_ne_zero (mul_ne_zero (hσ0 i) (hσ0 j)) (hvpair hij)
    not_double := hEnot
    sum_eq := E.sum_eq
    threshold := t
    full_upper := by
      intro i
      have heq : upperHalf (σ i • v i) (t i) = signedUpperHalf (σ i) (v i) (t i) := by
        ext z
        change t i ≤ det (σ i • v i) z ↔ t i ≤ σ i * det (v i) z
        have hdet : det (σ i • v i) z = σ i * det (v i) z := by simp [det]; ring
        rw [hdet]
      rw [heq]
      exact hupper i
    cone := regionCone R
    sector := (hprop.2.2.2.2 (by rwa [← hsum]) hEnot).1
    full_dimensional := hprop.2.2.1
    cone_upper := by
      intro i w hw
      have h := hcone i hw
      change 0 ≤ realDet (embed (σ i • v i)) w
      have heq : realDet (embed (σ i • v i)) w = (σ i : ℝ) * realDet (embed (v i)) w := by
        simp [realDet, embed]
        ring
      rwa [heq]
    avoids_directions := by
      intro i
      apply Set.disjoint_left.mpr
      rintro x ⟨r, rfl⟩ hx
      apply Set.disjoint_left.mp (havoid i) _ hx
      refine ⟨r * (σ i : ℝ), ?_⟩
      ext <;> simp [embed, smul_eq_mul] <;> ring }
  exact ⟨D, rfl⟩

end ConvexNivat
