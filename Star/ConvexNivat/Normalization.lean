import ConvexNivat.ReductionAlgebra
import ConvexNivat.ReductionRegions
import ConvexNivat.RegionExtension

namespace ConvexNivat
open scoped BigOperators

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

private theorem merge_periodic {A : Type*} [AddCommMonoid A] {n : ℕ}
    {θ : Configuration A} (D : PeriodicDecomposition A θ (n + 1))
    (i : Fin (n + 1)) (k : Fin n) (q : Lattice) (hq : q ≠ 0)
    (hperiod : HasPeriod (fun z => D.field (i.succAbove k) z + D.field i z) q) :
    Nonempty (PeriodicDecomposition A θ n) := by
  classical
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
      simpa only [ite_true] using hperiod
    · simpa only [ha, ite_false] using D.has_period (i.succAbove a)
  · intro z
    exact (D.sum_eq z).trans (merge_sum (fun a => D.field a z) i k).symm

private theorem decomposition_two_le {A : Type*} [AddCommMonoid A]
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

/-- 8.5(c): all parallel components can be merged, preserving the exact sum
and not increasing its length; nonperiodicity forces at least two survivors. -/
theorem lemma8_5_merge_parallel (p : ℕ) (hp : p.Prime)
    (θ : Configuration (ZMod p)) (m : ℕ)
    (D : PeriodicDecomposition (ZMod p) θ m) :
    ∃ n : ℕ, n ≤ m ∧ ∃ E : PeriodicDecomposition (ZMod p) θ n,
      Pairwise (fun i j => Nonparallel (E.period i) (E.period j)) ∧
        (¬ Periodic θ → 2 ≤ n) := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hpair : Pairwise (fun i j => Nonparallel (D.period i) (D.period j))
    · exact ⟨m, le_rfl, D, hpair, decomposition_two_le D⟩
    · dsimp [Pairwise, Nonparallel] at hpair
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
        obtain ⟨E⟩ := merge_periodic D i k q hq (by simpa only [hk] using hperiod)
        obtain ⟨l, hl, F, hF, htwo⟩ := ih n (Nat.lt_succ_self n) E
        exact ⟨l, Nat.le_trans hl (Nat.le_succ n), F, hF, htwo⟩

private theorem regional_iterate {A : Type*} (f : Configuration A) (R : Set Lattice)
    (h : Lattice) (hforward : ForwardInvariant R h)
    (hperiod : ∀ z ∈ R, f (z + h) = f z) (n : ℕ) :
    ∀ z ∈ R, z + (n : ℤ) • h ∈ R ∧ f (z + (n : ℤ) • h) = f z := by
  intro z hz
  induction n with
  | zero => simpa using And.intro hz (show f z = f z from rfl)
  | succ n ih =>
    have heq : z + ((n + 1 : ℕ) : ℤ) • h = (z + (n : ℤ) • h) + h := by
      simp [add_smul, add_assoc]
    rw [heq]
    exact ⟨hforward _ ih.1, (hperiod _ ih.1).trans ih.2⟩

private theorem full_add_double {A : Type*} [AddCommMonoid A]
    (f g : Configuration A) (R : Set Lattice)
    (hf : FullyPeriodicOn f R) (hg : DoublyPeriodic g) :
    FullyPeriodicOn (fun z => f z + g z) R := by
  obtain ⟨h, k, hfull⟩ := hf
  obtain ⟨N, hN, hNp⟩ := (doublyPeriodic_iff_grid g).mp hg
  refine ⟨(N : ℤ) • h, (N : ℤ) • k, hfull.1, ?_, ?_, ?_, ?_, ?_⟩
  · have hn : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have heq : det ((N : ℤ) • h) ((N : ℤ) • k) = (N : ℤ) * (N : ℤ) * det h k := by
      simp [det]
      ring
    change det _ _ ≠ 0
    rw [heq]
    exact mul_ne_zero (mul_ne_zero hn hn) hfull.2.1
  · exact fun z hz => (regional_iterate f R h hfull.2.2.1 hfull.2.2.2.2.1 N z hz).1
  · exact fun z hz => (regional_iterate f R k hfull.2.2.2.1 hfull.2.2.2.2.2 N z hz).1
  · intro z hz
    change f (z + (N : ℤ) • h) + g (z + (N : ℤ) • h) = f z + g z
    rw [(regional_iterate f R h hfull.2.2.1 hfull.2.2.2.2.1 N z hz).2,
      hNp h z]
  · intro z hz
    change f (z + (N : ℤ) • k) + g (z + (N : ℤ) • k) = f z + g z
    rw [(regional_iterate f R k hfull.2.2.2.1 hfull.2.2.2.2.2 N z hz).2,
      hNp k z]

/-- 8.17 operation A gives a strictly shorter admissible decomposition. -/
theorem admissible_absorb_double (p : ℕ) (hp : p.Prime)
    (θ : Configuration (ZMod p)) (m : ℕ) (hm : 2 ≤ m)
    (D : AdmissibleDecomposition p θ m) (i : Fin m)
    (hi : DoublyPeriodic (D.field i)) :
    Nonempty (AdmissibleDecomposition p θ (m - 1)) := by
  classical
  cases m with
  | zero => omega
  | succ n =>
    have hn : 0 < n := by omega
    let k : Fin n := ⟨0, hn⟩
    obtain ⟨q, hq, hqp⟩ := doublyPeriodic_multiple_period (D.field i) hi
      (D.period (i.succAbove k))
    have hqne : q • D.period (i.succAbove k) ≠ 0 := by
      intro heq
      have hqn : q ≠ 0 := by omega
      apply D.period_nonzero (i.succAbove k)
      exact Prod.ext
        ((mul_eq_zero.mp (by simpa using congrArg Prod.fst heq)).resolve_left hqn)
        ((mul_eq_zero.mp (by simpa using congrArg Prod.snd heq)).resolve_left hqn)
    refine ⟨{
      field := fun a z => if a = k then D.field (i.succAbove a) z + D.field i z
        else D.field (i.succAbove a) z
      period := fun a => if a = k then q • D.period (i.succAbove a)
        else D.period (i.succAbove a)
      period_nonzero := ?_
      has_period := ?_
      sum_eq := ?_
      left := fun a => D.left (i.succAbove a)
      right := fun a => D.right (i.succAbove a)
      disjoint := fun a => D.disjoint (i.succAbove a)
      full_left := ?_
      full_right := ?_ }⟩
    · intro a
      by_cases ha : a = k
      · subst a
        simpa using hqne
      · simpa only [ha, ite_false] using D.period_nonzero (i.succAbove a)
    · intro a
      by_cases ha : a = k
      · subst a
        simp only [ite_true]
        exact hasPeriod_sum _ _ _
          (hasPeriod_zsmul _ _ (D.has_period _) q) hqp
      · simpa only [ha, ite_false] using D.has_period (i.succAbove a)
    · intro z
      exact (D.sum_eq z).trans (merge_sum (fun a => D.field a z) i k).symm
    · intro a
      by_cases ha : a = k
      · simp only [ha, ite_true]
        exact full_add_double _ _ _ (D.full_left _) hi
      · simpa only [ha, ite_false] using D.full_left (i.succAbove a)
    · intro a
      by_cases ha : a = k
      · simp only [ha, ite_true]
        exact full_add_double _ _ _ (D.full_right _) hi
      · simpa only [ha, ite_false] using D.full_right (i.succAbove a)

private theorem dot_add_normal (x y : Lattice) (n : RealPlane) :
    realDot (embed (x + y)) n = realDot (embed x) n + realDot (embed y) n := by
  simp [realDot, embed]
  ring

private theorem dot_smul_normal (x : Lattice) (k : ℤ) (n : RealPlane) :
    realDot (embed (k • x)) n = (k : ℝ) * realDot (embed x) n := by
  simp [realDot, embed]
  ring

private theorem extension_halfPlane {A : Type*} (G : Configuration A)
    (H : HalfPlane) (hfull : FullyPeriodicOn G H.carrier) :
    ∃ E : Configuration A, DoublyPeriodic E ∧ AgreesOn G E H.carrier := by
  obtain ⟨h, k, hk⟩ := hfull
  have hentry : ∀ z, ∃ n : ℕ, z + (n : ℤ) • (h + k) ∈ H.carrier := by
    intro z
    obtain ⟨N, hN⟩ := halfPlane_eventually_enters H (h + k) z
      (lemma8_2_halfPlane_normal G H h k hk)
    exact ⟨N, hN N le_rfl⟩
  have hext := lemma8_2_extensionAlong G H.carrier h k hk hentry
  exact ⟨extensionAlong G H.carrier (h + k) hentry, hext.2.2.2.2.1,
    fun z hz => (hext.1 z hz).symm⟩

private theorem alignment_one {A : Type*} (G : Configuration A)
    (h : Lattice) (hperiod : HasPeriod G h) (hnotdouble : ¬ DoublyPeriodic G)
    (U : HalfPlane) (hU : FullyPeriodicOn G U.carrier) :
    realDot (embed h) U.normal = 0 := by
  by_contra hdot
  have inward_contradiction : ∀ d : Lattice, HasPeriod G d →
      0 < realDot (embed d) U.normal → False := by
    intro d hd hdin
    obtain ⟨E, hE, hagree⟩ := extension_halfPlane G U hU
    have htranslate : translate d E = E := by
      apply doublyPeriodic_halfPlane_agreement _ _
        ((doublyPeriodic_translate_iff E d).mpr hE) hE U
      intro z hz
      have hzd := halfPlane_forwardInvariant U d hdin.le z hz
      exact (hagree (z + d) hzd).symm.trans ((hd z).trans (hagree z hz))
    have hEd : HasPeriod E d := by
      intro z
      exact congrFun htranslate z
    have hGE : G = E := by
      funext z
      obtain ⟨n, hn⟩ := halfPlane_eventually_enters U d z hdin
      exact ((hasPeriod_zsmul G d hd n) z).symm.trans
        ((hagree _ (hn n le_rfl)).trans ((hasPeriod_zsmul E d hEd n) z))
    exact hnotdouble (hGE.symm ▸ hE)
  rcases lt_or_gt_of_ne hdot with hneg | hpos
  · apply inward_contradiction (-h) (hasPeriod_neg G h hperiod)
    simpa only [show -h = (-1 : ℤ) • h by simp, dot_smul_normal,
      Int.cast_neg, Int.cast_one, neg_one_mul] using neg_pos.mpr hneg
  · exact inward_contradiction h hperiod hpos

/-- 8.17(γ): non-double-periodic components must have tangential half-plane
boundaries, including initially irrational normals. -/
theorem lemma8_17_alignment (p : ℕ) (hp : p.Prime) (G : Configuration (ZMod p))
    (h : Lattice) (hh : h ≠ 0) (hperiod : HasPeriod G h)
    (hnotdouble : ¬ DoublyPeriodic G) (U V : HalfPlane)
    (hdisjoint : Disjoint U.carrier V.carrier)
    (hU : FullyPeriodicOn G U.carrier) (hV : FullyPeriodicOn G V.carrier) :
    realDot (embed h) U.normal = 0 ∧ realDot (embed h) V.normal = 0 := by
  exact ⟨alignment_one G h hperiod hnotdouble U hU,
    alignment_one G h hperiod hnotdouble V hV⟩

private theorem primitive_factor (h : Lattice) (hh : h ≠ 0) :
    ∃ v : Lattice, Primitive v ∧ ∃ k : ℤ, 1 ≤ k ∧ h = k • v := by
  have hg : 0 < Int.gcd h.1 h.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp hz
    exact hh (Prod.ext hx hy)
  obtain ⟨x, y, hxy, hx, hy⟩ := Int.exists_gcd_one hg
  refine ⟨(x, y), hxy, Int.gcd h.1 h.2, ?_, ?_⟩
  · exact_mod_cast hg
  · exact Prod.ext (hx.trans (mul_comm _ _)) (hy.trans (mul_comm _ _))

private theorem aligned_dot (v u : Lattice) (hu : height v u = 1)
    (H : HalfPlane) (hv : realDot (embed v) H.normal = 0) :
    ∀ z, realDot (embed z) H.normal =
      (height v z : ℝ) * realDot (embed u) H.normal := by
  intro z
  have hu' : (v.1 : ℝ) * u.2 - (v.2 : ℝ) * u.1 = 1 := by
    exact_mod_cast hu
  dsimp [realDot, embed] at hv ⊢
  dsimp [height, det]
  push_cast
  calc
    (z.1 : ℝ) * H.normal.1 + (z.2 : ℝ) * H.normal.2 =
        ((v.1 : ℝ) * u.2 - (v.2 : ℝ) * u.1) *
          ((z.1 : ℝ) * H.normal.1 + (z.2 : ℝ) * H.normal.2) := by rw [hu', one_mul]
    _ = ((v.1 : ℝ) * z.2 - (v.2 : ℝ) * z.1) *
          ((u.1 : ℝ) * H.normal.1 + (u.2 : ℝ) * H.normal.2) +
        ((z.1 : ℝ) * u.2 - (z.2 : ℝ) * u.1) *
          ((v.1 : ℝ) * H.normal.1 + (v.2 : ℝ) * H.normal.2) := by ring
    _ = _ := by rw [hv, mul_zero, add_zero]

private theorem aligned_coefficient_nonzero (v u : Lattice)
    (hu : height v u = 1) (H : HalfPlane)
    (hv : realDot (embed v) H.normal = 0) :
    realDot (embed u) H.normal ≠ 0 := by
  intro hz
  have h1 := aligned_dot v u hu H hv (1, 0)
  have h2 := aligned_dot v u hu H hv (0, 1)
  rw [hz, mul_zero] at h1 h2
  apply H.normal_ne_zero
  exact Prod.ext (by simpa [realDot, embed] using h1)
    (by simpa [realDot, embed] using h2)

private theorem carrier_mono_dot (H : HalfPlane) (x y : Lattice)
    (hxy : realDot (embed x) H.normal ≤ realDot (embed y) H.normal)
    (hx : x ∈ H.carrier) : y ∈ H.carrier := by
  unfold HalfPlane.carrier at hx ⊢
  simp only [Set.mem_ofPred_eq] at hx ⊢
  cases hs : H.strict <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hx ⊢ <;>
    linarith

private theorem aligned_positive_tail (v u : Lattice) (hu : height v u = 1)
    (H : HalfPlane) (hv : realDot (embed v) H.normal = 0)
    (hpositive : 0 < realDot (embed u) H.normal) :
    ∃ N : ℤ, upperHalf v N ⊆ H.carrier := by
  obtain ⟨N, hN⟩ := halfPlane_eventually_enters H u 0 hpositive
  refine ⟨N, ?_⟩
  intro z hz
  change (N : ℤ) ≤ height v z at hz
  apply carrier_mono_dot H (0 + (N : ℤ) • u) z _ (hN N le_rfl)
  rw [aligned_dot v u hu H hv z, dot_add_normal, dot_smul_normal]
  simp only [show realDot (embed (0 : Lattice)) H.normal = 0 by simp [realDot, embed],
    zero_add, Int.cast_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hpositive.le

private theorem aligned_negative_tail (v u : Lattice) (hu : height v u = 1)
    (H : HalfPlane) (hv : realDot (embed v) H.normal = 0)
    (hnegative : realDot (embed u) H.normal < 0) :
    ∃ N : ℤ, lowerHalf v N ⊆ H.carrier := by
  have hin : 0 < realDot (embed (-u)) H.normal := by
    rw [show -u = (-1 : ℤ) • u by simp, dot_smul_normal]
    norm_num
    exact hnegative
  obtain ⟨N, hN⟩ := halfPlane_eventually_enters H (-u) 0 hin
  refine ⟨-(N : ℤ), ?_⟩
  intro z hz
  apply carrier_mono_dot H (0 + (N : ℤ) • (-u)) z _ (hN N le_rfl)
  rw [aligned_dot v u hu H hv z, dot_add_normal, dot_smul_normal,
    show -u = (-1 : ℤ) • u by simp, dot_smul_normal]
  simp only [show realDot (embed (0 : Lattice)) H.normal = 0 by simp [realDot, embed],
    zero_add, Int.cast_natCast,
    Int.cast_neg, Int.cast_one, neg_one_mul, zero_add]
  have hc : (height v z : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hz
  nlinarith

private theorem aligned_opposite (v u : Lattice) (hu : height v u = 1)
    (U V : HalfPlane) (hU : realDot (embed v) U.normal = 0)
    (hV : realDot (embed v) V.normal = 0)
    (hdisjoint : Disjoint U.carrier V.carrier) :
    (realDot (embed u) U.normal < 0 ∧ 0 < realDot (embed u) V.normal) ∨
    (0 < realDot (embed u) U.normal ∧ realDot (embed u) V.normal < 0) := by
  have une := aligned_coefficient_nonzero v u hu U hU
  have vne := aligned_coefficient_nonzero v u hu V hV
  have pos_contra : ¬ (0 < realDot (embed u) U.normal ∧
      0 < realDot (embed u) V.normal) := by
    rintro ⟨hup, hvp⟩
    obtain ⟨a, ha⟩ := aligned_positive_tail v u hu U hU hup
    obtain ⟨b, hb⟩ := aligned_positive_tail v u hu V hV hvp
    have hz : height v (max a b • u) = max a b := by
      rw [height_zsmul, hu, mul_one]
    have hzu : max a b • u ∈ U.carrier := ha
      (by change a ≤ height v (max a b • u); rw [hz]; exact le_max_left _ _)
    have hzv : max a b • u ∈ V.carrier := hb
      (by change b ≤ height v (max a b • u); rw [hz]; exact le_max_right _ _)
    exact Set.disjoint_left.mp hdisjoint hzu hzv
  have neg_contra : ¬ (realDot (embed u) U.normal < 0 ∧
      realDot (embed u) V.normal < 0) := by
    rintro ⟨hun, hvn⟩
    obtain ⟨a, ha⟩ := aligned_negative_tail v u hu U hU hun
    obtain ⟨b, hb⟩ := aligned_negative_tail v u hu V hV hvn
    have hz : height v (min a b • u) = min a b := by
      rw [height_zsmul, hu, mul_one]
    have hzu : min a b • u ∈ U.carrier := ha
      (by change height v (min a b • u) ≤ a; rw [hz]; exact min_le_left _ _)
    have hzv : min a b • u ∈ V.carrier := hb
      (by change height v (min a b • u) ≤ b; rw [hz]; exact min_le_right _ _)
    exact Set.disjoint_left.mp hdisjoint hzu hzv
  rcases lt_or_gt_of_ne une with hun | hup
  · left
    exact ⟨hun, lt_of_le_of_ne (by by_contra h; exact neg_contra ⟨hun, lt_of_not_ge h⟩)
      vne.symm⟩
  · right
    exact ⟨hup, lt_of_le_of_ne (by by_contra h; exact pos_contra ⟨hup, lt_of_not_ge h⟩)
      vne⟩

/-- 8.17(γ) producer: the aligned component has the actual primitive direction,
positive tangential period, doubly periodic tails, and integer strip bounds. -/
theorem lemma8_17_component (p : ℕ) (hp : p.Prime) (G : Configuration (ZMod p))
    (h : Lattice) (hh : h ≠ 0) (hperiod : HasPeriod G h)
    (hnotdouble : ¬ DoublyPeriodic G) (U V : HalfPlane)
    (hdisjoint : Disjoint U.carrier V.carrier)
    (hU : FullyPeriodicOn G U.carrier) (hV : FullyPeriodicOn G V.carrier) :
    ∃ C : StarComponent p, C.field = G ∧ det C.direction h = 0 := by
  obtain ⟨v, hv, k, hk, hkv⟩ := primitive_factor h hh
  obtain ⟨u, hu⟩ := primitive_height_surjective v hv 1
  have hvalign : realDot (embed v) U.normal = 0 ∧ realDot (embed v) V.normal = 0 := by
    have halign := lemma8_17_alignment p hp G h hh hperiod hnotdouble U V hdisjoint hU hV
    rw [hkv, dot_smul_normal, dot_smul_normal] at halign
    have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    exact ⟨(mul_eq_zero.mp halign.1).resolve_left hkne,
      (mul_eq_zero.mp halign.2).resolve_left hkne⟩
  have construct : ∀ L R : HalfPlane, FullyPeriodicOn G L.carrier →
      FullyPeriodicOn G R.carrier → realDot (embed v) L.normal = 0 →
      realDot (embed v) R.normal = 0 → realDot (embed u) L.normal < 0 →
      0 < realDot (embed u) R.normal → ∃ C : StarComponent p,
        C.field = G ∧ det C.direction h = 0 := by
    intro L R hL hR hvL hvR hnL hnR
    obtain ⟨a, ha⟩ := aligned_negative_tail v u hu L hvL hnL
    obtain ⟨b, hb⟩ := aligned_positive_tail v u hu R hvR hnR
    obtain ⟨LT, hLT, hagL⟩ := extension_halfPlane G L hL
    obtain ⟨RT, hRT, hagR⟩ := extension_halfPlane G R hR
    refine ⟨{
      direction := v
      primitive := hv
      field := G
      tangential_period := ⟨k, hk, hkv ▸ hperiod⟩
      not_doubly_periodic := hnotdouble
      leftTail := LT
      rightTail := RT
      left_doubly_periodic := hLT
      right_doubly_periodic := hRT
      lower := min a 0
      upper := max b 0
      bounds := by have := min_le_right a 0; have := le_max_right b 0; omega
      left_agreement := ?_
      right_agreement := ?_ }, rfl, ?_⟩
    · intro z hz
      exact hagL z (ha (show height v z ≤ a by have := min_le_left a 0; exact le_trans hz.le this))
    · intro z hz
      exact hagR z (hb (show b ≤ height v z by have := le_max_left b 0; exact le_trans this hz.le))
    · change det v h = 0
      rw [hkv]
      change height v (k • v) = 0
      rw [height_zsmul, height_self, mul_zero]
  rcases aligned_opposite v u hu U V hvalign.1 hvalign.2 hdisjoint with hsign | hsign
  · exact construct U V hU hV hvalign.1 hvalign.2 hsign.1 hsign.2
  · exact construct V U hV hU hvalign.2 hvalign.1 hsign.2 hsign.1

private theorem parallel_alignment (v h : Lattice) (hh : h ≠ 0)
    (hdet : det v h = 0) (n : RealPlane) (horth : realDot (embed h) n = 0) :
    realDot (embed v) n = 0 := by
  have hd : (v.1 : ℝ) * h.2 - (v.2 : ℝ) * h.1 = 0 := by exact_mod_cast hdet
  dsimp [realDot, embed] at horth ⊢
  by_cases hx : h.1 = 0
  · have hy : h.2 ≠ 0 := by
      intro hy
      exact hh (Prod.ext hx hy)
    have hy' : (h.2 : ℝ) ≠ 0 := by exact_mod_cast hy
    have hn : n.2 = 0 := by
      simp only [hx, Int.cast_zero, zero_mul, zero_add] at horth
      exact (mul_eq_zero.mp horth).resolve_left hy'
    have hv : (v.1 : ℝ) = 0 := by
      simp only [hx, Int.cast_zero, mul_zero, sub_zero] at hd
      exact (mul_eq_zero.mp hd).resolve_right hy'
    rw [hn, hv]
    ring
  · have hx' : (h.1 : ℝ) ≠ 0 := by exact_mod_cast hx
    have heq : (h.1 : ℝ) * ((v.1 : ℝ) * n.1 + (v.2 : ℝ) * n.2) = 0 := by
      calc
        _ = (v.1 : ℝ) * ((h.1 : ℝ) * n.1 + (h.2 : ℝ) * n.2) -
            ((v.1 : ℝ) * h.2 - (v.2 : ℝ) * h.1) * n.2 := by ring
        _ = 0 := by rw [horth, hd]; ring
    exact (mul_eq_zero.mp heq).resolve_left hx'

private theorem fullyPeriodic_agreement {A : Type*} (f g : Configuration A)
    (R : Set Lattice) (hg : FullyPeriodicOn g R) (heq : AgreesOn f g R) :
    FullyPeriodicOn f R := by
  obtain ⟨h, k, hp⟩ := hg
  refine ⟨h, k, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_, ?_⟩
  · intro z hz
    exact (heq _ (hp.2.2.1 z hz)).trans ((hp.2.2.2.2.1 z hz).trans (heq z hz).symm)
  · intro z hz
    exact (heq _ (hp.2.2.2.1 z hz)).trans ((hp.2.2.2.2.2 z hz).trans (heq z hz).symm)

/-- 8.17 operation C gives a strictly shorter admissible decomposition. -/
theorem admissible_merge_parallel (p : ℕ) (hp : p.Prime)
    (θ : Configuration (ZMod p)) (m : ℕ) (D : AdmissibleDecomposition p θ m)
    (i j : Fin m) (hij : i ≠ j)
    (hinotdouble : ¬ DoublyPeriodic (D.field i))
    (hjnotdouble : ¬ DoublyPeriodic (D.field j))
    (hparallel : det (D.period i) (D.period j) = 0) :
    Nonempty (AdmissibleDecomposition p θ (m - 1)) := by
  classical
  obtain ⟨v, hv, t, ht, htperiod⟩ := primitive_factor (D.period i) (D.period_nonzero i)
  obtain ⟨u, hu⟩ := primitive_height_surjective v hv 1
  have hvi : det v (D.period i) = 0 := by
    rw [htperiod]
    change height v (t • v) = 0
    rw [height_zsmul, height_self, mul_zero]
  have hvj : det v (D.period j) = 0 := by
    have heq : det (t • v) (D.period j) = t * det v (D.period j) := by
      simp [det]
      ring
    rw [htperiod, heq] at hparallel
    exact (mul_eq_zero.mp hparallel).resolve_left (by omega)
  have tails : ∀ a : Fin m, ¬ DoublyPeriodic (D.field a) → det v (D.period a) = 0 →
      ∃ low high : ℤ, ∃ L R : Configuration (ZMod p), DoublyPeriodic L ∧
        DoublyPeriodic R ∧ AgreesOn (D.field a) L (lowerHalf v low) ∧
          AgreesOn (D.field a) R (upperHalf v high) := by
    intro a hnot hdir
    have halign := lemma8_17_alignment p hp (D.field a) (D.period a)
      (D.period_nonzero a) (D.has_period a) hnot (D.left a) (D.right a)
      (D.disjoint a) (D.full_left a) (D.full_right a)
    have hleft := parallel_alignment v (D.period a) (D.period_nonzero a)
      hdir (D.left a).normal halign.1
    have hright := parallel_alignment v (D.period a) (D.period_nonzero a)
      hdir (D.right a).normal halign.2
    have side : ∀ L R : HalfPlane, FullyPeriodicOn (D.field a) L.carrier →
        FullyPeriodicOn (D.field a) R.carrier → realDot (embed v) L.normal = 0 →
        realDot (embed v) R.normal = 0 → realDot (embed u) L.normal < 0 →
        0 < realDot (embed u) R.normal → ∃ low high : ℤ,
          ∃ LT RT : Configuration (ZMod p), DoublyPeriodic LT ∧ DoublyPeriodic RT ∧
            AgreesOn (D.field a) LT (lowerHalf v low) ∧
              AgreesOn (D.field a) RT (upperHalf v high) := by
      intro L R hL hR hvL hvR hnL hnR
      obtain ⟨low, hlow⟩ := aligned_negative_tail v u hu L hvL hnL
      obtain ⟨high, hhigh⟩ := aligned_positive_tail v u hu R hvR hnR
      obtain ⟨LT, hLT, hLT_agree⟩ := extension_halfPlane (D.field a) L hL
      obtain ⟨RT, hRT, hRT_agree⟩ := extension_halfPlane (D.field a) R hR
      exact ⟨low, high, LT, RT, hLT, hRT,
        fun z hz => hLT_agree z (hlow hz), fun z hz => hRT_agree z (hhigh hz)⟩
    rcases aligned_opposite v u hu (D.left a) (D.right a) hleft hright
      (D.disjoint a) with hs | hs
    · exact side _ _ (D.full_left a) (D.full_right a) hleft hright hs.1 hs.2
    · exact side _ _ (D.full_right a) (D.full_left a) hright hleft hs.2 hs.1
  obtain ⟨ai, bi, Li, Ri, hLi, hRi, hagLi, hagRi⟩ := tails i hinotdouble hvi
  obtain ⟨aj, bj, Lj, Rj, hLj, hRj, hagLj, hagRj⟩ := tails j hjnotdouble hvj
  have hvne := primitive_ne_zero v hv
  let L : HalfPlane := {
    normal := (v.2, -v.1)
    normal_ne_zero := by
      intro hz
      have h1 : v.2 = 0 := by
        have hc := congrArg Prod.fst hz
        change (v.2 : ℝ) = 0 at hc
        exact_mod_cast hc
      have h2 : v.1 = 0 := by
        have hc := congrArg Prod.snd hz
        change -(v.1 : ℝ) = 0 at hc
        exact_mod_cast neg_eq_zero.mp hc
      exact hvne (Prod.ext h2 h1)
    threshold := -(min (min ai aj) 0 : ℤ)
    strict := false }
  let R : HalfPlane := {
    normal := (-v.2, v.1)
    normal_ne_zero := by
      intro hz
      have h1 : v.2 = 0 := by
        have hc := congrArg Prod.fst hz
        change -(v.2 : ℝ) = 0 at hc
        exact_mod_cast neg_eq_zero.mp hc
      have h2 : v.1 = 0 := by
        have hc := congrArg Prod.snd hz
        change (v.1 : ℝ) = 0 at hc
        exact_mod_cast hc
      exact hvne (Prod.ext h2 h1)
    threshold := (max (max bi bj) 1 : ℤ)
    strict := false }
  have hLcarrier : L.carrier = lowerHalf v (min (min ai aj) 0) := by
    ext z
    simp only [L, HalfPlane.carrier, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
      lowerHalf, realDot, embed, det]
    push_cast
    have hz : (z.1 : ℝ) * v.2 + (z.2 : ℝ) * -(v.1 : ℝ) =
        -((v.1 : ℝ) * z.2 - (v.2 : ℝ) * z.1) := by ring
    rw [hz, neg_le_neg_iff]
    exact_mod_cast Iff.rfl
  have hRcarrier : R.carrier = upperHalf v (max (max bi bj) 1) := by
    ext z
    simp only [R, HalfPlane.carrier, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
      upperHalf, realDot, embed, det]
    push_cast
    have hz : (z.1 : ℝ) * -(v.2 : ℝ) + (z.2 : ℝ) * v.1 =
        (v.1 : ℝ) * z.2 - (v.2 : ℝ) * z.1 := by ring
    rw [hz]
    exact_mod_cast Iff.rfl
  have hLR : Disjoint L.carrier R.carrier := by
    rw [hLcarrier, hRcarrier]
    apply Set.disjoint_left.mpr
    intro z hzL hzR
    change height v z ≤ min (min ai aj) 0 at hzL
    change max (max bi bj) 1 ≤ height v z at hzR
    have := min_le_right (min ai aj) 0
    have := le_max_right (max bi bj) 1
    omega
  have hfullL : FullyPeriodicOn (fun z => D.field j z + D.field i z) L.carrier := by
    apply fullyPeriodic_agreement _ (fun z => Lj z + Li z) _
      (doublyPeriodic_full_halfPlane _ (doublyPeriodic_sum _ _ hLj hLi) L)
    intro z hz
    rw [hLcarrier] at hz
    change height v z ≤ min (min ai aj) 0 at hz
    have hi := min_le_left ai aj
    have hj := min_le_right ai aj
    have ha := min_le_left (min ai aj) 0
    change D.field j z + D.field i z = Lj z + Li z
    rw [hagLj z (show height v z ≤ aj by omega),
      hagLi z (show height v z ≤ ai by omega)]
  have hfullR : FullyPeriodicOn (fun z => D.field j z + D.field i z) R.carrier := by
    apply fullyPeriodic_agreement _ (fun z => Rj z + Ri z) _
      (doublyPeriodic_full_halfPlane _ (doublyPeriodic_sum _ _ hRj hRi) R)
    intro z hz
    rw [hRcarrier] at hz
    change max (max bi bj) 1 ≤ height v z at hz
    have hi := le_max_left bi bj
    have hj := le_max_right bi bj
    have hb := le_max_left (max bi bj) 1
    change D.field j z + D.field i z = Rj z + Ri z
    rw [hagRj z (show bj ≤ height v z by omega),
      hagRi z (show bi ≤ height v z by omega)]
  have hreverse : det (D.period j) (D.period i) = 0 := by
    dsimp [det] at hparallel ⊢
    nlinarith
  obtain ⟨q, hq, _, hqp⟩ := parallel_periodic_sum (D.field j) (D.field i)
    (D.period j) (D.period i) (D.period_nonzero j) (D.period_nonzero i)
    hreverse (D.has_period j) (D.has_period i)
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    refine ⟨{
      field := fun a z => if a = k then D.field (i.succAbove a) z + D.field i z
        else D.field (i.succAbove a) z
      period := fun a => if a = k then q else D.period (i.succAbove a)
      period_nonzero := ?_
      has_period := ?_
      sum_eq := ?_
      left := fun a => if a = k then L else D.left (i.succAbove a)
      right := fun a => if a = k then R else D.right (i.succAbove a)
      disjoint := ?_
      full_left := ?_
      full_right := ?_ }⟩
    · intro a
      split_ifs <;> first | exact hq | exact D.period_nonzero _
    · intro a
      by_cases ha : a = k
      · subst a
        simpa only [ite_true, hk] using hqp
      · simpa only [ha, ite_false] using D.has_period (i.succAbove a)
    · intro z
      exact (D.sum_eq z).trans (merge_sum (fun a => D.field a z) i k).symm
    · intro a
      by_cases ha : a = k
      · simpa only [ha, ite_true] using hLR
      · simpa only [ha, ite_false] using D.disjoint (i.succAbove a)
    · intro a
      by_cases ha : a = k
      · subst a
        simpa only [ite_true, hk] using hfullL
      · simpa only [ha, ite_false] using D.full_left (i.succAbove a)
    · intro a
      by_cases ha : a = k
      · subst a
        simpa only [ite_true, hk] using hfullR
      · simpa only [ha, ite_false] using D.full_right (i.succAbove a)

private theorem parallel_trans (v w h k : Lattice)
    (hvh : det v h = 0) (hwk : det w k = 0) (hvw : det v w = 0)
    (hv : v ≠ 0) (hw : w ≠ 0) : det h k = 0 := by
  have factor : ∀ a b c : Lattice, a ≠ 0 → det a b = 0 → det a c = 0 →
      det b c = 0 := by
    intro a b c ha hab hac
    by_cases hax : a.1 = 0
    · have hay : a.2 ≠ 0 := by
        intro hay
        exact ha (Prod.ext hax hay)
      have bx : b.1 = 0 := by
        simp only [det, hax, zero_mul, zero_sub, neg_eq_zero] at hab
        exact (mul_eq_zero.mp hab).resolve_left hay
      have cx : c.1 = 0 := by
        simp only [det, hax, zero_mul, zero_sub, neg_eq_zero] at hac
        exact (mul_eq_zero.mp hac).resolve_left hay
      simp [det, bx, cx]
    · have heq : a.1 * det b c = 0 := by
        calc
          _ = b.1 * det a c - c.1 * det a b := by dsimp [det]; ring
          _ = 0 := by rw [hab, hac]; ring
      exact (mul_eq_zero.mp heq).resolve_left hax
  have hwh : det w h = 0 := factor v w h hv hvw hvh
  exact factor w h k hw hwh hwk

/-- 8.17: no initial minimality or distinct-period-directions requirement. -/
theorem lemma8_17 (p : ℕ) (hp : p.Prime) (θ : Configuration (ZMod p))
    (haperiodic : ¬ Periodic θ) (m : ℕ) (D : AdmissibleDecomposition p θ m) :
    IsStarConfiguration θ := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have htwo : 2 ≤ m := decomposition_two_le D.toPeriodicDecomposition haperiodic
    by_cases hdouble : ∃ i, DoublyPeriodic (D.field i)
    · obtain ⟨i, hi⟩ := hdouble
      obtain ⟨E⟩ := admissible_absorb_double p hp θ m htwo D i hi
      exact ih (m - 1) (by omega) E
    · have hnotdouble : ∀ i, ¬ DoublyPeriodic (D.field i) := by
        simpa only [not_exists] using hdouble
      by_cases hpair : Pairwise (fun i j => Nonparallel (D.period i) (D.period j))
      · have hcomp : ∀ i, ∃ C : StarComponent p,
            C.field = D.field i ∧ det C.direction (D.period i) = 0 := by
          intro i
          exact lemma8_17_component p hp (D.field i) (D.period i)
            (D.period_nonzero i) (D.has_period i) (hnotdouble i)
            (D.left i) (D.right i) (D.disjoint i) (D.full_left i) (D.full_right i)
        choose C hfield hdir using hcomp
        let S : StarData p := {
          prime := hp
          m := m
          two_le := htwo
          component := C
          pairwise_nonparallel := by
            intro i j hij hparallel
            apply hpair hij
            exact parallel_trans (C i).direction (C j).direction (D.period i) (D.period j)
              (hdir i) (hdir j) hparallel
              (primitive_ne_zero _ (C i).primitive) (primitive_ne_zero _ (C j).primitive) }
        refine ⟨S, ?_⟩
        funext z
        change θ z = ∑ i, (C i).field z
        simp only [hfield]
        exact D.sum_eq z
      · dsimp [Pairwise, Nonparallel] at hpair
        push Not at hpair
        obtain ⟨i, j, hij, hparallel⟩ := hpair
        obtain ⟨E⟩ := admissible_merge_parallel p hp θ m D i j hij
          (hnotdouble i) (hnotdouble j) hparallel
        exact ih (m - 1) (by omega) E

end ConvexNivat
