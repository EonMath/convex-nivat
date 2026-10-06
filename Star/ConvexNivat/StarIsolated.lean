import ConvexNivat.StarOperators
import ConvexNivat.CoreLattice
import ConvexNivat.CorePeriods
import ConvexNivat.OperatorDifferences
import ConvexNivat.OperatorFiniteSupport

namespace ConvexNivat
open scoped BigOperators Pointwise
noncomputable section
set_option maxHeartbeats 1000000

 theorem isolatedScalarField_period {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (η : ScalarField) (hη : applyLaurent (starDifference P) η = 0) (i : Fin d.m) :
    HasPeriod (isolatedScalarField P η i) (P.vector i) := by
  apply (difference_zero_iff_period (P.vector i) _).mp
  rw [isolatedScalarField, ← applyLaurent_mul]
  simpa only [starDifference, starOtherDifference,
    differenceProduct_split Finset.univ P.vector i (Finset.mem_univ i)] using hη

private theorem encoding_killed {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (w : ZMod p → ℤ)
    (hD : ∀ a : ZMod p,
      applyLaurent (starDifference P) (scalarColourIndicator d.configuration a) = 0) :
    applyLaurent (starDifference P) (integerScalarEncoding d w) = 0 := by
  classical
  let : NeZero p := ⟨d.prime.ne_zero⟩
  have hη : integerScalarEncoding d w =
      ∑ a : ZMod p, (w a : ℂ) • scalarColourIndicator d.configuration a := by
    ext z
    simp [integerScalarEncoding, scalarEncoding, scalarColourIndicator,
      Finset.sum_apply, eq_comm]
  rw [hη]
  have hsum (s : Finset (ZMod p)) :
      applyLaurent (starDifference P)
        (∑ a ∈ s, (w a : ℂ) • scalarColourIndicator d.configuration a) = 0 := by
    induction s using Finset.induction_on with
    | empty => ext z; simp [applyLaurent]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, applyLaurent_add_field,
          applyLaurent_smul_field, hD a, ih]
        simp
  exact hsum Finset.univ

private theorem height_vector_other {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (i j : Fin d.m) (hij : j ≠ i) :
    height (d.component j).direction (P.vector i) ≠ 0 := by
  rw [StarPeriodData.vector, height_zsmul]
  exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt (P.multiplier_pos i))
    (d.pairwise_nonparallel j i hij)

private theorem scalar_period_encode {A : Type*} (f : Configuration A) (h : Lattice)
    (hf : HasPeriod f h) (w : A → ℂ) : HasPeriod (scalarEncoding f w) h := by
  intro z
  simp only [scalarEncoding, hf z]

private theorem applyLaurent_sub_field (q : LaurentPolynomial) (f g : ScalarField) :
    applyLaurent q (f-g) = applyLaurent q f - applyLaurent q g := by
  funext z
  simp [applyLaurent, Finsupp.sum_sub, mul_sub]

/-- The unique minimizing subset is formed from exactly the negative heights. -/
private theorem unique_minimal_subset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℤ) (ha : ∀ j ∈ s, a j ≠ 0) :
    ∀ C ∈ s.powerset, C ≠ s.filter (fun j => a j < 0) →
      (∑ j ∈ s.filter (fun j => a j < 0), a j) < ∑ j ∈ C, a j := by
  intro C hC hne
  have hCs : C ⊆ s := Finset.mem_powerset.mp hC
  let M := s.filter (fun j => a j < 0)
  have hnon : (C \ M).Nonempty ∨ (M \ C).Nonempty := by
    by_contra hn
    push Not at hn
    apply hne
    apply Finset.Subset.antisymm
    · intro j hj
      by_contra hm
      have hjm := Finset.mem_sdiff.mpr ⟨hj, hm⟩
      rw [hn.1] at hjm
      simp only [Finset.notMem_empty] at hjm
    · intro j hj
      by_contra hc
      have hjm := Finset.mem_sdiff.mpr ⟨hj, hc⟩
      rw [hn.2] at hjm
      simp only [Finset.notMem_empty] at hjm
  have hpos : ∀ j ∈ C \ M, 0 < a j := by
    intro j hj
    obtain ⟨hc, hm⟩ := Finset.mem_sdiff.mp hj
    have hjs := hCs hc
    have hn : ¬ a j < 0 := by
      intro hn
      exact hm (Finset.mem_filter.mpr ⟨hjs, hn⟩)
    exact lt_of_le_of_ne (le_of_not_gt hn) (ha j hjs).symm
  have hneg : ∀ j ∈ M \ C, a j < 0 := by
    intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
  have hcp : 0 ≤ ∑ j ∈ C \ M, a j :=
    Finset.sum_nonneg fun j hj => le_of_lt (hpos j hj)
  have hmn : ∑ j ∈ M \ C, a j ≤ 0 :=
    Finset.sum_nonpos fun j hj => le_of_lt (hneg j hj)
  have hstrict : (∑ j ∈ M \ C, a j) < ∑ j ∈ C \ M, a j := by
    rcases hnon with hc | hm
    · exact lt_of_le_of_lt hmn (Finset.sum_pos hpos hc)
    · exact lt_of_lt_of_le (Finset.sum_neg hneg hm) hcp
  have hCsplit := Finset.sum_inter_add_sum_sdiff C M a
  have hMsplit := Finset.sum_inter_add_sum_sdiff M C a
  rw [Finset.inter_comm M C] at hMsplit
  change (∑ j ∈ M, a j) < ∑ j ∈ C, a j
  omega

/-- Maximal-row nonvanishing, using the unique formal extremal subset. -/
private theorem differenceProduct_nonzero_of_upper_support {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → Lattice) (v : Lattice) (f : ScalarField)
    (hH : ∀ j ∈ s, height v (H j) ≠ 0)
    (hf : f ≠ 0) (b : ℤ) (hb : ∀ z, f z ≠ 0 → height v z ≤ b) :
    applyLaurent (differenceProduct s H) f ≠ 0 := by
  classical
  let A : Set ℤ := height v '' Function.support f
  have hA : A.Nonempty := by
    obtain ⟨z, hz⟩ := Function.ne_iff.mp hf
    exact ⟨height v z, z, hz, rfl⟩
  have hAb : BddAbove A := ⟨b, by rintro _ ⟨z, hz, rfl⟩; exact hb z hz⟩
  obtain ⟨z, hz, hzmax⟩ := Int.csSup_mem hA hAb
  let M := s.filter (fun j => height v (H j) < 0)
  have hMp : M ∈ s.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hheight (C : Finset ι) : height v (formalExponent H C) =
      ∑ j ∈ C, height v (H j) := by
    unfold formalExponent
    induction C using Finset.induction_on with
    | empty => simp [height, det]
    | @insert j C hj ih => rw [Finset.sum_insert hj, height_add, ih, Finset.sum_insert hj]
  have hvanish (C : Finset ι) (hC : C ∈ s.powerset) (hne : C ≠ M) :
      f (z - formalExponent H M + formalExponent H C) = 0 := by
    by_contra hnon
    have hle := le_csSup hAb (show height v
        (z - formalExponent H M + formalExponent H C) ∈ A from ⟨_, hnon, rfl⟩)
    have hlt := unique_minimal_subset s (fun j => height v (H j)) hH C hC hne
    change (∑ j ∈ M, height v (H j)) < ∑ j ∈ C, height v (H j) at hlt
    have hcalc : height v (z - formalExponent H M + formalExponent H C) =
        height v z - height v (formalExponent H M) + height v (formalExponent H C) := by
      simp only [height, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [hcalc, hheight, hheight, hzmax] at hle
    omega
  have heval : applyLaurent (differenceProduct s H) f (z-formalExponent H M) =
      (-1 : ℂ) ^ (s.card - M.card) * f z := by
    rw [differenceProduct_expansion, Finset.sum_eq_single M]
    · simp
    · intro C hC hne
      rw [hvanish C hC hne, mul_zero]
    · exact fun hn => (hn hMp).elim
  intro hzero
  have he := congrFun hzero (z-formalExponent H M)
  rw [heval] at he
  exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hz) he


private def rayTail {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (i j : Fin d.m) : Configuration (ZMod p) :=
  if height (d.component j).direction (P.vector i) < 0 then
    (d.component j).leftTail else (d.component j).rightTail

private def rayBackground {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (i : Fin d.m) : Configuration (ZMod p) :=
  ∑ j ∈ Finset.univ.erase i, rayTail d P i j

private theorem rayTail_period {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (i j k : Fin d.m) : HasPeriod (rayTail d P i j) (P.vector k) := by
  unfold rayTail
  split
  · exact (P.all_tail_periods k j).1
  · exact (P.all_tail_periods k j).2

private theorem rayBackground_period {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (i k : Fin d.m) : HasPeriod (rayBackground d P i) (P.vector k) := by
  intro z
  simp only [rayBackground, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact rayTail_period d P i j k z

private theorem rayBackground_doublyPeriodic {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (i : Fin d.m) : DoublyPeriodic (rayBackground d P i) := by
  classical
  have hsum (s : Finset (Fin d.m)) : DoublyPeriodic (∑ j ∈ s, rayTail d P i j) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        refine ⟨(1, 0), (0, 1), ?_, ?_, ?_⟩
        · norm_num [Nonparallel, det]
        · intro z; rfl
        · intro z; rfl
    | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        apply doublyPeriodic_add_fields _ _ _ ih
        unfold rayTail
        split
        · exact (d.component j).left_doubly_periodic
        · exact (d.component j).right_doubly_periodic
  exact hsum _

private theorem ray_component_eventually {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (i j : Fin d.m) (hji : j ≠ i) (z : Lattice) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (d.component j).field (z + (n : ℤ) • P.vector i) = rayTail d P i j z := by
  let a := height (d.component j).direction (P.vector i)
  have ha : a ≠ 0 := height_vector_other d P i j hji
  have hnperiod (n : ℕ) : HasPeriod (rayTail d P i j) ((n : ℤ) • P.vector i) :=
    hasPeriod_zsmul _ _ (rayTail_period d P i j i) _
  by_cases hneg : a < 0
  · change height (d.component j).direction (P.vector i) < 0 at hneg
    filter_upwards [Filter.eventually_ge_atTop
      ((height (d.component j).direction z - (d.component j).lower).natAbs + 1)] with n hn
    have hnb : height (d.component j).direction z - (d.component j).lower < (n : ℤ) := by
      have hb : height (d.component j).direction z - (d.component j).lower ≤
          ((height (d.component j).direction z - (d.component j).lower).natAbs : ℤ) := Int.le_natAbs
      exact lt_of_le_of_lt hb (by exact_mod_cast hn)
    have hna : (n : ℤ) * a ≤ -(n : ℤ) := by
      have hmul := mul_le_mul_of_nonneg_left (show a ≤ -1 by omega) (Int.natCast_nonneg n)
      simpa using hmul
    have hheight : height (d.component j).direction (z + (n : ℤ) • P.vector i) <
        (d.component j).lower := by
      rw [height_add, height_zsmul]
      change height (d.component j).direction z + (n : ℤ) * a < _
      omega
    rw [(d.component j).left_agreement _ hheight]
    have hp := hnperiod n z
    simpa only [rayTail, ite_eq_left hneg] using hp
  · change ¬ height (d.component j).direction (P.vector i) < 0 at hneg
    have hpos : 0 < a := lt_of_le_of_ne (le_of_not_gt hneg) ha.symm
    filter_upwards [Filter.eventually_ge_atTop
      (((d.component j).upper - height (d.component j).direction z).natAbs + 1)] with n hn
    have hnb : (d.component j).upper - height (d.component j).direction z < (n : ℤ) := by
      have hb : (d.component j).upper - height (d.component j).direction z ≤
          (((d.component j).upper - height (d.component j).direction z).natAbs : ℤ) := Int.le_natAbs
      exact lt_of_le_of_lt hb (by exact_mod_cast hn)
    have hna : (n : ℤ) ≤ (n : ℤ) * a := by
      have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ a by omega) (Int.natCast_nonneg n)
      simpa using hmul
    have hheight : (d.component j).upper <
        height (d.component j).direction (z + (n : ℤ) • P.vector i) := by
      rw [height_add, height_zsmul]
      change _ < height (d.component j).direction z + (n : ℤ) * a
      omega
    rw [(d.component j).right_agreement _ hheight]
    have hp := hnperiod n z
    simpa only [rayTail, ite_eq_right hneg] using hp

private theorem ray_configuration_eventually {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (i : Fin d.m) (z : Lattice) :
    ∀ᶠ n : ℕ in Filter.atTop,
      d.configuration (z + (n : ℤ) • P.vector i) =
        (d.component i).field z + rayBackground d P i z := by
  classical
  have hj : ∀ j ∈ Finset.univ.erase i, ∀ᶠ n : ℕ in Filter.atTop,
      (d.component j).field (z + (n : ℤ) • P.vector i) = rayTail d P i j z := by
    intro j hj
    exact ray_component_eventually d P i j (Finset.ne_of_mem_erase hj) z
  filter_upwards [(Finset.univ.erase i).eventually_all.mpr hj] with n hn
  have hpi := hasPeriod_zsmul _ _ (P.component_period i) (n : ℤ) z
  change (d.component i).field (z + (n : ℤ) • P.vector i) = (d.component i).field z at hpi
  unfold StarData.configuration rayBackground
  rw [← Finset.add_sum_erase Finset.univ (fun j => (d.component j).field
    (z + (n : ℤ) • P.vector i)) (Finset.mem_univ i), hpi, Finset.sum_apply]
  congr 1
  exact Finset.sum_congr rfl hn

private theorem isolated_ray_identity {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (w : ZMod p → ℤ)
    (hD : ∀ a : ZMod p,
      applyLaurent (starDifference P) (scalarColourIndicator d.configuration a) = 0)
    (i : Fin d.m) :
    isolatedScalarField P (integerScalarEncoding d w) i =
      applyLaurent (starOtherDifference P i)
        (scalarEncoding ((d.component i).field + rayBackground d P i) (fun a => (w a : ℂ))) := by
  classical
  have hp := isolatedScalarField_period d P _ (encoding_killed d P w hD) i
  ext z
  have hev : ∀ u ∈ (starOtherDifference P i).coeff.support,
      ∀ᶠ n : ℕ in Filter.atTop,
      d.configuration (z + u + (n : ℤ) • P.vector i) =
        (d.component i).field (z + u) + rayBackground d P i (z + u) := by
    intro u hu
    exact ray_configuration_eventually d P i _
  obtain ⟨n, hn⟩ := ((starOtherDifference P i).coeff.support.eventually_all.mpr hev).exists
  have hpz := hasPeriod_zsmul _ _ hp (n : ℤ) z
  rw [← hpz]
  change applyLaurent _ _ (z + (n : ℤ) • P.vector i) = _
  unfold applyLaurent
  apply Finset.sum_congr rfl
  intro u hu
  change _ * (w (d.configuration (z + (n : ℤ) • P.vector i + u)) : ℂ) =
    _ * (w ((d.component i).field (z+u) + rayBackground d P i (z+u)) : ℂ)
  rw [add_right_comm, hn u hu]


private theorem applyLaurent_upper_support (q : LaurentPolynomial) (f : ScalarField)
    (v : Lattice) (b : ℤ) (hb : ∀ z, f z ≠ 0 → height v z ≤ b) :
    ∃ r : ℤ, ∀ z, applyLaurent q f z ≠ 0 → height v z ≤ r := by
  let c := q.coeff.support.sup (fun u => (height v u).natAbs)
  refine ⟨b + (c : ℤ), ?_⟩
  intro z hz
  by_contra hbound
  apply hz
  unfold applyLaurent
  apply Finset.sum_eq_zero
  intro u hu
  have hcu : (height v u).natAbs ≤ c := Finset.le_sup (f := fun u => (height v u).natAbs) hu
  have hlow : -(c : ℤ) ≤ height v u := by
    have hn : -height v u ≤ ((height v u).natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -height v u))
    have hcast : ((height v u).natAbs : ℤ) ≤ (c : ℤ) := by exact_mod_cast hcu
    omega
  have hzero : f (z + u) = 0 := by
    by_contra hnon
    have hb' := hb (z+u) hnon
    rw [height_add] at hb'
    omega
  simp [hzero]

private theorem applyLaurent_lower_support (q : LaurentPolynomial) (f : ScalarField)
    (v : Lattice) (b : ℤ) (hb : ∀ z, f z ≠ 0 → b ≤ height v z) :
    ∃ l : ℤ, ∀ z, applyLaurent q f z ≠ 0 → l ≤ height v z := by
  let c := q.coeff.support.sup (fun u => (height v u).natAbs)
  refine ⟨b - (c : ℤ), ?_⟩
  intro z hz
  by_contra hbound
  apply hz
  unfold applyLaurent
  apply Finset.sum_eq_zero
  intro u hu
  have hcu : (height v u).natAbs ≤ c := Finset.le_sup (f := fun u => (height v u).natAbs) hu
  have hhigh : height v u ≤ (c : ℤ) := by
    have hn := Int.le_natAbs (a := height v u)
    have hcast : ((height v u).natAbs : ℤ) ≤ (c : ℤ) := by exact_mod_cast hcu
    omega
  have hzero : f (z + u) = 0 := by
    by_contra hnon
    have hb' := hb (z+u) hnon
    rw [height_add] at hb'
    omega
  simp [hzero]

/-- The scalar pure-tail field is killed by the complementary operator. -/
private theorem otherDifference_kills_pure_tail {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (i : Fin d.m) (G : Configuration (ZMod p))
    (hG : ∀ j, HasPeriod G (P.vector j)) (w : ZMod p → ℤ) :
    applyLaurent (starOtherDifference P i)
      (scalarEncoding (G + rayBackground d P i) (fun a => (w a : ℂ))) = 0 := by
  have hcard : 0 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hm := d.two_le
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  apply differenceProduct_kills_period (Finset.univ.erase i) P.vector j hj
  exact scalar_period_encode _ _
    (hasPeriod_add_fields _ _ _ (hG j) (rayBackground_period d P i j)) _

 theorem lemma_4_1 {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (w : ZMod p → ℤ) (hw : Function.Injective w)
    (hD : ∀ a : ZMod p,
      applyLaurent (starDifference P) (scalarColourIndicator d.configuration a) = 0)
    (i : Fin d.m) :
    (∃ l r : ℤ, ∀ z : Lattice,
      isolatedScalarField P (integerScalarEncoding d w) i z ≠ 0 →
        l ≤ height (d.component i).direction z ∧ height (d.component i).direction z ≤ r) ∧
      isolatedScalarField P (integerScalarEncoding d w) i ≠ 0 := by
  classical
  let B := rayBackground d P i
  let ξ : ScalarField := scalarEncoding ((d.component i).field + B) (fun a => (w a : ℂ))
  let R : ScalarField := scalarEncoding ((d.component i).rightTail + B) (fun a => (w a : ℂ))
  let L : ScalarField := scalarEncoding ((d.component i).leftTail + B) (fun a => (w a : ℂ))
  have hid : isolatedScalarField P (integerScalarEncoding d w) i =
      applyLaurent (starOtherDifference P i) ξ := isolated_ray_identity d P w hD i
  have hR : applyLaurent (starOtherDifference P i) R = 0 :=
    otherDifference_kills_pure_tail d P i _ (fun j => (P.all_tail_periods j i).2) w
  have hL : applyLaurent (starOtherDifference P i) L = 0 :=
    otherDifference_kills_pure_tail d P i _ (fun j => (P.all_tail_periods j i).1) w
  have hidR : isolatedScalarField P (integerScalarEncoding d w) i =
      applyLaurent (starOtherDifference P i) (ξ-R) := by
    rw [applyLaurent_sub_field, hR, sub_zero, ← hid]
  have hidL : isolatedScalarField P (integerScalarEncoding d w) i =
      applyLaurent (starOtherDifference P i) (ξ-L) := by
    rw [applyLaurent_sub_field, hL, sub_zero, ← hid]
  have hupper : ∀ z, (ξ-R) z ≠ 0 → height (d.component i).direction z ≤ (d.component i).upper := by
    intro z hz
    by_contra hb
    have hagree := (d.component i).right_agreement z (lt_of_not_ge hb)
    exact hz (by simp [ξ, R, scalarEncoding, hagree])
  have hlower : ∀ z, (ξ-L) z ≠ 0 → (d.component i).lower ≤ height (d.component i).direction z := by
    intro z hz
    by_contra hb
    have hagree := (d.component i).left_agreement z (lt_of_not_ge hb)
    exact hz (by simp [ξ, L, scalarEncoding, hagree])
  obtain ⟨r, hr⟩ := applyLaurent_upper_support (starOtherDifference P i) (ξ-R) _ _ hupper
  obtain ⟨l, hl⟩ := applyLaurent_lower_support (starOtherDifference P i) (ξ-L) _ _ hlower
  refine ⟨⟨l, r, ?_⟩, ?_⟩
  · intro z hz
    exact ⟨hl z (by rwa [← hidL]), hr z (by rwa [← hidR])⟩
  · rw [hidR]
    apply differenceProduct_nonzero_of_upper_support (Finset.univ.erase i) P.vector
      (d.component i).direction (ξ-R) ?_ ?_ (d.component i).upper hupper
    · intro j hj
      exact height_vector_other d P j i (Finset.ne_of_mem_erase hj).symm
    · intro hzero
      have heq : (d.component i).field = (d.component i).rightTail := by
        ext z
        have he := congrFun hzero z
        change (w ((d.component i).field z+B z) : ℂ) -
          (w ((d.component i).rightTail z+B z) : ℂ) = 0 at he
        have hew := hw (Int.cast_injective (α := ℂ) (sub_eq_zero.mp he))
        exact add_right_cancel hew
      exact (d.component i).not_doubly_periodic (heq.symm ▸ (d.component i).right_doubly_periodic)

end
end ConvexNivat
