import NivatTrial.PeriodicDifference

/-! One-sided elimination of products of transverse differences over finite
additive groups. The proof integrates differences one factor at a time. -/

namespace NivatTrial.OneSidedRecurrence

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open scoped Classical

variable {A : Type*} [AddCommGroup A]

def iteratedIncrement : List Lattice → (Lattice → A) → Lattice → A
  | [], f => f
  | h :: hs, f => increment (iteratedIncrement hs f) h

@[simp] theorem iteratedIncrement_nil (f : Lattice → A) :
    iteratedIncrement [] f = f := rfl

@[simp] theorem iteratedIncrement_cons (h : Lattice) (hs : List Lattice)
    (f : Lattice → A) : iteratedIncrement (h :: hs) f = increment (iteratedIncrement hs f) h := rfl

theorem increment_commute (f : Lattice → A) (h k : Lattice) :
    increment (increment f h) k = increment (increment f k) h := by
  funext z
  simp only [increment]
  rw [show z + k + h = z + h + k by abel]
  abel

theorem iteratedIncrement_commute (hs : List Lattice) (f : Lattice → A) (h : Lattice) :
    iteratedIncrement hs (increment f h) = increment (iteratedIncrement hs f) h := by
  induction hs with
  | nil => rfl
  | cons k hs ih => rw [iteratedIncrement_cons, ih, increment_commute, iteratedIncrement_cons]

theorem iteratedIncrement_translate (hs : List Lattice) (f : Lattice → A) (h z : Lattice) :
    iteratedIncrement hs (fun x => f (x + h)) z = iteratedIncrement hs f (z + h) := by
  induction hs generalizing z with
  | nil => rfl
  | cons k hs ih =>
    simp only [iteratedIncrement_cons, increment, ih]
    rw [show z + k + h = z + h + k by abel]

theorem iteratedIncrement_neg (hs : List Lattice) (f : Lattice → A) :
    iteratedIncrement hs (-f) = -iteratedIncrement hs f := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext z
    simp only [iteratedIncrement_cons, ih, increment, Pi.neg_apply]
    abel

theorem increment_neg_direction (f : Lattice → A) (h z : Lattice) :
    increment f (-h) z = -increment f h (z - h) := by
  simp [increment, sub_eq_add_neg]

theorem iteratedIncrement_period (hs : List Lattice) {f : Lattice → A} {h : Lattice}
    (hp : IsPeriod f h) : IsPeriod (iteratedIncrement hs f) h := by
  induction hs with
  | nil => exact hp
  | cons k hs ih => exact increment_period ih k

theorem independent_of_height (π : Lattice →+ ℤ) (h d : Lattice)
    (hh : h ≠ 0) (hπh : π h = 0) (hπd : π d ≠ 0) : det h d ≠ 0 := by
  intro hd
  have hz (z : Lattice) : det h z = 0 := by
    have heq := congrArg π (cramer_identity h d z)
    simp only [hd, zero_smul, map_zero, map_add, map_zsmul, hπh,
      smul_eq_mul, mul_zero, zero_add] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_right hπd
  apply hh
  have hx := hz (0, 1)
  have hy := hz (1, 0)
  apply Prod.ext
  · simpa [det] using hx
  · have hy' : -h.2 = 0 := by simpa [det] using hy
    change h.2 = 0
    omega

theorem preserve_heightHalfPlane (π : Lattice →+ ℤ) (c : ℤ) (d : Lattice)
    (hd : 0 ≤ π d) : ∀ z ∈ heightHalfPlane π c, z + d ∈ heightHalfPlane π c := by
  intro z hz
  change c ≤ π (z + d)
  rw [map_add]
  exact le_add_of_nonneg_right hd |>.trans' hz

theorem period_on_of_global (π : Lattice →+ ℤ) (c : ℤ) {f : Lattice → A}
    {h : Lattice} (hp : IsPeriod f h) (hh : 0 ≤ π h) :
    PeriodicOn f (heightHalfPlane π c) h :=
  ⟨preserve_heightHalfPlane π c h hh, fun z _ => hp z⟩

theorem increment_commute_period_on (f : Lattice → A) (d e : Lattice)
    (R : Set Lattice) (hd : ∀ z ∈ R, z + d ∈ R)
    (hp : PeriodicOn (increment f d) R e) : PeriodicOn (increment f e) R d := by
  refine ⟨hd, ?_⟩
  intro z hz
  have h := hp.2 z hz
  dsimp [increment] at h ⊢
  rw [show z + e + d = z + d + e by abel] at h
  apply sub_eq_sub_iff_add_eq_add.mpr
  have hh := sub_eq_sub_iff_add_eq_add.mp h
  convert hh using 1 <;> abel

theorem increment_nsmul_on (f : Lattice → A) (d : Lattice) (R : Set Lattice)
    (hp : PeriodicOn (increment f d) R d) (n : ℕ) (z : Lattice) (hz : z ∈ R) :
    f (z + n • d) = f z + n • increment f d z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (hp.nsmul n).2 z hz
    change f (z + n • d + d) - f (z + n • d) = increment f d z at h
    rw [succ_nsmul, ← add_assoc,
      ← sub_add_cancel (f (z + n • d + d)) (f (z + n • d)), h, ih]
    rw [succ_nsmul]
    abel

theorem period_of_periodic_increment_on [Fintype A] (f : Lattice → A)
    (d : Lattice) (R : Set Lattice) (hp : PeriodicOn (increment f d) R d) :
    PeriodicOn f R (Fintype.card A • d) := by
  refine ⟨(hp.nsmul _).1, ?_⟩
  intro z hz
  simpa using increment_nsmul_on f d R hp (Fintype.card A) z hz

theorem extension_of_positive_period (f : Lattice → A) (π : Lattice →+ ℤ)
    (c : ℤ) (h e : Lattice) (hh : h ≠ 0) (hπh : π h = 0) (hπe : 0 < π e)
    (hfixed : IsPeriod f h) (he : PeriodicOn f (heightHalfPlane π c) e) :
    ∃ η : Lattice → A, (∀ z ∈ heightHalfPlane π c, η z = f z) ∧ IsDoublyPeriodic η := by
  have hd := independent_of_height π h e hh hπh (ne_of_gt hπe)
  obtain ⟨η, ha, _, _, hdp⟩ := doublyPeriodic_extension_of_entry f (heightHalfPlane π c)
    h e hd (period_on_of_global π c hfixed (by omega)) he (by
      intro z
      obtain ⟨N, hN⟩ := positive_direction_enters_halfplane π c (h + e) (by
        rw [map_add, hπh, zero_add]
        exact hπe) z
      exact ⟨N, hN N le_rfl⟩)
  exact ⟨η, ha, hdp⟩

theorem period_on_of_agreement (f η : Lattice → A) (π : Lattice →+ ℤ)
    (c : ℤ) (d : Lattice) (hd : 0 ≤ π d)
    (ha : ∀ z ∈ heightHalfPlane π c, η z = f z) (hp : IsPeriod η d) :
    PeriodicOn f (heightHalfPlane π c) d := by
  have hpres := preserve_heightHalfPlane π c d hd
  refine ⟨hpres, ?_⟩
  intro z hz
  exact (ha (z + d) (hpres z hz)).symm.trans ((hp z).trans (ha z hz))

theorem integrate_increment_on_halfplane [Fintype A] (f : Lattice → A)
    (π : Lattice →+ ℤ) (c : ℤ) (h u d e : Lattice)
    (hh : h ≠ 0) (hπh : π h = 0) (hπu : 0 < π u) (hπd : 0 < π d)
    (hπe : 0 < π e) (hfixed : IsPeriod f h)
    (he : PeriodicOn (increment f d) (heightHalfPlane π c) e) :
    ∃ q : ℕ, 0 < q ∧ PeriodicOn f (heightHalfPlane π c) (q • u) := by
  obtain ⟨η, ha, hη⟩ := extension_of_positive_period (increment f d) π c h e
    hh hπh hπe (increment_period hfixed d) he
  obtain ⟨M, hM, hpM⟩ := direction_period_of_finite_orbit η d
    (finite_orbit_of_doublyPeriodic η hη)
  have hπM : 0 < π (M • d) := by
    rw [map_nsmul, nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast hM) hπd
  have hincM := period_on_of_agreement (increment f d) η π c (M • d) hπM.le ha hpM
  have hcomm := increment_commute_period_on f d (M • d) (heightHalfPlane π c)
    (preserve_heightHalfPlane π c d hπd.le) hincM
  have hperiod := period_of_periodic_increment_on f (M • d) (heightHalfPlane π c)
    (hcomm.nsmul M)
  have hπcard : 0 < π (Fintype.card A • (M • d)) := by
    rw [map_nsmul, nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast Fintype.card_pos) hπM
  obtain ⟨θ, hb, hθ⟩ := extension_of_positive_period f π c h
    (Fintype.card A • (M • d)) hh hπh hπcard hfixed hperiod
  obtain ⟨q, hq, hpq⟩ := direction_period_of_finite_orbit θ u
    (finite_orbit_of_doublyPeriodic θ hθ)
  refine ⟨q, hq, period_on_of_agreement f θ π c (q • u) ?_ hb hpq⟩
  rw [map_nsmul, nsmul_eq_mul]
  exact mul_nonneg (by positivity) hπu.le

/-- A product of transverse differences vanishing on a half-plane forces a
second period on a half-plane, with an explicitly existential boundary. -/
theorem tail_period_of_iteratedIncrement [Fintype A] (π : Lattice →+ ℤ)
    (h u : Lattice) (hh : h ≠ 0) (hπh : π h = 0) (hπu : 0 < π u)
    (hs : List Lattice) (htrans : ∀ d ∈ hs, π d ≠ 0)
    (f : Lattice → A) (hfixed : IsPeriod f h) (c : ℤ)
    (hzero : ∀ z, c ≤ π z → iteratedIncrement hs f z = 0) :
    ∃ b : ℤ, ∃ q : ℕ, 0 < q ∧ PeriodicOn f (heightHalfPlane π b) (q • u) := by
  induction hs generalizing f c with
  | nil =>
    refine ⟨c, 1, by omega, ?_⟩
    rw [one_smul]
    have hpres := preserve_heightHalfPlane π c u hπu.le
    refine ⟨hpres, ?_⟩
    intro z hz
    exact (hzero (z + u) (hpres z hz)).trans (hzero z hz).symm
  | cons d hs ih =>
    have hd : π d ≠ 0 := htrans d (by simp)
    have ht : ∀ e ∈ hs, π e ≠ 0 := fun e he => htrans e (by simp [he])
    have step (e : Lattice) (he : 0 < π e) (c' : ℤ)
        (hz : ∀ z, c' ≤ π z → iteratedIncrement hs (increment f e) z = 0) :
        ∃ b : ℤ, ∃ q : ℕ, 0 < q ∧ PeriodicOn f (heightHalfPlane π b) (q • u) := by
      obtain ⟨b, q, hq, hp⟩ := ih ht (increment f e) (increment_period hfixed e) c' hz
      have hπq : 0 < π (q • u) := by
        rw [map_nsmul, nsmul_eq_mul]
        exact mul_pos (by exact_mod_cast hq) hπu
      obtain ⟨Q, hQ, hper⟩ := integrate_increment_on_halfplane f π b h u e (q • u)
        hh hπh hπu he hπq hfixed hp
      exact ⟨b, Q, hQ, hper⟩
    by_cases hpos : 0 < π d
    · apply step d hpos c
      intro z hz
      rw [iteratedIncrement_commute]
      exact hzero z hz
    · apply step (-d) (by rw [map_neg]; omega) (c + π d)
      intro z hz
      rw [iteratedIncrement_commute, increment_neg_direction]
      have hb : c ≤ π (z - d) := by rw [map_sub]; omega
      have hval := hzero (z - d) hb
      change increment (iteratedIncrement hs f) d (z - d) = 0 at hval
      rw [hval, neg_zero]

/-- The full-plane version of Lemma 8.8. It follows by the same factor
induction and finite-group integration without any boundary changes. -/
theorem doublyPeriodic_of_iteratedIncrement [Fintype A] (π : Lattice →+ ℤ)
    (h : Lattice) (hh : h ≠ 0) (hπh : π h = 0) (hs : List Lattice)
    (htrans : ∀ d ∈ hs, π d ≠ 0) (f : Lattice → A) (hfixed : IsPeriod f h)
    (hzero : iteratedIncrement hs f = 0) : IsDoublyPeriodic f := by
  induction hs generalizing f with
  | nil =>
    have hf : f = 0 := hzero
    rw [hf]
    refine ⟨(1, 0), (0, 1), by norm_num [det], ?_, ?_⟩ <;> intro z <;> rfl
  | cons d hs ih =>
    have hd := independent_of_height π h d hh hπh (htrans d (by simp))
    have ht : ∀ e ∈ hs, π e ≠ 0 := fun e he => htrans e (by simp [he])
    have hz : iteratedIncrement hs (increment f d) = 0 := by
      rw [iteratedIncrement_commute]
      exact hzero
    have hdp := ih ht (increment f d) (increment_period hfixed d) hz
    exact doublyPeriodic_of_increment f h d hfixed hd hdp

@[simp] theorem iteratedIncrement_zero (hs : List Lattice) :
    iteratedIncrement hs (0 : Lattice → A) = 0 := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    rw [iteratedIncrement_cons, ih]
    funext z
    simp [PeriodicDifference.increment]

theorem iteratedIncrement_add (hs : List Lattice) (f g : Lattice → A) :
    iteratedIncrement hs (f + g) = iteratedIncrement hs f + iteratedIncrement hs g := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext z
    simp only [iteratedIncrement_cons, ih, increment, Pi.add_apply]
    abel

theorem iteratedIncrement_sub (hs : List Lattice) (f g : Lattice → A) :
    iteratedIncrement hs (f - g) = iteratedIncrement hs f - iteratedIncrement hs g := by
  rw [sub_eq_add_neg, iteratedIncrement_add, iteratedIncrement_neg, sub_eq_add_neg]

theorem iteratedIncrement_sum {ι : Type*} (s : Finset ι) (f : ι → Lattice → A)
    (hs : List Lattice) :
    iteratedIncrement hs (∑ i ∈ s, f i) = ∑ i ∈ s, iteratedIncrement hs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, iteratedIncrement_add, ih]

theorem factor_kills_of_mem (hs : List Lattice) (h : Lattice) (hh : h ∈ hs)
    (f : Lattice → A) (hp : IsPeriod f h) : iteratedIncrement hs f = 0 := by
  induction hs with
  | nil => simp at hh
  | cons d hs ih =>
    rcases List.mem_cons.mp hh with hhd | hh
    · subst d
      rw [iteratedIncrement_cons]
      funext z
      exact sub_eq_zero.mpr (iteratedIncrement_period hs hp z)
    · rw [iteratedIncrement_cons, ih hh]
      funext z
      simp [PeriodicDifference.increment]

/-- The actual additive endomorphism `T^h - 1`, over any coefficient group. -/
def differenceEnd (h : Lattice) : AddMonoid.End (Lattice → A) where
  toFun f := increment f h
  map_zero' := by funext z; simp [PeriodicDifference.increment]
  map_add' f g := by
    funext z
    simp only [PeriodicDifference.increment, Pi.add_apply]
    abel

@[simp] theorem differenceEnd_apply (h : Lattice) (f : Lattice → A) :
    differenceEnd h f = increment f h := rfl

theorem differenceEnd_commute (h k : Lattice) :
    Commute (differenceEnd (A := A) h) (differenceEnd k) := by
  ext f z
  change increment (increment f k) h z = increment (increment f h) k z
  exact congrFun (increment_commute f k h) z

theorem iteratedIncrement_eq_product (hs : List Lattice) (f : Lattice → A) :
    iteratedIncrement hs f = (hs.map (differenceEnd (A := A))).prod f := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    rw [iteratedIncrement_cons, List.map_cons, List.prod_cons]
    change increment (iteratedIncrement hs f) h = increment ((hs.map differenceEnd).prod f) h
    rw [ih]

theorem iteratedIncrement_perm {hs ks : List Lattice} (hp : hs.Perm ks)
    (f : Lattice → A) : iteratedIncrement hs f = iteratedIncrement ks f := by
  have hc : (hs.map (differenceEnd (A := A))).Pairwise Commute := by
    clear hp
    induction hs with
    | nil => simp
    | cons h hs ih =>
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro e he
      rcases List.mem_map.mp he with ⟨k, _, rfl⟩
      exact differenceEnd_commute h k
  rw [iteratedIncrement_eq_product, iteratedIncrement_eq_product]
  exact congrArg (fun E : AddMonoid.End (Lattice → A) => E f) ((hp.map differenceEnd).prod_eq' hc)

def rowHeight (v u : Lattice) : Lattice →+ ℤ where
  toFun z := det v u * det v z
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

@[simp] theorem rowHeight_apply (v u z : Lattice) :
    rowHeight v u z = det v u * det v z := rfl

@[simp] theorem rowHeight_self (v u : Lattice) : rowHeight v u v = 0 := by simp

theorem rowHeight_basis (v u : Lattice) (hvu : det v u = 1 ∨ det v u = -1) :
    rowHeight v u u = 1 := by
  rcases hvu with hvu | hvu <;> simp [hvu]

theorem basis_vector_ne_zero (v u : Lattice) (hvu : det v u = 1 ∨ det v u = -1) :
    v ≠ 0 := by
  intro hv
  rcases hvu with h | h <;> simp [hv, det] at h

/-- Lemma 8.8 in the original integer-basis coordinates. This version allows
the boundary to shrink by an existential amount, as sufficient for 8.9. -/
theorem lemma8_8 [Fintype A] (f : Lattice → A) (v u : Lattice)
    (hvu : det v u = 1 ∨ det v u = -1) (k : ℕ) (hk : 0 < k)
    (hfixed : IsPeriod f (k • v)) (hs : List Lattice)
    (htrans : ∀ d ∈ hs, rowHeight v u d ≠ 0) (c : ℤ)
    (hzero : ∀ z, c ≤ rowHeight v u z → iteratedIncrement hs f z = 0) :
    ∃ b : ℤ, ∃ q : ℕ, 0 < q ∧
      PeriodicOn f (heightHalfPlane (rowHeight v u) b) (k • v) ∧
      PeriodicOn f (heightHalfPlane (rowHeight v u) b) (q • u) ∧
      det (k • v) (q • u) ≠ 0 := by
  have hh := nsmul_lattice_ne_zero (basis_vector_ne_zero v u hvu) hk
  have hπh : rowHeight v u (k • v) = 0 := by
    rw [map_nsmul, rowHeight_self, nsmul_zero]
  have hπu : 0 < rowHeight v u u := by rw [rowHeight_basis v u hvu]; omega
  obtain ⟨b, q, hq, hp⟩ := tail_period_of_iteratedIncrement (rowHeight v u)
    (k • v) u hh hπh hπu hs htrans f hfixed c hzero
  refine ⟨b, q, hq, period_on_of_global _ b hfixed (by omega), hp, ?_⟩
  apply independent_of_height (rowHeight v u) (k • v) (q • u) hh hπh
  rw [map_nsmul, nsmul_eq_mul]
  exact ne_of_gt (mul_pos (by exact_mod_cast hq) hπu)

theorem lemma8_8_global [Fintype A] (f : Lattice → A) (v u : Lattice)
    (hvu : det v u = 1 ∨ det v u = -1) (k : ℕ) (hk : 0 < k)
    (hfixed : IsPeriod f (k • v)) (hs : List Lattice)
    (htrans : ∀ d ∈ hs, rowHeight v u d ≠ 0)
    (hzero : iteratedIncrement hs f = 0) : IsDoublyPeriodic f := by
  apply doublyPeriodic_of_iteratedIncrement (rowHeight v u) (k • v)
    (nsmul_lattice_ne_zero (basis_vector_ne_zero v u hvu) hk) _ hs htrans f hfixed hzero
  rw [map_nsmul, rowHeight_self, nsmul_zero]

end NivatTrial.OneSidedRecurrence
