import NivatTrial.Algebra
import Mathlib.Data.Int.LeastGreatest

/-!
# Laurent actions on one-sided integer sequences

This file proves the extremal-support argument used in Lemma 2.3. The
configuration can have infinite support: only one end of its support is bounded.
-/

namespace NivatTrial.OneSided

abbrev Laurent1 := AddMonoidAlgebra ℂ ℤ
abbrev Sequence := ℤ → ℂ

noncomputable section

def act (f : Laurent1) (J : Sequence) (t : ℤ) : ℂ :=
  f.coeff.sum fun u c => c * J (t + u)

def UpperSupport (J : Sequence) : Prop :=
  ∃ c : ℤ, ∀ t : ℤ, c < t → J t = 0

def LowerSupport (J : Sequence) : Prop :=
  ∃ c : ℤ, ∀ t : ℤ, t < c → J t = 0

theorem exists_nonzero {J : Sequence} (hJ : J ≠ 0) : ∃ t, J t ≠ 0 := by
  by_contra h
  apply hJ
  funext t
  simpa using not_exists.mp h t

theorem exists_last {J : Sequence} (hJ : J ≠ 0) (hupper : UpperSupport J) :
    ∃ t, J t ≠ 0 ∧ ∀ u, J u ≠ 0 → u ≤ t := by
  obtain ⟨c, hc⟩ := hupper
  apply Int.exists_greatest_of_bdd
  · exact ⟨c, fun t ht => le_of_not_gt fun h => ht (hc t h)⟩
  · exact exists_nonzero hJ

theorem exists_first {J : Sequence} (hJ : J ≠ 0) (hlower : LowerSupport J) :
    ∃ t, J t ≠ 0 ∧ ∀ u, J u ≠ 0 → t ≤ u := by
  obtain ⟨c, hc⟩ := hlower
  apply Int.exists_least_of_bdd
  · exact ⟨c, fun t ht => le_of_not_gt fun h => ht (hc t h)⟩
  · exact exists_nonzero hJ

@[simp] theorem act_zero (J : Sequence) : act 0 J = 0 := by
  funext t
  simp [act]

@[simp] theorem act_zero_sequence (f : Laurent1) : act f 0 = 0 := by
  funext t
  simp [act]

@[simp] theorem act_single (u : ℤ) (c : ℂ) (J : Sequence) (t : ℤ) :
    act (AddMonoidAlgebra.single u c) J t = c * J (t + u) := by
  simp only [act, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index, zero_mul]

theorem act_add (f g : Laurent1) (J : Sequence) :
    act (f + g) J = act f J + act g J := by
  funext t
  simp [act, Finsupp.sum_add_index, add_mul]

theorem act_sub (f g : Laurent1) (J : Sequence) :
    act (f - g) J = act f J - act g J := by
  funext t
  simp [act, Finsupp.sum_sub_index, sub_mul]

theorem act_add_sequence (f : Laurent1) (J K : Sequence) :
    act f (J + K) = act f J + act f K := by
  funext t
  simp [act, Finsupp.sum_add, mul_add]

theorem act_sub_sequence (f : Laurent1) (J K : Sequence) :
    act f (J - K) = act f J - act f K := by
  funext t
  simp [act, Finsupp.sum_sub, mul_sub]

theorem act_mul (f g : Laurent1) (J : Sequence) :
    act (f * g) J = act f (act g J) := by
  funext t
  simp [act, AddMonoidAlgebra.mul_def, Finsupp.sum_sum_index,
    Finsupp.mul_sum, add_mul, mul_assoc, add_assoc,
    -LaurentPolynomial.single_eq_C_mul_T]

theorem act_comm (f g : Laurent1) (J : Sequence) :
    act f (act g J) = act g (act f J) := by
  rw [← act_mul, ← act_mul, mul_comm]

theorem upperSupport_zero : UpperSupport 0 := by
  exact ⟨0, by simp⟩

theorem lowerSupport_zero : LowerSupport 0 := by
  exact ⟨0, by simp⟩

theorem UpperSupport.add {J K : Sequence}
    (hJ : UpperSupport J) (hK : UpperSupport K) : UpperSupport (J + K) := by
  obtain ⟨c, hc⟩ := hJ
  obtain ⟨d, hd⟩ := hK
  refine ⟨max c d, fun t ht => ?_⟩
  simp [hc t (lt_of_le_of_lt (le_max_left c d) ht),
    hd t (lt_of_le_of_lt (le_max_right c d) ht)]

theorem LowerSupport.add {J K : Sequence}
    (hJ : LowerSupport J) (hK : LowerSupport K) : LowerSupport (J + K) := by
  obtain ⟨c, hc⟩ := hJ
  obtain ⟨d, hd⟩ := hK
  refine ⟨min c d, fun t ht => ?_⟩
  simp [hc t (lt_of_lt_of_le ht (min_le_left c d)),
    hd t (lt_of_lt_of_le ht (min_le_right c d))]

theorem UpperSupport.neg {J : Sequence} (hJ : UpperSupport J) : UpperSupport (-J) := by
  obtain ⟨c, hc⟩ := hJ
  exact ⟨c, by simpa using hc⟩

theorem LowerSupport.neg {J : Sequence} (hJ : LowerSupport J) : LowerSupport (-J) := by
  obtain ⟨c, hc⟩ := hJ
  exact ⟨c, by simpa using hc⟩

theorem UpperSupport.sub {J K : Sequence}
    (hJ : UpperSupport J) (hK : UpperSupport K) : UpperSupport (J - K) := by
  simpa only [sub_eq_add_neg] using hJ.add hK.neg

theorem LowerSupport.sub {J K : Sequence}
    (hJ : LowerSupport J) (hK : LowerSupport K) : LowerSupport (J - K) := by
  simpa only [sub_eq_add_neg] using hJ.add hK.neg

theorem UpperSupport.shift {J : Sequence} (hJ : UpperSupport J) (u : ℤ) :
    UpperSupport (fun t => J (t + u)) := by
  obtain ⟨c, hc⟩ := hJ
  refine ⟨c - u, fun t ht => hc (t + u) ?_⟩
  omega

theorem LowerSupport.shift {J : Sequence} (hJ : LowerSupport J) (u : ℤ) :
    LowerSupport (fun t => J (t + u)) := by
  obtain ⟨c, hc⟩ := hJ
  refine ⟨c - u, fun t ht => hc (t + u) ?_⟩
  omega

theorem upperSupport_reflect_iff (J : Sequence) :
    UpperSupport (fun t => J (-t)) ↔ LowerSupport J := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨-c, fun t ht => ?_⟩
    simpa using hc (-t) (by omega)
  · rintro ⟨c, hc⟩
    refine ⟨-c, fun t ht => hc (-t) ?_⟩
    omega

theorem lowerSupport_reflect_iff (J : Sequence) :
    LowerSupport (fun t => J (-t)) ↔ UpperSupport J := by
  simpa using (upperSupport_reflect_iff (fun t => J (-t))).symm

/-- At the last nonzero row, the smallest exponent is the unique contribution. -/
theorem act_at_last (f : Laurent1) (J : Sequence) (t b : ℤ)
    (hb : b ∈ f.coeff.support) (hmin : ∀ u ∈ f.coeff.support, b ≤ u)
    (hlast : ∀ u, t < u → J u = 0) :
    act f J (t - b) = f.coeff b * J t := by
  classical
  unfold act Finsupp.sum
  rw [Finset.sum_eq_single b]
  · simp
  · intro u hu hne
    have hbu := hmin u hu
    change f.coeff u * J (t - b + u) = 0
    rw [hlast (t - b + u) (by omega), mul_zero]
  · exact fun h => (h hb).elim

/-- At the first nonzero row, the largest exponent is the unique contribution. -/
theorem act_at_first (f : Laurent1) (J : Sequence) (t b : ℤ)
    (hb : b ∈ f.coeff.support) (hmax : ∀ u ∈ f.coeff.support, u ≤ b)
    (hfirst : ∀ u, u < t → J u = 0) :
    act f J (t - b) = f.coeff b * J t := by
  classical
  unfold act Finsupp.sum
  rw [Finset.sum_eq_single b]
  · simp
  · intro u hu hne
    have hub := hmax u hu
    change f.coeff u * J (t - b + u) = 0
    rw [hfirst (t - b + u) (by omega), mul_zero]
  · exact fun h => (h hb).elim

theorem act_ne_zero_of_upperSupport {f : Laurent1} {J : Sequence}
    (hf : f ≠ 0) (hJ : J ≠ 0) (hupper : UpperSupport J) : act f J ≠ 0 := by
  classical
  obtain ⟨t, ht, hlast⟩ := exists_last hJ hupper
  have hs : f.coeff.support.Nonempty := by
    simpa only [Finsupp.support_nonempty_iff, ne_eq, AddMonoidAlgebra.coeff_eq_zero] using hf
  let b := f.coeff.support.min' hs
  have hb : b ∈ f.coeff.support := Finset.min'_mem _ _
  have hmin : ∀ u ∈ f.coeff.support, b ≤ u := fun u hu => Finset.min'_le _ u hu
  intro h
  have hvalue := congrArg (fun K : Sequence => K (t - b)) h
  rw [act_at_last f J t b hb hmin] at hvalue
  · exact mul_ne_zero (Finsupp.mem_support_iff.mp hb) ht hvalue
  · intro u hu
    by_contra hne
    exact not_le_of_gt hu (hlast u hne)

theorem act_ne_zero_of_lowerSupport {f : Laurent1} {J : Sequence}
    (hf : f ≠ 0) (hJ : J ≠ 0) (hlower : LowerSupport J) : act f J ≠ 0 := by
  classical
  obtain ⟨t, ht, hfirst⟩ := exists_first hJ hlower
  have hs : f.coeff.support.Nonempty := by
    simpa only [Finsupp.support_nonempty_iff, ne_eq, AddMonoidAlgebra.coeff_eq_zero] using hf
  let b := f.coeff.support.max' hs
  have hb : b ∈ f.coeff.support := Finset.max'_mem _ _
  have hmax : ∀ u ∈ f.coeff.support, u ≤ b := fun u hu => Finset.le_max' _ u hu
  intro h
  have hvalue := congrArg (fun K : Sequence => K (t - b)) h
  rw [act_at_first f J t b hb hmax] at hvalue
  · exact mul_ne_zero (Finsupp.mem_support_iff.mp hb) ht hvalue
  · intro u hu
    by_contra hne
    exact not_le_of_gt hu (hfirst u hne)

theorem eq_zero_of_annihilates_upperSupport {f : Laurent1} {J : Sequence}
    (hJ : J ≠ 0) (hupper : UpperSupport J) (hact : act f J = 0) : f = 0 := by
  by_contra hf
  exact act_ne_zero_of_upperSupport hf hJ hupper hact

theorem eq_zero_of_annihilates_lowerSupport {f : Laurent1} {J : Sequence}
    (hJ : J ≠ 0) (hlower : LowerSupport J) (hact : act f J = 0) : f = 0 := by
  by_contra hf
  exact act_ne_zero_of_lowerSupport hf hJ hlower hact

theorem injective_on_upperSupport {f : Laurent1} (hf : f ≠ 0)
    {J K : Sequence} (hJ : UpperSupport J) (hK : UpperSupport K)
    (hact : act f J = act f K) : J = K := by
  have hzero : act f (J - K) = 0 := by rw [act_sub_sequence, hact, sub_self]
  by_contra hne
  exact act_ne_zero_of_upperSupport hf (sub_ne_zero.mpr hne) (hJ.sub hK) hzero

theorem injective_on_lowerSupport {f : Laurent1} (hf : f ≠ 0)
    {J K : Sequence} (hJ : LowerSupport J) (hK : LowerSupport K)
    (hact : act f J = act f K) : J = K := by
  have hzero : act f (J - K) = 0 := by rw [act_sub_sequence, hact, sub_self]
  by_contra hne
  exact act_ne_zero_of_lowerSupport hf (sub_ne_zero.mpr hne) (hJ.sub hK) hzero

end

end NivatTrial.OneSided
