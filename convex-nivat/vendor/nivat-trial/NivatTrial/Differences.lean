import NivatTrial.Algebra

namespace NivatTrial.Differences

open NivatTrial.Algebra

noncomputable section

@[simp] theorem act_one (J : G → ℂ) : act 1 J = J := by
  funext z
  change act (AddMonoidAlgebra.single 0 1) J z = J z
  simp

/-- The formal difference `T^h - 1`. -/
def difference (h : G) : Laurent := AddMonoidAlgebra.single h 1 - 1

@[simp] theorem act_difference (h : G) (J : G → ℂ) (z : G) :
    act (difference h) J z = J (z + h) - J z := by
  simp [difference, act_sub]

theorem difference_ne_zero {h : G} (hh : h ≠ 0) : difference h ≠ 0 := by
  intro heq
  have hsingle : (AddMonoidAlgebra.single h 1 : Laurent) =
      AddMonoidAlgebra.single 0 1 := sub_eq_zero.mp heq
  exact hh ((AddMonoidAlgebra.single_left_inj (one_ne_zero : (1 : ℂ) ≠ 0)).mp hsingle)

@[simp] theorem difference_const (h : G) (b : ℂ) :
    act (difference h) (fun _ => b) = 0 := by
  funext z
  simp

theorem difference_eq_zero_of_period (h : G) (J : G → ℂ)
    (hp : ∀ z, J (z + h) = J z) : act (difference h) J = 0 := by
  funext z
  simp [hp]

theorem period_of_difference_eq_zero (h : G) (J : G → ℂ)
    (hp : act (difference h) J = 0) : ∀ z, J (z + h) = J z := by
  intro z
  have hz := congrFun hp z
  simpa only [act_difference, Pi.zero_apply, sub_eq_zero] using hz

/-- A finite product of commuting differences. -/
def differenceProduct {ι : Type*} (s : Finset ι) (H : ι → G) : Laurent :=
  ∏ i ∈ s, difference (H i)

@[simp] theorem differenceProduct_empty {ι : Type*} (H : ι → G) :
    differenceProduct ∅ H = 1 := by simp [differenceProduct]

theorem differenceProduct_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (H : ι → G) {i : ι} (hi : i ∉ s) :
    differenceProduct (insert i s) H = difference (H i) * differenceProduct s H := by
  simp [differenceProduct, hi]

theorem differenceProduct_ne_zero {ι : Type*} (s : Finset ι) (H : ι → G)
    (hH : ∀ i ∈ s, H i ≠ 0) : differenceProduct s H ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => difference_ne_zero (hH i hi))

theorem differenceProduct_factor {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → G) {i : ι} (hi : i ∈ s) :
    differenceProduct s H = differenceProduct (s.erase i) H * difference (H i) := by
  exact (Finset.prod_erase_mul s (fun j => difference (H j)) hi).symm

theorem differenceProduct_const {ι : Type*} (s : Finset ι) (H : ι → G)
    (hs : s.Nonempty) (b : ℂ) : act (differenceProduct s H) (fun _ => b) = 0 := by
  classical
  obtain ⟨i, hi⟩ := hs
  rw [differenceProduct_factor s H hi, act_mul, difference_const, act_zero_config]

/-- Only values on the cofactor's finite support are needed to cancel a difference. -/
theorem act_mul_difference_eq_zero_at (Q : Laurent) (h : G) (J : G → ℂ) (z : G)
    (hp : ∀ u ∈ Q.coeff.support, J (z + u + h) = J (z + u)) :
    act (Q * difference h) J z = 0 := by
  rw [act_mul]
  change ∑ u ∈ Q.coeff.support, Q.coeff u *
    act (difference h) J (z + u) = 0
  apply Finset.sum_eq_zero
  intro u hu
  simp only [act_difference, hp u hu, sub_self, mul_zero]

/-- Differencing commutes with every translation. -/
theorem act_translate (f : Laurent) (J : G → ℂ) (h z : G) :
    act f (fun x => J (x + h)) z = act f J (z + h) := by
  simp [act, add_comm, add_left_comm]

/-- A finite difference of a periodic observation is zero, even when the other
factors have arbitrary directions. -/
theorem differenceProduct_eq_zero_of_period {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → G) {i : ι} (hi : i ∈ s) (J : G → ℂ)
    (hp : ∀ z, J (z + H i) = J z) : act (differenceProduct s H) J = 0 := by
  rw [differenceProduct_factor s H hi, act_mul,
    difference_eq_zero_of_period (H i) J hp, act_zero_config]

end

end NivatTrial.Differences
