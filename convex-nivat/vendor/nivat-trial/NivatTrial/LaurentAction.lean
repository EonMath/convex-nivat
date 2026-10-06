import NivatTrial.Algebra
import NivatTrial.Patterns

/-! Laurent actions with variable coefficient ring, needed for the integer,
rational and finite-characteristic stages of the external decomposition proof. -/

namespace NivatTrial.LaurentAction

open scoped Classical
noncomputable section

abbrev RingLaurent (R : Type*) [Semiring R] := AddMonoidAlgebra R Lattice

variable {R : Type*} [CommRing R]

def act (f : RingLaurent R) (x : Lattice → R) (z : Lattice) : R :=
  f.coeff.sum fun u c => c * x (z + u)

@[simp] theorem act_zero (x : Lattice → R) : act 0 x = 0 := by
  funext z
  simp [act]

@[simp] theorem act_zero_config (f : RingLaurent R) : act f 0 = 0 := by
  funext z
  simp [act]

@[simp] theorem act_single (u : Lattice) (c : R) (x : Lattice → R) (z : Lattice) :
    act (AddMonoidAlgebra.single u c) x z = c * x (z + u) := by
  simp [act]

@[simp] theorem act_one (x : Lattice → R) : act 1 x = x := by
  funext z
  simp [act, AddMonoidAlgebra.one_def]

theorem act_add (f g : RingLaurent R) (x : Lattice → R) :
    act (f + g) x = act f x + act g x := by
  funext z
  simp [act, Finsupp.sum_add_index, add_mul]

theorem act_sub (f g : RingLaurent R) (x : Lattice → R) :
    act (f - g) x = act f x - act g x := by
  funext z
  simp [act, Finsupp.sum_sub_index, sub_mul]

theorem act_add_config (f : RingLaurent R) (x y : Lattice → R) :
    act f (x + y) = act f x + act f y := by
  funext z
  simp [act, mul_add, Finsupp.sum_add]

theorem act_mul (f g : RingLaurent R) (x : Lattice → R) :
    act (f * g) x = act f (act g x) := by
  funext z
  simp [act, AddMonoidAlgebra.mul_def, Finsupp.sum_sum_index,
    Finsupp.mul_sum, -Finsupp.single_mul, add_mul, mul_assoc, add_assoc]

theorem act_comm (f g : RingLaurent R) (x : Lattice → R) :
    act f (act g x) = act g (act f x) := by
  rw [← act_mul, ← act_mul, mul_comm]

theorem act_sum {ι : Type*} (s : Finset ι) (f : ι → RingLaurent R) (x : Lattice → R) :
    act (∑ i ∈ s, f i) x = ∑ i ∈ s, act (f i) x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, act_add, ih]

def annihilator (x : Lattice → R) : Ideal (RingLaurent R) where
  carrier := {f | act f x = 0}
  zero_mem' := act_zero x
  add_mem' := by
    intro f g hf hg
    change act (f+g) x=0
    rw [act_add, hf, hg, add_zero]
  smul_mem' := by
    intro f g hg
    change act (f*g) x=0
    rw [act_mul, hg, act_zero_config]

@[simp] theorem mem_annihilator (x : Lattice → R) (f : RingLaurent R) :
    f ∈ annihilator x ↔ act f x = 0 := Iff.rfl

theorem act_eq_zero_of_dvd {f g : RingLaurent R} {x : Lattice → R}
    (hfg : f ∣ g) (hf : act f x=0) : act g x=0 := by
  obtain ⟨q,rfl⟩ := hfg
  rw [mul_comm, act_mul, hf, act_zero_config]

theorem act_pow_eq_zero {f : RingLaurent R} {x : Lattice → R}
    (hf : act f x=0) {n : ℕ} (hn : 0<n) : act (f^n) x=0 :=
  act_eq_zero_of_dvd (dvd_pow_self f (Nat.ne_of_gt hn)) hf

def windowPolynomial (S : Finset Lattice) (c : S → R) : RingLaurent R :=
  ∑ s : S, AddMonoidAlgebra.single (s : Lattice) (c s)

@[simp] theorem windowPolynomial_coeff (S : Finset Lattice) (c : S → R) (s : S) :
    (windowPolynomial S c).coeff (s : Lattice) = c s := by
  simp [windowPolynomial, Finsupp.single_apply]

theorem windowPolynomial_ne_zero (S : Finset Lattice) {c : S → R} (hc : c ≠ 0) :
    windowPolynomial S c ≠ 0 := by
  intro h
  apply hc
  funext s
  have hs := congrArg (fun f : RingLaurent R => f.coeff (s : Lattice)) h
  simpa using hs

theorem act_windowPolynomial (S : Finset Lattice) (c : S → R)
    (x : Lattice → R) (z : Lattice) :
    act (windowPolynomial S c) x z = ∑ s : S, c s * x (z+s) := by
  simp [windowPolynomial, act_sum, act_single]

end
end NivatTrial.LaurentAction
