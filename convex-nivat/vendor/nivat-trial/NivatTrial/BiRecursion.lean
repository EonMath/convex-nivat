import NivatTrial.Witness

/-! The two finite recursions of Lemma 5.1, with the periodic-background
conclusion of Proposition 3.3 supplied explicitly. -/

namespace NivatTrial.BiRecursion

open NivatTrial.Algebra NivatTrial.Differences NivatTrial.Quadratic

noncomputable section

/-- Multiplication by a background preserved by every difference direction
commutes with the product of finite differences. -/
theorem action_mul_periodic_right {ι : Type*} (s : Finset ι) (H : ι → G)
    (η B : G → ℂ) (hB : ∀ i ∈ s, ∀ z, B (z + H i) = B z) :
    act (differenceProduct s H) (fun z => η z * B z) =
      fun z => act (differenceProduct s H) η z * B z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hBs : ∀ j ∈ s, ∀ z, B (z + H j) = B z :=
      fun j hj => hB j (Finset.mem_insert_of_mem hj)
    have hBi := hB i (Finset.mem_insert_self i s)
    rw [differenceProduct_insert s H hi, act_mul, ih hBs]
    funext z
    simp only [act_mul, act_difference, hBi]
    ring

theorem action_mul_periodic_left {ι : Type*} (s : Finset ι) (H : ι → G)
    (η B : G → ℂ) (hB : ∀ i ∈ s, ∀ z, B (z + H i) = B z) :
    act (differenceProduct s H) (fun z => B z * η z) =
      fun z => B z * act (differenceProduct s H) η z := by
  simpa only [mul_comm] using action_mul_periodic_right s H η B hB

theorem shifted_background_period {ι : Type*} (s : Finset ι) (H : ι → G)
    (B : G → ℂ) (hB : ∀ i ∈ s, ∀ z, B (z + H i) = B z) (d : G) :
    ∀ i ∈ s, ∀ z, B (z + H i + d) = B (z + d) := by
  intro i hi z
  simpa only [add_assoc, add_comm, add_left_comm] using hB i hi (z + d)

def witness (D : Laurent) (η : G → ℂ) (d z : G) : ℂ :=
  act D (twoPoint η 0 d) z

/-- Apply a Laurent polynomial to the displacement variable. -/
def displacementAction (A : Laurent) (J : G → G → ℂ) (d z : G) : ℂ :=
  A.coeff.sum fun s c => c * J (d + s) z

/-- Move the first observation point while keeping the second fixed. -/
def diagonalAction (A : Laurent) (J : G → G → ℂ) (d z : G) : ℂ :=
  A.coeff.sum fun s c => c * J (d - s) (z + s)

theorem displacement_identity (A D : Laurent) (η : G → ℂ) (d z : G) :
    displacementAction A (witness D η) d z =
      act D (fun x => η x * act A η (x + d)) z := by
  simp only [displacementAction, witness, act, twoPoint, add_zero, Finsupp.sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro s _
  simp only [add_assoc]
  ring

theorem diagonal_identity (A D : Laurent) (η : G → ℂ) (d z : G) :
    diagonalAction A (witness D η) d z =
      act D (fun x => act A η x * η (x + d)) z := by
  simp only [diagonalAction, witness, act, twoPoint, add_zero, Finsupp.sum,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro s _
  have h₁ : z + s + u = z + u + s := by abel
  have h₂ : z + s + u + (d - s) = z + u + d := by abel
  rw [h₂, h₁]
  ring

/-- First identity of Lemma 5.1. -/
theorem displacement_recursion {ι : Type*} (s : Finset ι) (H : ι → G)
    (A : Laurent) (η B : G → ℂ)
    (hA : act A η = B) (hη : act (differenceProduct s H) η = 0)
    (hB : ∀ i ∈ s, ∀ z, B (z + H i) = B z) (d z : G) :
    displacementAction A (witness (differenceProduct s H) η) d z = 0 := by
  rw [displacement_identity, hA]
  have hp : ∀ i ∈ s, ∀ z, (fun x => B (x + d)) (z + H i) =
      (fun x => B (x + d)) z := shifted_background_period s H B hB d
  rw [action_mul_periodic_right s H η (fun x => B (x + d)) hp, hη]
  simp

/-- Second identity of Lemma 5.1. -/
theorem diagonal_recursion {ι : Type*} (s : Finset ι) (H : ι → G)
    (A : Laurent) (η B : G → ℂ)
    (hA : act A η = B) (hη : act (differenceProduct s H) η = 0)
    (hB : ∀ i ∈ s, ∀ z, B (z + H i) = B z) (d z : G) :
    diagonalAction A (witness (differenceProduct s H) η) d z = 0 := by
  rw [diagonal_identity, hA]
  rw [action_mul_periodic_left s H (fun x => η (x + d)) B hB]
  change B z * act (differenceProduct s H) (fun x => η (x + d)) z = 0
  rw [act_translate, hη]
  simp

/-- Both recursions use the same polynomial and the same witness. -/
theorem bi_recursion {ι : Type*} (s : Finset ι) (H : ι → G)
    (A : Laurent) (η B : G → ℂ)
    (hA : act A η = B) (hη : act (differenceProduct s H) η = 0)
    (hB : ∀ i ∈ s, ∀ z, B (z + H i) = B z) :
    (∀ d z, displacementAction A (witness (differenceProduct s H) η) d z = 0) ∧
    (∀ d z, diagonalAction A (witness (differenceProduct s H) η) d z = 0) := by
  exact ⟨displacement_recursion s H A η B hA hη hB,
    diagonal_recursion s H A η B hA hη hB⟩

end

end NivatTrial.BiRecursion
