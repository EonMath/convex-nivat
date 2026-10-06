import NivatTrial.KariMoutot
import NivatTrial.ModularReduction

/-!
# Period directions under an independent-difference annihilator

An observed finite-alphabet configuration with a product-difference
annihilator can have a global period transverse to every factor only if it
is doubly periodic. We pass the integer annihilator to a faithful finite
cyclic alphabet, where the full-plane finite-state recurrence applies.
-/

namespace NivatTrial.CollePeriodDirections

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.Dynamics
open NivatTrial.ExternalInputs NivatTrial.ModularReduction

open scoped Classical
noncomputable section

def determinantHeight (u : Lattice) : Lattice →+ ℤ where
  toFun := det u
  map_zero' := det_zero_right u
  map_add' := det_add_right u

@[simp] theorem determinantHeight_apply (u z : Lattice) :
    determinantHeight u z = det u z := rfl

@[simp] theorem determinantHeight_self (u : Lattice) :
    determinantHeight u u = 0 := det_self u

theorem cast_iteratedIncrement {M : ℕ} (hs : List Lattice)
    (f : Lattice → ℤ) :
    iteratedIncrement hs (fun z => (f z : ZMod (M+1))) =
      fun z => ((iteratedIncrement (A := ℤ) hs f z : ℤ) : ZMod (M+1)) := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    rw [iteratedIncrement_cons, iteratedIncrement_cons, ih]
    funext z
    simp only [increment, Int.cast_sub]

/-- An integer product relation remains an exact relation after faithful
finite cyclic coding. No primality assumption on the modulus is used. -/
theorem modCode_annihilated {M : ℕ} (θ : Lattice → Fin M)
    (hs : List Lattice)
    (hann : iteratedIncrement hs (integerField θ) = 0) :
    iteratedIncrement hs (encode modCode θ) = 0 := by
  have hcode : (fun z => (integerField θ z : ZMod (M+1))) =
      encode modCode θ := by
    funext z
    exact cast_integerField θ z
  rw [← hcode, cast_iteratedIncrement]
  funext z
  have hz := congrFun hann z
  simpa only [Pi.zero_apply, Int.cast_zero] using
    congrArg (fun a : ℤ => (a : ZMod (M+1))) hz

/-- A period transverse to all factors forces two independent periods of
the finite alphabet itself. -/
theorem doublyPeriodic_of_transverse_period {M : ℕ}
    (θ : Lattice → Fin M) (hs : List Lattice)
    (hann : iteratedIncrement hs (integerField θ) = 0)
    (u : Lattice) (hu : u ≠ 0) (hperiod : IsPeriod θ u)
    (htrans : ∀ h ∈ hs, det u h ≠ 0) : IsDoublyPeriodic θ := by
  have hmod := modCode_annihilated θ hs hann
  have hperiodMod : IsPeriod (encode modCode θ) u := hperiod.encode modCode
  have hdp := doublyPeriodic_of_iteratedIncrement
    (determinantHeight u) u hu (determinantHeight_self u)
    hs (fun h hh => htrans h hh) (encode modCode θ) hperiodMod hmod
  obtain ⟨a, b, hab, hpa, hpb⟩ := hdp
  exact ⟨a, b, hab,
    (isPeriod_encode_iff (modCode_injective M) θ a).mp hpa,
    (isPeriod_encode_iff (modCode_injective M) θ b).mp hpb⟩

/-- Every nonzero period of a non-doubly-periodic configuration runs parallel
to at least one factor of an integer product annihilator. -/
theorem period_parallel_to_factor {M : ℕ}
    (θ : Lattice → Fin M) (hs : List Lattice)
    (hann : iteratedIncrement hs (integerField θ) = 0)
    (hnotDP : ¬IsDoublyPeriodic θ) (u : Lattice) (hu : u ≠ 0)
    (hperiod : IsPeriod θ u) :
    ∃ h ∈ hs, det u h = 0 := by
  by_contra hno
  have htrans : ∀ h ∈ hs, det u h ≠ 0 := by
    intro h hh hz
    exact hno ⟨h, hh, hz⟩
  exact hnotDP (doublyPeriodic_of_transverse_period θ hs hann u hu hperiod htrans)

theorem period_parallel_to_factor_of_aperiodic {M : ℕ}
    (θ : Lattice → Fin M) (hs : List Lattice)
    (hann : iteratedIncrement hs (integerField θ) = 0)
    (hnot : ¬IsPeriodic θ) (u : Lattice) (hu : u ≠ 0)
    (hperiod : IsPeriod θ u) :
    ∃ h ∈ hs, det u h = 0 :=
  period_parallel_to_factor θ hs hann
    (fun hdp => hnot hdp.isPeriodic) u hu hperiod

end
end NivatTrial.CollePeriodDirections
