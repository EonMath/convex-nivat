import NivatTrial.ExternalInputs

/-! Faithful finite cyclic encoding of the integer colours and their components.
The internal proofs work over finite additive groups, so primality is unnecessary. -/

namespace NivatTrial.ModularReduction

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.Dynamics
open NivatTrial.ExternalInputs

noncomputable section

def modCode {M : ℕ} (a : Fin M) : ZMod (M+1) := ((a.val+1 : ℕ) : ZMod (M+1))

theorem modCode_injective (M : ℕ) : Function.Injective (@modCode M) := by
  intro a b hab
  have hv := congrArg ZMod.val hab
  simp only [modCode, ZMod.val_cast_of_lt (Nat.succ_lt_succ a.isLt),
    ZMod.val_cast_of_lt (Nat.succ_lt_succ b.isLt)] at hv
  apply Fin.ext
  omega

theorem cast_integerCode {M : ℕ} (a : Fin M) :
    (integerCode a : ZMod (M+1)) = modCode a := by
  simp [integerCode, modCode]

theorem cast_integerField {M : ℕ} (θ : Lattice → Fin M) (z : Lattice) :
    (integerField θ z : ZMod (M+1)) = encode modCode θ z := cast_integerCode _

def modularComponent {M n : ℕ} {θ : Lattice → Fin M}
    (D : IntegerDecomposition (integerField θ) n) (i : Fin n) : Lattice → ZMod (M+1) :=
  fun z => (D.component i z : ZMod (M+1))

theorem modularComponent_period {M n : ℕ} {θ : Lattice → Fin M}
    (D : IntegerDecomposition (integerField θ) n) (i : Fin n) :
    IsPeriod (modularComponent D i) (D.period i) := by
  intro z
  exact congrArg (fun x : ℤ => (x : ZMod (M+1))) (D.component_period i z)

theorem modularComponent_sum {M n : ℕ} {θ : Lattice → Fin M}
    (D : IntegerDecomposition (integerField θ) n) :
    (∑ i,modularComponent D i) = encode modCode θ := by
  funext z
  have hz := congrArg (fun f : Lattice → ℤ => (f z : ZMod (M+1))) D.sum_eq
  simpa only [modularComponent, Finset.sum_apply, Int.cast_sum, cast_integerField] using hz

theorem modular_low_complexity {M : ℕ} (θ : Lattice → Fin M) (S : Finset Lattice)
    (hlow : patternComplexity θ S ≤ S.card) :
    patternComplexity (encode modCode θ) S ≤ S.card := by
  rw [patternComplexity_encode_eq (modCode_injective M)]
  exact hlow

theorem modular_not_periodic {M : ℕ} (θ : Lattice → Fin M) (hn : ¬IsPeriodic θ) :
    ¬IsPeriodic (encode modCode θ) := by
  rwa [isPeriodic_encode_iff (modCode_injective M)]

theorem periodicOn_encode {A B : Type*} (f : A → B) {θ : Lattice → A}
    {R : Set Lattice} {h : Lattice} (hp : PeriodicOn θ R h) :
    PeriodicOn (encode f θ) R h := ⟨hp.1, fun z hz => congrArg f (hp.2 z hz)⟩

end
end NivatTrial.ModularReduction
