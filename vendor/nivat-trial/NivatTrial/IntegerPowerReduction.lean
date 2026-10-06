import NivatTrial.OneSidedRecurrence

/-!
# Removing repeated integer difference factors for finite-range fields

If an integer-valued configuration takes only finitely many values, a
periodic first difference in one direction must vanish: otherwise the values
along that orbit form a nonconstant arithmetic progression. Consequently any
positive power of one difference that annihilates the field already implies
periodicity in that direction.
-/

namespace NivatTrial.IntegerPowerReduction

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence

open scoped Classical

noncomputable section

theorem finite_range_increment (f : Lattice → ℤ)
    (hf : (Set.range f).Finite) (h : Lattice) :
    (Set.range (increment f h)).Finite := by
  have hpair : (Set.range (fun z => (f (z + h), f z))).Finite := by
    apply (hf.prod hf).subset
    rintro p ⟨z, rfl⟩
    exact ⟨⟨z + h, rfl⟩, ⟨z, rfl⟩⟩
  apply (hpair.image (fun p : ℤ × ℤ => p.1 - p.2)).subset
  rintro y ⟨z, rfl⟩
  exact ⟨(f (z + h), f z), ⟨z, rfl⟩, rfl⟩

/-- A finite-range integer field cannot have a nonzero constant increment
along any of its translation orbits. -/
theorem period_of_periodic_increment (f : Lattice → ℤ) (h : Lattice)
    (hf : (Set.range f).Finite) (hp : IsPeriod (increment f h) h) :
    IsPeriod f h := by
  intro z
  let orbitValue : ℕ → Set.range f :=
    fun n => ⟨f (z + n • h), ⟨z + n • h, rfl⟩⟩
  obtain ⟨n, m, hne, heq⟩ :=
    @Finite.exists_ne_map_eq_of_infinite ℕ (Set.range f) inferInstance hf orbitValue
  have hv := congrArg Subtype.val heq
  change f (z + n • h) = f (z + m • h) at hv
  rw [increment_nsmul f h hp n z, increment_nsmul f h hp m z] at hv
  have hmul : ((n : ℤ) - (m : ℤ)) * increment f h z = 0 := by
    simpa only [nsmul_eq_mul, sub_mul] using sub_eq_zero.mpr (add_left_cancel hv)
  have hneInt : (n : ℤ) - (m : ℤ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hne)
  have hzero : increment f h z = 0 := (mul_eq_zero.mp hmul).resolve_left hneInt
  exact sub_eq_zero.mp hzero

/-- Iterating the same difference is the `List.replicate` specialization of
`iteratedIncrement`. -/
theorem finite_range_power_period (n : ℕ) (f : Lattice → ℤ) (h : Lattice)
    (hf : (Set.range f).Finite)
    (hann : iteratedIncrement (List.replicate (n + 1) h) f = 0) :
    IsPeriod f h := by
  induction n generalizing f with
  | zero =>
    intro z
    have hz := congrFun hann z
    simpa [iteratedIncrement, increment] using sub_eq_zero.mp hz
  | succ n ih =>
    have hstep : iteratedIncrement (List.replicate (n + 1) h)
        (increment f h) = 0 := by
      rw [iteratedIncrement_commute]
      simpa only [Nat.succ_eq_add_one, List.replicate_succ,
        iteratedIncrement_cons] using hann
    have hp : IsPeriod (increment f h) h :=
      ih (increment f h) (finite_range_increment f hf h) hstep
    exact period_of_periodic_increment f h hf hp

/-- Convenient positive-exponent statement. -/
theorem finite_range_power_period_of_pos (n : ℕ) (hn : 0 < n)
    (f : Lattice → ℤ) (h : Lattice) (hf : (Set.range f).Finite)
    (hann : iteratedIncrement (List.replicate n h) f = 0) : IsPeriod f h := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact finite_range_power_period m f h hf hann

theorem finite_range_iterated (hs : List Lattice) (f : Lattice → ℤ)
    (hf : (Set.range f).Finite) :
    (Set.range (iteratedIncrement hs f)).Finite := by
  induction hs with
  | nil => simpa using hf
  | cons h hs ih =>
    simpa only [iteratedIncrement_cons] using
      finite_range_increment (iteratedIncrement hs f) ih h

theorem iteratedIncrement_append (xs ys : List Lattice)
    (f : Lattice → ℤ) :
    iteratedIncrement (xs ++ ys) f = iteratedIncrement xs (iteratedIncrement ys f) := by
  induction xs with
  | nil => rfl
  | cons h xs ih =>
    simp only [List.cons_append, iteratedIncrement_cons, ih]

/-- A list of directions, each with its positive multiplicity. -/
def expandedDirections (blocks : List (Lattice × ℕ)) : List Lattice :=
  blocks.flatMap (fun p => List.replicate (p.2 + 1) p.1)

/-- Simultaneously remove all powers from a product of binomial differences.
No independence between the directions is needed at this stage. -/
theorem finite_range_remove_all_powers (blocks : List (Lattice × ℕ))
    (f : Lattice → ℤ) (hf : (Set.range f).Finite)
    (hann : iteratedIncrement (expandedDirections blocks) f = 0) :
    iteratedIncrement (blocks.map Prod.fst) f = 0 := by
  induction blocks generalizing f with
  | nil => simpa [expandedDirections] using hann
  | cons p ps ih =>
    obtain ⟨h, m⟩ := p
    have hpower : iteratedIncrement (List.replicate (m + 1) h)
        (iteratedIncrement (expandedDirections ps) f) = 0 := by
      simpa only [expandedDirections, List.flatMap_cons,
        iteratedIncrement_append] using hann
    have hperiod : IsPeriod (iteratedIncrement (expandedDirections ps) f) h :=
      finite_range_power_period m _ h (finite_range_iterated _ f hf) hpower
    have hzero : iteratedIncrement (expandedDirections ps) (increment f h) = 0 := by
      rw [iteratedIncrement_commute]
      funext z
      exact sub_eq_zero.mpr (hperiod z)
    have hsimpler := ih (increment f h) (finite_range_increment f hf h) hzero
    simpa only [List.map_cons, iteratedIncrement_cons, ← iteratedIncrement_commute] using
      hsimpler

end

end NivatTrial.IntegerPowerReduction
