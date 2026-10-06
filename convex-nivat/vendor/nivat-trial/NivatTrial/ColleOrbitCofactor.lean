import NivatTrial.CollePeriodDirections
import NivatTrial.HullIntegerDecomposition

/-!
# Cofactor rigidity along a component-period orbit

If a periodic decomposition has component period `h`, applying all other
differences gives an `h`-periodic cofactor. Any finite-window limit along
the `h`-orbit has exactly the same cofactor. A doubly periodic limit therefore
gives a new annihilator obtained by replacing the `h` factor with a period
transverse to `h`. This is the local algebraic part of Colle's Lemma 4.4.
-/

namespace NivatTrial.ColleOrbitCofactor

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.IncrementSupport
open NivatTrial.ExternalInputs NivatTrial.Dynamics

open scoped Classical
noncomputable section

/-- Finite-window limits using only translates by integer multiples of one
fixed direction. -/
def DirectionOrbitHull {A : Type*} (x y : Lattice → A) (h : Lattice) : Prop :=
  ∀ S : Finset Lattice, ∃ t : ℤ,
    ∀ z ∈ S, x (t • h + z) = y z

theorem directionOrbitHull_mem_languageHull {A : Type*}
    {x y : Lattice → A} {h : Lattice}
    (hy : DirectionOrbitHull x y h) : y ∈ languageHull x := by
  intro S
  obtain ⟨t, ht⟩ := hy S
  exact ⟨t • h, ht⟩

theorem DirectionOrbitHull.encode {A B : Type*} {x y : Lattice → A}
    {h : Lattice} (hy : DirectionOrbitHull x y h) (w : A → B) :
    DirectionOrbitHull (encode w x) (encode w y) h := by
  intro S
  obtain ⟨t, ht⟩ := hy S
  exact ⟨t, fun z hz => congrArg w (ht z hz)⟩

/-- A local operator whose output already has period `h` cannot distinguish
an `h`-orbit limit from its source. -/
theorem iteratedIncrement_eq_of_directionOrbitHull {B : Type*} [AddCommGroup B]
    (hs : List Lattice) {x y : Lattice → B} {h : Lattice}
    (hy : DirectionOrbitHull x y h)
    (hper : IsPeriod (iteratedIncrement hs x) h) :
    iteratedIncrement hs x = iteratedIncrement hs y := by
  funext z
  obtain ⟨t, ht⟩ := hy ((offsets hs).image (fun e => z + e))
  have heq := iteratedIncrement_congr_at hs
    (fun q => x (q + t • h)) y z (by
      intro e he
      have hz := ht (z + e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      simpa only [add_comm] using hz)
  rw [iteratedIncrement_translate] at heq
  exact ((hper.zsmul t) z).symm.trans heq

theorem cofactor_period {n : ℕ} {x : Lattice → ℤ}
    (D : IntegerDecomposition x n) (i : Fin n) :
    IsPeriod (iteratedIncrement (cofactorDirections D.period i) x)
      (D.period i) := by
  have heq : iteratedIncrement (cofactorDirections D.period i) x =
      iteratedIncrement (cofactorDirections D.period i) (D.component i) := by
    calc
      iteratedIncrement (cofactorDirections D.period i) x =
          iteratedIncrement (cofactorDirections D.period i) (∑ j, D.component j) :=
        congrArg _ D.sum_eq.symm
      _ = _ := cofactor_isolates D.component D.period D.component_period i
  rw [heq]
  exact iteratedIncrement_period _ (D.component_period i)

theorem cofactor_eq_of_directionOrbitHull {n : ℕ} {x y : Lattice → ℤ}
    (D : IntegerDecomposition x n) (i : Fin n)
    (hy : DirectionOrbitHull x y (D.period i)) :
    iteratedIncrement (cofactorDirections D.period i) x =
      iteratedIncrement (cofactorDirections D.period i) y :=
  iteratedIncrement_eq_of_directionOrbitHull _ hy (cofactor_period D i)

private theorem transverse_period_of_doublyPeriodic {B : Type*}
    (g : Lattice → B) (h : Lattice) (hh : h ≠ 0)
    (hdp : IsDoublyPeriodic g) :
    ∃ k : Lattice, det h k ≠ 0 ∧ IsPeriod g k := by
  obtain ⟨a, b, hab, hpa, hpb⟩ := hdp
  by_cases ha : det h a = 0
  · refine ⟨b, ?_, hpb⟩
    intro hb
    have hc := cramer_identity h a b
    rw [ha, hb] at hc
    simp only [zero_smul, add_zero] at hc
    have hba : det b a = 0 :=
      (smul_left_injective ℤ hh) (by simpa using hc.symm)
    exact hab (by rw [det_swap, hba]; simp)
  · exact ⟨a, ha, hpa⟩

/-- The exact additional product annihilator furnished by a doubly periodic
orbit limit along one summand's period. No minimality is assumed here. -/
theorem replacement_annihilator_of_doublyPeriodic_direction_limit
    {n : ℕ} {x y : Lattice → ℤ}
    (D : IntegerDecomposition x n) (i : Fin n)
    (hy : DirectionOrbitHull x y (D.period i))
    (hdp : IsDoublyPeriodic y) :
    ∃ k : Lattice, det (D.period i) k ≠ 0 ∧
      iteratedIncrement (k :: cofactorDirections D.period i) x = 0 := by
  let hs := cofactorDirections D.period i
  have heq : iteratedIncrement hs x = iteratedIncrement hs y :=
    cofactor_eq_of_directionOrbitHull D i hy
  obtain ⟨a, b, hab, hpa, hpb⟩ := hdp
  have hgdp : IsDoublyPeriodic (iteratedIncrement hs x) := by
    rw [heq]
    exact ⟨a, b, hab, iteratedIncrement_period hs hpa,
      iteratedIncrement_period hs hpb⟩
  obtain ⟨k, hk, hkper⟩ :=
    transverse_period_of_doublyPeriodic _ (D.period i) (D.period_ne_zero i) hgdp
  refine ⟨k, hk, ?_⟩
  rw [iteratedIncrement_cons]
  funext z
  exact sub_eq_zero.mpr (hkper z)

end
end NivatTrial.ColleOrbitCofactor
