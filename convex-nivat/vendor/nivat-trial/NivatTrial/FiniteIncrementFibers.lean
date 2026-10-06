import NivatTrial.PeriodicBandCoding

/-! A single deterministic direction bounds the cardinality of every fiber
of the transverse difference map, uniformly over the orbit closure. -/

namespace NivatTrial.FiniteIncrementFibers

open NivatTrial.Nonexpansive NivatTrial.Dynamics NivatTrial.PeriodicDifference
open NivatTrial.PeriodicBandCoding Filter
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem increment_encode_shift (w : A → ℤ) (x : Lattice → A) (h u : Lattice) :
    increment (encode w (shift u x)) h = shift u (increment (encode w x) h) := by
  funext z
  simp [increment,encode,shift,add_assoc]

theorem eventually_score_translate_nonpos (v : Plane) (d : Lattice)
    (hd : 0 < score v d) (z : Lattice) :
    ∀ᶠ n : ℕ in atTop, score v (z-n•d) ≤ 0 := by
  obtain ⟨N,hN⟩ := exists_nat_ge (score v z / score v d)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [score_sub,score_nsmul]
  have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hmul := (div_le_iff₀ hd).mp hN
  nlinarith

omit [Fintype A] in
theorem eventually_shifted_patterns_ne (θ : Lattice → A) (w : A → ℤ)
    (h d : Lattice) (v : Plane) (hd : 0 < score v d) (B : Finset Lattice)
    (hcode : ∀ x ∈ languageHull θ, ∀ y ∈ languageHull θ,
      increment (encode w x) h = increment (encode w y) h →
      (∀ b ∈ B, x b = y b) → ∀ z, score v z ≤ 0 → x z = y z)
    (x y : Lattice → A) (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (hne : x ≠ y) (hinc : increment (encode w x) h = increment (encode w y) h)
    (u : Lattice) :
    ∀ᶠ n : ℕ in atTop, patternAt (shift (n•d) x) B u ≠ patternAt (shift (n•d) y) B u := by
  obtain ⟨z,hz⟩ := Function.ne_iff.mp hne
  filter_upwards [eventually_score_translate_nonpos v d hd (z-u)] with n hn
  intro hp
  have hcommon : increment (encode w (shift (n•d+u) x)) h =
      increment (encode w (shift (n•d+u) y)) h := by
    rw [increment_encode_shift,increment_encode_shift,hinc]
  have hbound : score v (z-(n•d+u)) ≤ 0 := by
    convert hn using 2
    abel
  have he := hcode (shift (n•d+u) x) (shift_mem_languageHull hx _)
    (shift (n•d+u) y) (shift_mem_languageHull hy _) hcommon
    (fun b hb => by simpa [patternAt,shift,add_assoc] using congrFun hp ⟨b,hb⟩)
    (z-(n•d+u)) hbound
  exact hz (by simpa [shift] using he)

/-- Translate a finite family until each of its finitely many disagreements
lies on the coded side of the same finite window. -/
theorem card_bound_of_fiber_coding (θ : Lattice → A) (w : A → ℤ)
    (h d : Lattice) (v : Plane) (hd : 0 < score v d) (B : Finset Lattice)
    (hcode : ∀ x ∈ languageHull θ, ∀ y ∈ languageHull θ,
      increment (encode w x) h = increment (encode w y) h →
      (∀ b ∈ B, x b = y b) → ∀ z, score v z ≤ 0 → x z = y z)
    (n : ℕ) (F : Fin n → Lattice → A) (hF : ∀ i, F i ∈ languageHull θ)
    (hinj : Function.Injective F)
    (hinc : ∀ i j, increment (encode w (F i)) h = increment (encode w (F j)) h) :
    n ≤ Fintype.card A ^ B.card := by
  have hpair (i j : Fin n) : ∀ᶠ m : ℕ in atTop, i ≠ j →
      patternAt (shift (m•d) (F i)) B 0 ≠ patternAt (shift (m•d) (F j)) B 0 := by
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · exact (eventually_shifted_patterns_ne θ w h d v hd B hcode (F i) (F j)
        (hF i) (hF j) (fun he => hij (hinj he)) (hinc i j) 0).mono (fun _ hn _ => hn)
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i j : Fin n, i ≠ j →
      patternAt (shift (m•d) (F i)) B 0 ≠ patternAt (shift (m•d) (F j)) B 0 :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j => hpair i j))
  obtain ⟨m,hm⟩ := hall.exists
  have hi : Function.Injective (fun i : Fin n => patternAt (shift (m•d) (F i)) B 0) := by
    intro i j he
    by_contra hij
    exact hm i j hij he
  have hc := Fintype.card_le_of_injective _ hi
  simpa using hc

theorem exists_uniform_fiber_bound (θ : Lattice → A) (w : A → ℤ)
    (hw : Function.Injective w) (v : Plane) (hv : v ≠ 0)
    (hexp : OneSidedExpansive θ v) (h d : Lattice)
    (hdet : NivatTrial.Geometry.det h d ≠ 0) (hh : score v h = 0)
    (hd : 0 < score v d) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ F : Fin n → Lattice → A,
      (∀ i, F i ∈ languageHull θ) → Function.Injective F →
      (∀ i j, increment (encode w (F i)) h = increment (encode w (F j)) h) → n ≤ N := by
  obtain ⟨B,hB⟩ := exists_finite_fiber_coding θ w hw v hv hexp h d hdet hh hd
  exact ⟨Fintype.card A ^ B.card,fun n F hF hi hinc =>
    card_bound_of_fiber_coding θ w h d v hd B hB n F hF hi hinc⟩

end
end NivatTrial.FiniteIncrementFibers
