import Mathlib

/-! The elementary lattice geometry used at the end of Lemma 1.1. -/

namespace NivatTrial.Geometry

abbrev Lattice := ℤ × ℤ

def det (v z : Lattice) : ℤ := v.1 * z.2 - v.2 * z.1

@[simp] theorem det_add_right (v x y : Lattice) :
    det v (x + y) = det v x + det v y := by simp [det]; ring

@[simp] theorem det_zero_right (v : Lattice) : det v 0 = 0 := by simp [det]

@[simp] theorem det_neg_right (v x : Lattice) : det v (-x) = -det v x := by
  simp [det]; ring

@[simp] theorem det_sub_right (v x y : Lattice) :
    det v (x - y) = det v x - det v y := by simp [det]; ring

theorem det_swap (v w : Lattice) : det v w = -det w v := by simp [det]; ring

@[simp] theorem det_self (v : Lattice) : det v v = 0 := by simp [det]; ring

@[simp] theorem det_zsmul_right (v x : Lattice) (n : ℤ) :
    det v (n • x) = n * det v x := by simp [det]; ring

@[simp] theorem det_zsmul_left (v x : Lattice) (n : ℤ) :
    det (n • v) x = n * det v x := by simp [det]; ring

theorem det_nsmul_right (v x : Lattice) (n : ℕ) :
    det v (n • x) = (n : ℤ) * det v x := by simp [det]; ring

/-- An integer basis provided by Bezout for a primitive direction. -/
theorem exists_unimodular_complement (v : Lattice) (hv : Int.gcd v.1 v.2 = 1) :
    ∃ u : Lattice, det v u = 1 := by
  refine ⟨(-Int.gcdB v.1 v.2, Int.gcdA v.1 v.2), ?_⟩
  have h := Int.gcd_eq_gcd_ab v.1 v.2
  rw [hv] at h
  simp only [Int.cast_ofNat_Int] at h
  dsimp [det]
  linarith

theorem det_surjective_of_primitive (v : Lattice) (hv : Int.gcd v.1 v.2 = 1) :
    Function.Surjective (det v) := by
  obtain ⟨u, hu⟩ := exists_unimodular_complement v hv
  intro n
  exact ⟨n • u, by rw [det_zsmul_right, hu, mul_one]⟩

/-- The inverse coordinate formula for a unimodular lattice basis. -/
theorem unimodular_coordinates (v u z : Lattice) (hvu : det v u = 1) :
    (det z u) • v + (det v z) • u = z := by
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  · have h : det z u * v.1 + det v z * u.1 = det v u * z.1 := by
      simp [det]; ring
    simpa [hvu] using h
  · have h : det z u * v.2 + det v z * u.2 = det v u * z.2 := by
      simp [det]; ring
    simpa [hvu] using h

theorem det_zero_iff_parallel_in_basis (v u z : Lattice) (hvu : det v u = 1) :
    det v z = 0 ↔ ∃ n : ℤ, z = n • v := by
  constructor
  · intro hz
    refine ⟨det z u, ?_⟩
    simpa [hz] using (unimodular_coordinates v u z hvu).symm
  · rintro ⟨n, rfl⟩
    rw [det_zsmul_right, det_self, mul_zero]

/-- Two independent integer normals distinguish all lattice points. -/
theorem det_pair_injective (v w : Lattice) (h : det v w ≠ 0) :
    Function.Injective (fun z : Lattice => (det v z, det w z)) := by
  intro x y hxy
  have hv : det v x = det v y := congrArg Prod.fst hxy
  have hw : det w x = det w y := congrArg Prod.snd hxy
  apply Prod.ext
  · have hid : det v w * (x.1 - y.1) =
        w.1 * (det v x - det v y) - v.1 * (det w x - det w y) := by
      simp only [det]
      ring
    rw [hv, hw] at hid
    simp only [sub_self, mul_zero] at hid
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left h)
  · have hid : det v w * (x.2 - y.2) =
        w.2 * (det v x - det v y) - v.2 * (det w x - det w y) := by
      simp only [det]
      ring
    rw [hv, hw] at hid
    simp only [sub_self, mul_zero] at hid
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left h)

/-- An intersection of bounded-width lattice strips in distinct directions is finite. -/
theorem finite_strip_intersection (v w : Lattice) (h : det v w ≠ 0)
    (a b c d : ℤ) :
    {z : Lattice | det v z ∈ Set.Icc a b ∧ det w z ∈ Set.Icc c d}.Finite := by
  have hp : (Set.Icc a b ×ˢ Set.Icc c d).Finite :=
    (Set.finite_Icc a b).prod (Set.finite_Icc c d)
  exact hp.preimage (det_pair_injective v w h).injOn

end NivatTrial.Geometry
