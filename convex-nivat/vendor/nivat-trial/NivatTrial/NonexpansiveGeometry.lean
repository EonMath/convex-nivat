import NivatTrial.Nonexpansive

/-! The elementary circle geometry used when a nearest disagreement is
translated to the origin. Squared lattice distance makes the minimizing
choice discrete; normalized real normals have compact range. -/

namespace NivatTrial.NonexpansiveGeometry

open NivatTrial.Nonexpansive
open scoped Classical
noncomputable section

def energy (z : Lattice) : ℕ := z.1.natAbs ^ 2 + z.2.natAbs ^ 2

theorem energy_cast (z : Lattice) :
    (energy z : ℝ) = (z.1:ℝ)^2 + (z.2:ℝ)^2 := by
  simp [energy, sq_abs]

@[simp] theorem energy_zero : energy 0 = 0 := by simp [energy]

theorem energy_eq_zero_iff (z : Lattice) : energy z = 0 ↔ z = 0 := by
  simp [energy, Prod.ext_iff]

def radius (z : Lattice) : ℝ := Real.sqrt (energy z)

theorem radius_nonneg (z : Lattice) : 0 ≤ radius z := Real.sqrt_nonneg _

theorem radius_sq (z : Lattice) : radius z ^ 2 = (energy z:ℝ) :=
  Real.sq_sqrt (Nat.cast_nonneg _)

theorem radius_pos {z : Lattice} (hz : z ≠ 0) : 0 < radius z := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.pos_of_ne_zero (mt (energy_eq_zero_iff z).mp hz)

def normal (z : Lattice) : Plane := (-(z.2:ℝ) / radius z, (z.1:ℝ) / radius z)

theorem normal_unit {z : Lattice} (hz : z ≠ 0) :
    (normal z).1 ^ 2 + (normal z).2 ^ 2 = 1 := by
  have hr := radius_pos hz
  have he := radius_sq z
  rw [energy_cast] at he
  dsimp [normal]
  field_simp
  nlinarith

theorem normal_bounds {z : Lattice} (hz : z ≠ 0) :
    normal z ∈ Set.Icc ((-1:ℝ),(-1:ℝ)) (1,1) := by
  have he := normal_unit hz
  have h1 := sq_nonneg ((normal z).1)
  have h2 := sq_nonneg ((normal z).2)
  change (-1 ≤ (normal z).1 ∧ -1 ≤ (normal z).2) ∧
    ((normal z).1 ≤ 1 ∧ (normal z).2 ≤ 1)
  constructor <;> constructor <;> nlinarith

theorem energy_add_identity (w z : Lattice) :
    (energy (w+z):ℝ) = (energy w:ℝ) + (energy z:ℝ) +
      2 * ((w.1:ℝ)*(z.1:ℝ) + (w.2:ℝ)*(z.2:ℝ)) := by
  simp only [energy_cast, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem normal_score (w z : Lattice) :
    score (normal w) z = -((w.1:ℝ)*(z.1:ℝ) + (w.2:ℝ)*(z.2:ℝ)) / radius w := by
  simp only [score, normal]
  ring

/-- A point on the inward side of the tangent line lies in the large original
agreement disk once the positive score dominates its quadratic error. -/
theorem energy_add_lt {w z : Lattice} (hw : w ≠ 0)
    (h : (energy z:ℝ) < 2 * radius w * score (normal w) z) :
    energy (w+z) < energy w := by
  have hr := ne_of_gt (radius_pos hw)
  have he : 2 * radius w * score (normal w) z =
      -2 * ((w.1:ℝ)*(z.1:ℝ) + (w.2:ℝ)*(z.2:ℝ)) := by
    rw [normal_score]
    field_simp
  rw [he] at h
  have ht : (energy (w+z):ℝ) < (energy w:ℝ) := by
    rw [energy_add_identity]
    linarith
  exact_mod_cast ht

theorem continuous_score (z : Lattice) : Continuous (fun v : Plane => score v z) := by
  unfold score
  fun_prop

def box (n : ℕ) : Finset Lattice :=
  Finset.Icc (-((n:ℤ),(n:ℤ))) ((n:ℤ),(n:ℤ))

theorem mem_box_of_energy_le {z : Lattice} {n : ℕ} (h : energy z ≤ n^2) :
    z ∈ box n := by
  have hr : (z.1:ℝ)^2 + (z.2:ℝ)^2 ≤ (n:ℝ)^2 := by
    rw [← energy_cast]
    exact_mod_cast h
  have h1 := sq_nonneg (z.1:ℝ)
  have h2 := sq_nonneg (z.2:ℝ)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hb1 : -(n:ℝ) ≤ z.1 ∧ (z.1:ℝ) ≤ n := by constructor <;> nlinarith
  have hb2 : -(n:ℝ) ≤ z.2 ∧ (z.2:ℝ) ≤ n := by constructor <;> nlinarith
  change z ∈ Finset.Icc (-((n:ℤ),(n:ℤ))) ((n:ℤ),(n:ℤ))
  rw [Finset.mem_Icc]
  change (-(n:ℤ) ≤ z.1 ∧ -(n:ℤ) ≤ z.2) ∧ (z.1 ≤ (n:ℤ) ∧ z.2 ≤ (n:ℤ))
  constructor
  · constructor
    · exact_mod_cast hb1.1
    · exact_mod_cast hb2.1
  · constructor
    · exact_mod_cast hb1.2
    · exact_mod_cast hb2.2

theorem radius_gt_of_not_mem_box {z : Lattice} {n : ℕ} (h : z ∉ box n) :
    (n:ℝ) < radius z := by
  have hen : n^2 < energy z := lt_of_not_ge (fun he => h (mem_box_of_energy_le he))
  have he : (n:ℝ)^2 < radius z^2 := by
    rw [radius_sq]
    exact_mod_cast hen
  have hnon := radius_nonneg z
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

end
end NivatTrial.NonexpansiveGeometry
