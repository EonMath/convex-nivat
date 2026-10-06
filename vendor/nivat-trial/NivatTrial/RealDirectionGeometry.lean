import NivatTrial.RealHalfPlaneRecurrence

/-! A real nonzero normal has a one-dimensional kernel. Distinct lattice
directions in that kernel are therefore parallel, and a transverse lattice
step supplies an independent basis. -/

namespace NivatTrial.RealDirectionGeometry

open NivatTrial.Nonexpansive NivatTrial.Geometry
noncomputable section

theorem det_eq_zero_of_scores_zero (v : Plane) (hv : v ≠ 0) (h k : Lattice)
    (hh : score v h = 0) (hk : score v k = 0) : det h k = 0 := by
  have hh' := hh
  have hk' := hk
  unfold score at hh' hk'
  have he1 : v.1 * ((h.1:ℝ)*k.2-(h.2:ℝ)*k.1) = 0 := by
    linear_combination (h.1:ℝ)*hk' - (k.1:ℝ)*hh'
  have he2 : v.2 * ((h.1:ℝ)*k.2-(h.2:ℝ)*k.1) = 0 := by
    linear_combination (h.2:ℝ)*hk' - (k.2:ℝ)*hh'
  have hd : (h.1:ℝ)*k.2-(h.2:ℝ)*k.1 = 0 := by
    by_contra hn
    have h1 := (mul_eq_zero.mp he1).resolve_right hn
    have h2 := (mul_eq_zero.mp he2).resolve_right hn
    exact hv (Prod.ext h1 h2)
  exact_mod_cast hd

theorem independent_of_score (v : Plane) (h d : Lattice) (hh : h ≠ 0)
    (hvh : score v h = 0) (hvd : score v d ≠ 0) : det h d ≠ 0 := by
  intro hd
  have hcast : (h.1:ℝ)*d.2-(h.2:ℝ)*d.1 = 0 := by exact_mod_cast hd
  have hs := hvh
  unfold score at hs hvd
  have h1 : (h.1:ℝ) * (v.1*d.2-v.2*d.1) = 0 := by
    linear_combination v.1*hcast + (d.1:ℝ)*hs
  have h2 : (h.2:ℝ) * (v.1*d.2-v.2*d.1) = 0 := by
    linear_combination v.2*hcast + (d.2:ℝ)*hs
  have hz1 : (h.1:ℝ) = 0 := (mul_eq_zero.mp h1).resolve_right hvd
  have hz2 : (h.2:ℝ) = 0 := (mul_eq_zero.mp h2).resolve_right hvd
  apply hh
  apply Prod.ext <;> change _ = (0:ℤ)
  · exact_mod_cast hz1
  · exact_mod_cast hz2

theorem transverse_other (v : Plane) (hv : v ≠ 0) (h k : Lattice)
    (hh : score v h = 0) (hind : det h k ≠ 0) : score v k ≠ 0 :=
  fun hk => hind (det_eq_zero_of_scores_zero v hv h k hh hk)

end
end NivatTrial.RealDirectionGeometry
