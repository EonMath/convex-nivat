import NivatTrial.RowDetermination
import NivatTrial.Divisibility
import NivatTrial.LatticeCoordinates

/-! Primitive normalization of two genuinely independent lattice periods. -/

namespace NivatTrial.HorizontalCoordinates

open NivatTrial.RowDetermination NivatTrial.Geometry NivatTrial.Divisibility

noncomputable section

abbrev G := ℤ × ℤ

theorem exists_horizontal_coordinates (h₁ h₂ : G) (hindependent : Geometry.det h₁ h₂ ≠ 0) :
    ∃ c : ℕ, ∃ e : G ≃+ G,
      0 < c ∧ e (c • horizontal) = h₁ ∧ (e.symm h₂).2 ≠ 0 := by
  have hne : h₁ ≠ 0 := by
    intro hz
    exact hindependent (by simp [hz, Geometry.det])
  have hg : 0 < Int.gcd h₁.1 h₁.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hx := Int.gcd_dvd_left h₁.1 h₁.2
    have hy := Int.gcd_dvd_right h₁.1 h₁.2
    rw [hz] at hx hy
    simp only [Nat.cast_zero, zero_dvd_iff] at hx hy
    exact hne (Prod.ext hx hy)
  obtain ⟨c, x, y, hc, hprimitive, hx, hy⟩ := Int.exists_gcd_one' hg
  let u : G := (x,y)
  have hu : Int.gcd u.1 u.2 = 1 := hprimitive
  obtain ⟨w, hw⟩ := Geometry.exists_unimodular_complement u hu
  have hw' : Divisibility.det u w = 1 := hw
  let e := Divisibility.basisEquiv u w hw'
  have hfirst : e horizontal = u := Divisibility.basisEquiv_first u w hw'
  have h₁eq : h₁ = c • u := by
    ext
    · simpa [u, nsmul_eq_mul, mul_comm] using hx
    · simpa [u, nsmul_eq_mul, mul_comm] using hy
  refine ⟨c, e, hc, ?_, ?_⟩
  · rw [map_nsmul, hfirst]
    exact h₁eq.symm
  · intro hz
    have hzero : Geometry.det u h₂ = 0 := hz
    have hid : Geometry.det h₁ h₂ = (c : ℤ) * Geometry.det u h₂ := by
      rw [h₁eq]
      simp [Geometry.det, nsmul_eq_mul]
      ring
    exact hindependent (by rw [hid, hzero, mul_zero])

end

end NivatTrial.HorizontalCoordinates
