import NivatTrial.HorizontalCoordinates

/-! A normalized second-edge coordinate basis with its first axis pointing
opposite to the given lattice direction and a positive transverse
determinant formula. -/

namespace NivatTrial.ColleLeftwardCoordinates

open NivatTrial.Geometry NivatTrial.Divisibility
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ

def reflectFirst : G ≃+ G where
  toFun z := (-z.1,z.2)
  invFun z := (-z.1,z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by ext <;> simp [add_comm,add_left_comm]

theorem exists_leftward_coordinates (k : G) (hk : k ≠ 0) :
    ∃ c : ℕ, ∃ e : G ≃+ G,
      0 < c ∧ e (-(c:ℤ),0) = k ∧
      ∀ z : G, Geometry.det k (e z) = (c:ℤ)*z.2 := by
  have hg : 0 < Int.gcd k.1 k.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hx := Int.gcd_dvd_left k.1 k.2
    have hy := Int.gcd_dvd_right k.1 k.2
    rw [hz] at hx hy
    simp only [Nat.cast_zero, zero_dvd_iff] at hx hy
    exact hk (Prod.ext hx hy)
  obtain ⟨c,x,y,hc,hprimitive,hx,hy⟩ := Int.exists_gcd_one' hg
  let u : G := (x,y)
  obtain ⟨v,hv⟩ := Geometry.exists_unimodular_complement u hprimitive
  have hv' : Divisibility.det u v = 1 := hv
  let e₀ := Divisibility.basisEquiv u v hv'
  let e := reflectFirst.trans e₀
  have hk_eq : k = c • u := by
    ext
    · simpa [u,nsmul_eq_mul,mul_comm] using hx
    · simpa [u,nsmul_eq_mul,mul_comm] using hy
  refine ⟨c,e,hc,?_,?_⟩
  · have hfirst : reflectFirst (-(c:ℤ),0) = c • ((1,0):G) := by
      ext <;> simp [reflectFirst,nsmul_eq_mul]
    change e₀ (reflectFirst (-(c:ℤ),0)) = k
    rw [hfirst,map_nsmul,Divisibility.basisEquiv_first]
    exact hk_eq.symm
  · intro z
    rw [hk_eq]
    have hdet : Geometry.det u (e z) = z.2 := by
      have hh := hv
      dsimp [Geometry.det] at hh
      dsimp [Geometry.det,e,e₀,reflectFirst,Divisibility.basisEquiv]
      linear_combination z.2 * hh
    simpa only [← natCast_zsmul,Geometry.det_zsmul_left,hdet] using
      (show (c:ℤ)*z.2=(c:ℤ)*z.2 from rfl)

end
end NivatTrial.ColleLeftwardCoordinates
