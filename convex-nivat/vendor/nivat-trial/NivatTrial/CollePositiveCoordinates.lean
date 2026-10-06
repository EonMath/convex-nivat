import NivatTrial.ColleCoordinateTransport
import NivatTrial.HorizontalCoordinates

/-! A positively oriented unimodular basis for an arbitrary nonzero lattice direction. -/
namespace NivatTrial.CollePositiveCoordinates
open NivatTrial.Geometry NivatTrial.ColleCoordinateTransport NivatTrial.RowDetermination
noncomputable section
/-- Normalize the first direction while preserving the sign and exact
value of every determinant. -/
theorem exists_positive_horizontal_coordinates (u : Lattice) (hu : u ≠ 0) :
    ∃ P : ℕ, ∃ f : Lattice ≃+ Lattice,
      0 < P ∧ f (P•horizontal) = u ∧
        ∀ a b : Lattice, det (f a) (f b) = det a b := by
  have hg : 0 < Int.gcd u.1 u.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hx := Int.gcd_dvd_left u.1 u.2
    have hy := Int.gcd_dvd_right u.1 u.2
    rw [hz] at hx hy
    simp only [Nat.cast_zero,zero_dvd_iff] at hx hy
    exact hu (Prod.ext hx hy)
  obtain ⟨P,x,y,hP,hprim,hx,hy⟩ := Int.exists_gcd_one' hg
  let v : Lattice := (x,y)
  obtain ⟨w,hw⟩ := exists_unimodular_complement v hprim
  have hw' : NivatTrial.Divisibility.det v w = 1 := hw
  let f := NivatTrial.Divisibility.basisEquiv v w hw'
  have hf1 : f (1,0) = v := NivatTrial.Divisibility.basisEquiv_first v w hw'
  have hf2 : f (0,1) = w := NivatTrial.Divisibility.basisEquiv_second v w hw'
  refine ⟨P,f,hP,?_,?_⟩
  · rw [map_nsmul]
    change P • f (1,0) = u
    rw [hf1]
    ext
    · simpa [v,nsmul_eq_mul,mul_comm] using hx.symm
    · simpa [v,nsmul_eq_mul,mul_comm] using hy.symm
  · intro a b
    have hh := det_addHom f.toAddMonoidHom a b
    simpa only [AddEquiv.toAddMonoidHom_eq_coe,AddMonoidHom.coe_coe,
      hf1,hf2,hw,one_mul] using hh

end
end NivatTrial.CollePositiveCoordinates
