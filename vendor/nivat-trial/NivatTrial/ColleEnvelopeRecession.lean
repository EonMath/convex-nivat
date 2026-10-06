import NivatTrial.ColleMaximalEnvelope
import NivatTrial.AvailableDirections

/-! A recentered envelope which grows away from its bottom boundary has a
second recession direction among its actual allowed normals. The missing
next boundary point forces a transverse support; a finite slope maximum
selects the other unbounded boundary direction. -/

namespace NivatTrial.ColleEnvelopeRecession

open NivatTrial.Geometry NivatTrial.RegionGeometry
open NivatTrial.ColleMaximalEnvelope
open scoped Classical
noncomputable section

def HasLowerSupport (R : Set Lattice) (d : Lattice) : Prop :=
  ∃ b : ℤ, ∀ z ∈ R, b ≤ det d z

theorem support_nonnegative_on_ray (R : Set Lattice) (z₀ q : Lattice)
    (hray : ∀ n : ℕ, z₀+n•q ∈ R) {d : Lattice} (hd : HasLowerSupport R d) :
    0 ≤ det d q := by
  obtain ⟨b,hb⟩ := hd
  by_contra hn
  have hneg : det d q ≤ -1 := by omega
  obtain ⟨N,hN⟩ := exists_nat_gt (det d z₀-b)
  have hbound := hb (z₀+N•q) (hray N)
  rw [det_add_right,det_nsmul_right] at hbound
  have hnat : (0:ℤ) ≤ N := by omega
  nlinarith

theorem exists_transverse_support (D : Finset Lattice) (R : Set Lattice)
    (hR : IsEnvelope D R) (hzero : 0 ∈ R) (u : Lattice) (hnot : u ∉ R) :
    ∃ d ∈ D, det d u < 0 ∧ HasLowerSupport R d := by
  have hn : u ∉ supportHull D R := by rwa [hR]
  by_contra hnone
  apply hn
  intro d hd b hb
  have hb0 := hb 0 hzero
  simp only [det_zero_right] at hb0
  have hdu : 0 ≤ det d u := by
    by_contra hn
    exact hnone ⟨d,hd,lt_of_not_ge hn,⟨b,hb⟩⟩
  omega

theorem forward_of_support_signs (D : Finset Lattice) (R : Set Lattice)
    (hR : IsEnvelope D R) (q : Lattice)
    (hq : ∀ d ∈ D, HasLowerSupport R d → 0 ≤ det d q) :
    ForwardInvariant R q := by
  intro z hz
  rw [← hR]
  intro d hd b hb
  rw [det_add_right]
  exact (hb z hz).trans (le_add_of_nonneg_right (hq d hd ⟨b,hb⟩))

theorem det_plucker (u k d z : Lattice) :
    det u k * det d z = det d k * det u z - det d u * det k z := by
  simp only [det]
  ring

theorem parallel_support_nonnegative (R : Set Lattice) (u k d : Lattice)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (huk : 0 < det u k) (hdu : det d u = 0) (hd : HasLowerSupport R d) :
    0 ≤ det d k := by
  obtain ⟨b,hb⟩ := hd
  by_contra hn
  have hneg : det d k ≤ -1 := by omega
  obtain ⟨z,hz,hlarge⟩ := hheight (|det u k*b|+1)
  have hbz := hb z hz
  have hid := det_plucker u k d z
  rw [hdu,zero_mul,sub_zero] at hid
  have hleft : det u k*b ≤ det u k*det d z := mul_le_mul_of_nonneg_left hbz huk.le
  have habs := neg_abs_le (det u k*b)
  have hpositive : 0 ≤ det u z := by have := abs_nonneg (det u k*b); omega
  have hright : det d k*det u z ≤ -det u z := by nlinarith
  rw [hid] at hleft
  omega

theorem exists_supported_second_recession_direction
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u : Lattice) (hzero : 0 ∈ R) (hnot : u ∉ R)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z) :
    ∃ k ∈ D, 0 < det u k ∧ HasLowerSupport R k ∧
      ForwardInvariant R (-u) ∧ ForwardInvariant R k := by
  have hray : ∀ n : ℕ, (0:Lattice)+n•(-u) ∈ R := by
    intro n
    simpa only [smul_neg,zero_add] using hback n
  have hsign (d : Lattice) (hd : HasLowerSupport R d) : det d u ≤ 0 := by
    have hh := support_nonnegative_on_ray R 0 (-u) hray hd
    rw [det_neg_right] at hh
    omega
  let C := D.filter (fun d => det d u < 0 ∧ HasLowerSupport R d)
  have hC : C.Nonempty := by
    obtain ⟨d,hd,hdu,hs⟩ := exists_transverse_support D R hR hzero u hnot
    exact ⟨d,Finset.mem_filter.mpr ⟨hd,hdu,hs⟩⟩
  obtain ⟨k,hk,hmax⟩ := C.exists_max_image (fun d => NivatTrial.AvailableDirections.score d (-u)) hC
  have hkD := (Finset.mem_filter.mp hk).1
  have hku := (Finset.mem_filter.mp hk).2.1
  have huk : 0 < det u k := by rw [det_swap]; omega
  have hkp : 0 < det k (-u) := by rw [det_neg_right]; omega
  refine ⟨k,hkD,huk,(Finset.mem_filter.mp hk).2.2,forward_of_support_signs D R hR (-u) ?_,
    forward_of_support_signs D R hR k ?_⟩
  · intro d _ hd
    rw [det_neg_right]
    have := hsign d hd
    omega
  · intro d hd hs
    have hdu := hsign d hs
    rcases lt_or_eq_of_le hdu with hneg | heq
    · have hdC : d ∈ C := Finset.mem_filter.mpr ⟨hd,hneg,hs⟩
      have hdp : 0 < det d (-u) := by rw [det_neg_right]; omega
      have hle := hmax d hdC
      by_contra hn
      have hkd : 0 < det k d := by rw [det_swap]; omega
      have hlt := (NivatTrial.AvailableDirections.score_lt_iff hkp hdp).mpr hkd
      exact not_lt_of_ge hle hlt
    · exact parallel_support_nonnegative R u k d hheight huk heq hs

theorem exists_second_recession_direction
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u : Lattice) (hzero : 0 ∈ R) (hnot : u ∉ R)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z) :
    ∃ k ∈ D, 0 < det u k ∧ ForwardInvariant R (-u) ∧ ForwardInvariant R k := by
  obtain ⟨k,hk,huk,_,hbackR,hforR⟩ := exists_supported_second_recession_direction
    D R hR u hzero hnot hback hheight
  exact ⟨k,hk,huk,hbackR,hforR⟩

end
end NivatTrial.ColleEnvelopeRecession
