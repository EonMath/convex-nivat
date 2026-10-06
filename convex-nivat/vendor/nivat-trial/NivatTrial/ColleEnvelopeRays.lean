import NivatTrial.ColleEnvelopeRecession

/-! A boundary ray of a finitely supported convex envelope sweeps its
entire supporting half-plane. This supplies the actual geometric inclusion
needed when taking a directional orbit limit of a regional period. -/

namespace NivatTrial.ColleEnvelopeRays

open NivatTrial.Geometry NivatTrial.RegionGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleEnvelopeRecession
open Filter
open scoped Classical
noncomputable section

theorem exists_support_point (R : Set Lattice) (hR : R.Nonempty)
    (d : Lattice) (hd : HasLowerSupport R d) :
    ∃ w ∈ R, ∀ z ∈ R, det d w ≤ det d z := by
  let S : Set ℤ := (det d) '' R
  have hS : S.Nonempty := hR.image _
  obtain ⟨b,hb⟩ := hd
  have hbound : BddBelow S := ⟨b,by rintro _ ⟨z,hz,rfl⟩; exact hb z hz⟩
  obtain ⟨w,hw,he⟩ := Int.csInf_mem hS hbound
  refine ⟨w,hw,?_⟩
  intro z hz
  rw [he]
  exact csInf_le hbound ⟨z,hz,rfl⟩

theorem eventually_mem_of_support_signs
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (hne : R.Nonempty) (z q : Lattice)
    (hsign : ∀ d ∈ D, HasLowerSupport R d → 0 ≤ det d q)
    (hzero : ∀ d ∈ D, det d q = 0 → ∀ b : ℤ,
      (∀ w ∈ R, b ≤ det d w) → b ≤ det d z) :
    ∀ᶠ n : ℕ in atTop, z+n•q ∈ R := by
  have hevent (d : D) : ∀ᶠ n : ℕ in atTop, ∀ b : ℤ,
      (∀ w ∈ R, b ≤ det d.val w) → b ≤ det d.val (z+n•q) := by
    by_cases hs : HasLowerSupport R d.val
    · obtain ⟨w,hw,hmin⟩ := exists_support_point R hne d.val hs
      have hn := hsign d.val d.property hs
      rcases eq_or_lt_of_le hn with he | hp
      · have he' : det d.val q = 0 := he.symm
        filter_upwards [] with n b hb
        simpa only [det_add_right,det_nsmul_right,he',mul_zero,add_zero]
          using hzero d.val d.property he' b hb
      · obtain ⟨N,hN⟩ := exists_nat_gt (det d.val w-det d.val z)
        filter_upwards [eventually_ge_atTop N] with n hnN b hb
        rw [det_add_right,det_nsmul_right]
        have hb' := hb w hw
        have hcast : (N:ℤ) ≤ n := by exact_mod_cast hnN
        have hnat : (0:ℤ) ≤ n := by omega
        nlinarith
    · filter_upwards [] with n b hb
      exact (hs ⟨b,hb⟩).elim
  have hall : ∀ᶠ n : ℕ in atTop, ∀ d : D, ∀ b : ℤ,
      (∀ w ∈ R, b ≤ det d.val w) → b ≤ det d.val (z+n•q) :=
    Filter.eventually_all.mpr hevent
  filter_upwards [hall] with n hn
  rw [← hR]
  intro d hd b hb
  exact hn ⟨d,hd⟩ b hb

theorem eventually_mem_support_halfPlane
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u q w : Lattice) (hw : w ∈ R) (huq : 0 < det u q)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hsign : ∀ d ∈ D, HasLowerSupport R d → 0 ≤ det d q)
    (z : Lattice) (hz : det q w ≤ det q z) :
    ∀ᶠ n : ℕ in atTop, z+n•q ∈ R := by
  apply eventually_mem_of_support_signs D R hR ⟨w,hw⟩ z q hsign
  intro d _ hdq b hb
  have hdu : det d u ≤ 0 := by
    have hh := support_nonnegative_on_ray R 0 (-u)
      (fun n => by simpa only [zero_add,smul_neg] using hback n) ⟨b,hb⟩
    rw [det_neg_right] at hh
    omega
  have hid := det_plucker u q d (z-w)
  rw [hdq,zero_mul,zero_sub,det_sub_right,det_sub_right] at hid
  have hdw := hb w hw
  have hprod : 0 ≤ -(det d u)*(det q z-det q w) :=
    mul_nonneg (by omega) (by omega)
  have hdz : det d w ≤ det d z := by nlinarith
  exact hdw.trans hdz

theorem swept_region_eq_support_halfPlane
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u q w : Lattice) (hw : w ∈ R) (huq : 0 < det u q)
    (hmin : ∀ z ∈ R, det q w ≤ det q z)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hsign : ∀ d ∈ D, HasLowerSupport R d → 0 ≤ det d q) :
    {z | ∃ n : ℕ, z+n•q ∈ R} = {z | det q w ≤ det q z} := by
  ext z
  constructor
  · rintro ⟨n,hn⟩
    change det q w ≤ det q z
    simpa only [det_add_right,det_nsmul_right,det_self,mul_zero,add_zero]
      using hmin (z+n•q) hn
  · intro hz
    exact (eventually_mem_support_halfPlane D R hR u q w hw huq hback hsign z hz).exists

theorem support_signs_of_forward (R : Set Lattice) (hne : R.Nonempty)
    (q : Lattice) (hq : ForwardInvariant R q) (d : Lattice)
    (hd : HasLowerSupport R d) : 0 ≤ det d q := by
  obtain ⟨z,hz⟩ := hne
  exact support_nonnegative_on_ray R z q (fun n => hq.nsmul n z hz) hd

theorem eventually_mem_bottom_halfPlane
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u k : Lattice) (huk : 0 < det u k) (hzero : 0 ∈ R)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (z : Lattice) (hz : 0 ≤ det u z) :
    ∀ᶠ n : ℕ in atTop, z+n•(-u) ∈ R := by
  apply eventually_mem_of_support_signs D R hR ⟨0,hzero⟩ z (-u)
  · intro d _ hd
    exact support_nonnegative_on_ray R 0 (-u)
      (fun n => by simpa only [zero_add,smul_neg] using hback n) hd
  · intro d _ he b hb
    have hdu : det d u = 0 := by rw [det_neg_right] at he; omega
    have hdk := parallel_support_nonnegative R u k d hheight huk hdu ⟨b,hb⟩
    have hid := det_plucker u k d z
    rw [hdu,zero_mul,sub_zero] at hid
    have hprod := mul_nonneg hdk hz
    have hdz : 0 ≤ det d z := by nlinarith
    have hb0 := hb 0 hzero
    simp only [det_zero_right] at hb0
    omega

/-- The second direction selected from the actual support constraints has
an attained supporting face and sweeps the whole associated half-plane. -/
theorem exists_second_boundary_ray
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u : Lattice) (hzero : 0 ∈ R) (hnot : u ∉ R)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z) :
    ∃ q ∈ D, ∃ w ∈ R, 0 < det u q ∧
      (∀ z ∈ R, det q w ≤ det q z) ∧
      ForwardInvariant R (-u) ∧ ForwardInvariant R q ∧
      ∀ z, det q w ≤ det q z → ∀ᶠ n : ℕ in atTop, z+n•q ∈ R := by
  obtain ⟨q,hq,huq,hs,hbackR,hfor⟩ := exists_supported_second_recession_direction
    D R hR u hzero hnot hback hheight
  obtain ⟨w,hw,hmin⟩ := exists_support_point R ⟨0,hzero⟩ q hs
  refine ⟨q,hq,w,hw,huq,hmin,hbackR,hfor,?_⟩
  exact eventually_mem_support_halfPlane D R hR u q w hw huq hback
    (fun d _ hd => support_signs_of_forward R ⟨0,hzero⟩ q hfor d hd)

end
end NivatTrial.ColleEnvelopeRays
