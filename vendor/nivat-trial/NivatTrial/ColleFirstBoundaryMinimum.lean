import NivatTrial.ColleEnvelopeRays
import NivatTrial.ColleEnvelopeTranslation

/-! The first boundary of a proper upper-half-plane envelope has an actual
left endpoint.  A forward ray and unbounded transverse height force every
support parallel to that ray to be an upper-half-plane constraint.  Thus
an excluded point supplies a transverse support, whose integer minimum
on the bottom row is attained. -/

namespace NivatTrial.ColleFirstBoundaryMinimum

open NivatTrial.Geometry NivatTrial.RegionGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleEnvelopeRecession
open NivatTrial.ColleEnvelopeRays NivatTrial.ColleEnvelopeTranslation
open scoped Classical
noncomputable section

theorem exists_positive_transverse_support
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u k a : Lattice) (huk : 0 < det u k)
    (ha : a ∈ R) (ha0 : det u a = 0)
    (hray : ∀ n : ℕ, a+n•u ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hproper : ∃ z : Lattice, 0 ≤ det u z ∧ z ∉ R) :
    ∃ d ∈ D, 0 < det d u ∧ HasLowerSupport R d := by
  obtain ⟨z,hz,hout⟩ := hproper
  by_contra hnone
  apply hout
  rw [← hR]
  intro d hd b hb
  have hs : HasLowerSupport R d := ⟨b,hb⟩
  have hdu := support_nonnegative_on_ray R a u hray hs
  have hdu0 : det d u = 0 := by
    by_contra hn
    exact hnone ⟨d,hd,by omega,hs⟩
  have hdk := parallel_support_nonnegative R u k d hheight huk hdu0 hs
  have hida := det_plucker u k d a
  rw [ha0,hdu0,mul_zero,zero_mul,sub_zero] at hida
  have hda : det d a = 0 := by nlinarith
  have hidz := det_plucker u k d z
  rw [hdu0,zero_mul,sub_zero] at hidz
  have hp := mul_nonneg hdk hz
  have hdz : 0 ≤ det d z := by nlinarith
  have hba := hb a ha
  rw [hda] at hba
  omega

/-- An attained minimum on the actual bottom row gives a missing predecessor,
even when `u` is not primitive. -/
theorem exists_first_boundary_point
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u k a : Lattice) (huk : 0 < det u k)
    (ha : a ∈ R) (ha0 : det u a = 0)
    (hray : ∀ n : ℕ, a+n•u ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hproper : ∃ z : Lattice, 0 ≤ det u z ∧ z ∉ R) :
    ForwardInvariant R u ∧
      ∃ w ∈ R, det u w = 0 ∧ w-u ∉ R ∧ ∀ n : ℕ, w+n•u ∈ R := by
  have hforward : ForwardInvariant R u :=
    forward_of_support_signs D R hR u
      (fun _ _ hs => support_nonnegative_on_ray R a u hray hs)
  obtain ⟨d,_,hdu,b,hb⟩ := exists_positive_transverse_support
    D R hR u k a huk ha ha0 hray hheight hproper
  let B : Set Lattice := {z | z ∈ R ∧ det u z = 0}
  obtain ⟨w,hw,hmin⟩ := exists_support_point B ⟨a,ha,ha0⟩ d
    ⟨b,fun z hz => hb z hz.1⟩
  refine ⟨hforward,w,hw.1,hw.2,?_,fun n => hforward.nsmul n w hw.1⟩
  intro hmem
  have hm : w-u ∈ B := ⟨hmem,by rw [det_sub_right,det_self,hw.2,sub_zero]⟩
  have hle := hmin (w-u) hm
  rw [det_sub_right] at hle
  omega

theorem exists_recentered_first_boundary
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u k a : Lattice) (huk : 0 < det u k)
    (ha : a ∈ R) (ha0 : det u a = 0)
    (hray : ∀ n : ℕ, a+n•u ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hproper : ∃ z : Lattice, 0 ≤ det u z ∧ z ∉ R) :
    ∃ w : Lattice, det u w = 0 ∧
      0 ∈ recenter R w ∧ -u ∉ recenter R w ∧
      (∀ n : ℕ, n•u ∈ recenter R w) ∧
      ForwardInvariant (recenter R w) u ∧
      ∀ N : ℤ, ∃ z ∈ recenter R w, N ≤ det u z := by
  obtain ⟨hf,w,hw,hw0,hout,hr⟩ := exists_first_boundary_point
    D R hR u k a huk ha ha0 hray hheight hproper
  refine ⟨w,hw0,by simpa [recenter] using hw,?_,?_,?_,?_⟩
  · simpa [recenter,sub_eq_add_neg,add_comm] using hout
  · intro n
    simpa [recenter,add_comm] using hr n
  · intro z hz
    change z+u+w ∈ R
    have hh := hf (z+w) hz
    convert hh using 1
    abel
  · intro N
    obtain ⟨z,hz,hNz⟩ := hheight N
    refine ⟨z-w,by simpa [recenter] using hz,?_⟩
    simpa only [det_sub_right,hw0,sub_zero] using hNz

end
end NivatTrial.ColleFirstBoundaryMinimum
