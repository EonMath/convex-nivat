import NivatTrial.ColleHalfStripEnvelope
import NivatTrial.ColleAdjacentDirections

/-! A sufficiently wide long-faced half-strip contains the base strip of
every adjacent wedge after moving its second supporting line backwards. -/

namespace NivatTrial.ColleHalfStripBase

open NivatTrial.Geometry NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleFiniteEnvelope NivatTrial.ColleHalfStripEnvelope
open NivatTrial.ColleAdjacentDirections NivatTrial.ColleWedgePeriod
open NivatTrial.ColleStripRigidity NivatTrial.FirstHalfPlane
open NivatTrial.Periodicity NivatTrial.RegionGeometry
open scoped Classical
noncomputable section

theorem determinant_identity (u k d z : Lattice) :
    det u k * det d z = det u d * det k z + det d k * det u z := by
  simp only [det]
  ring

theorem exists_base_strip_in_halfStrip (D T : Finset Lattice) (u k : Lattice)
    (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu : u ∈ D) (hnu : -u ∈ D) (huk : 0 < det u k)
    (hzero : (0 : Lattice) ∈ T) (b : Lattice) (hb : b ∈ T)
    (W : ℤ) (hwidth : W ≤ det u b) :
    ∃ c : ℤ, ∀ z, 0 ≤ det u z → det u z ≤ W → det k z ≤ c →
      z ∈ halfStrip T u := by
  let bounds := insert 0 (D.image (fun d =>
    -(abs (det u k * lowerSupport T d) + abs (det d k) * W + 1)))
  have hne : bounds.Nonempty := ⟨0,Finset.mem_insert_self _ _⟩
  let c := bounds.min' hne
  have hc0 : c ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hcd (d : Lattice) (hd : d ∈ D) :
      c ≤ -(abs (det u k * lowerSupport T d) + abs (det d k) * W + 1) :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩))
  have hu0 : u ≠ 0 := by intro he; subst u; simp [det] at huk
  refine ⟨c,?_⟩
  intro z hz0 hzW hzc
  rw [halfStrip_eq_forward_support D T u ⟨0,hzero⟩ hclosed hfaces hu0 hu hnu]
  intro d hd hdu
  have hid := determinant_identity u k d z
  have hudz : det u d = -det d u := det_swap u d
  by_cases he : det d u = 0
  · have hud : det u d = 0 := by omega
    rw [hud,zero_mul,zero_add] at hid
    by_cases hdk : 0 ≤ det d k
    · have hdz : 0 ≤ det d z := by nlinarith [mul_nonneg hdk hz0]
      exact (show lowerSupport T d ≤ 0 by simpa using lowerSupport_le hzero d).trans hdz
    · have hidb := determinant_identity u k d b
      rw [hud,zero_mul,zero_add] at hidb
      have hm := mul_le_mul_of_nonpos_left (hzW.trans hwidth) (le_of_lt (lt_of_not_ge hdk))
      have hdb : det d b ≤ det d z := by nlinarith
      exact (lowerSupport_le hb d).trans hdb
  · have hud : det u d ≤ -1 := by omega
    have hψ : det k z ≤ 0 := hzc.trans hc0
    have hm : -det k z ≤ det u d * det k z := by nlinarith
    have hlow : -(abs (det d k) * W) ≤ det d k * det u z := by
      have ha : -abs (det d k) ≤ det d k := neg_abs_le _
      have hb' := mul_le_mul_of_nonneg_right ha hz0
      have hc' := mul_le_mul_of_nonneg_left hzW (abs_nonneg (det d k))
      nlinarith
    have htarget := le_abs_self (det u k * lowerSupport T d)
    have hbound := hcd d hd
    have hprod : det u k * lowerSupport T d ≤ det u k * det d z := by
      nlinarith
    nlinarith

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]

theorem period_on_wedge_of_periodic_halfStrip
    (F : ι → Lattice → A) (h : ι → Lattice)
    (hper : ∀ i, IsPeriod (F i) (h i)) (hzero : ∀ i, h i ≠ 0)
    (D T : Finset Lattice) (u : Lattice) (ht : ∃ i, det u (h i) ≠ 0)
    (hclosed : IsEnvelope D (T : Set Lattice))
    (hfaces : LongFaces D (T : Set Lattice))
    (hu : u ∈ D) (hnu : -u ∈ D) (h0 : (0 : Lattice) ∈ T)
    (b : Lattice) (hb : b ∈ T)
    (hwidth : widthBudget (height u) (downwardTransverse u h) ≤ det u b)
    (q : ℕ) (hq : 0 < q)
    (hbase : ∀ z ∈ halfStrip T u, (∑ i,F i) (z+q•u) = (∑ i,F i) z) :
    ∃ i k c Q, (k = h i ∨ k = -h i) ∧ 0 < det u k ∧ 0 < Q ∧
      PeriodicOn (∑ i,F i) {z | 0 ≤ det u z ∧ det k z ≤ c} (Q•u) := by
  apply period_on_adjacent_wedge F h hper hzero u ht q hq
  intro k huk _
  obtain ⟨c,hc⟩ := exists_base_strip_in_halfStrip D T u k hclosed hfaces hu hnu huk
    h0 b hb _ hwidth
  exact ⟨c,fun z hz0 hzW hzc => hbase z (hc z hz0 hzW hzc)⟩

end
end NivatTrial.ColleHalfStripBase
