import NivatTrial.ColleReferenceLimits
import NivatTrial.ColleLimitRigidity

/-! A single proper periodic reference limit suffices to exclude a global
period once the original field has a genuine defect in the swept half-plane.
No second singly periodic limit is needed in this case. -/

namespace NivatTrial.ColleReferenceRigidity

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.ColleEnvelopeRays NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleReferenceLimits NivatTrial.ColleLimitRigidity
open NivatTrial.ColleOrbitCofactor NivatTrial.ColleProperReferences
open NivatTrial.ExternalInputs
open Filter
open scoped Classical
noncomputable section

/-- Parallel integer directions have a common positive multiple. This
version of the period transfer only needs an arbitrary alphabet. -/
theorem parallel_period_of_arbitrary_alphabet {A : Type*}
    {f : Lattice → A} {h : Lattice}
    (hp : IsPeriod f h) (hh : h ≠ 0) (u : Lattice) (hpar : det h u = 0) :
    ∃ K : ℕ, 0 < K ∧ IsPeriod f (K•u) := by
  obtain ⟨k, hk⟩ := exists_transverse h hh
  have heq : det h k • u = det u k • h := by
    simpa [hpar] using cramer_identity h k u
  have hper : IsPeriod f (det h k • u) := by
    rw [heq]
    exact hp.zsmul _
  refine ⟨(det h k).natAbs, Int.natAbs_pos.mpr hk, ?_⟩
  rw [← natCast_zsmul, Int.natCast_natAbs]
  exact hper.abs_zsmul

/-- A period by a positive multiple of the reference direction upgrades
agreement on an envelope to agreement on the entire swept half-plane. -/
theorem agree_on_upper_halfPlane_of_multiple_period {A : Type*}
    (x p : Lattice → A) (D : Finset Lattice) (R : Set Lattice)
    (hR : IsEnvelope D R) (u k : Lattice) (huk : 0 < det u k)
    (hzero : 0 ∈ R) (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hxp : AgreeOn x p R) (hp : IsPeriod p u)
    (M : ℕ) (hM : 0 < M) (hx : IsPeriod x (M•u)) :
    AgreeOn x p (halfPlane (embed u) 0) := by
  intro z hz
  have hzdet : 0 ≤ det u z := by
    have hs : (0 : ℝ) ≤ (det u z : ℝ) := by
      simpa [halfPlane, score, embed, det] using hz
    exact_mod_cast hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_mem_bottom_halfPlane D R hR u k huk hzero hback hheight z hzdet)
  let n : ℕ := M * (N + 1)
  have hnlarge : N ≤ n := by dsimp [n]; nlinarith
  have hnR : z + n • (-u) ∈ R := hN n hnlarge
  have hxneg : IsPeriod x (n • (-u)) := by
    have h := hx.neg.nsmul (N + 1)
    convert h using 1
    simp only [smul_neg, smul_smul, n]
    rw [mul_comm M (N + 1)]
  have hpneg : IsPeriod p (n • (-u)) := hp.neg.nsmul n
  exact (hxneg z).symm.trans ((hxp _ hnR).trans (hpneg z))

/-- A proper one-directional limit blocks transverse global periods. A
single actual mismatching site in the swept half-plane then blocks the
remaining parallel periods as well. -/
theorem aperiodic_of_proper_reference_and_defect
    {M m : ℕ} (x p : Lattice → Fin M)
    (E : IntegerDecomposition (integerField x) m)
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (u k : Lattice) (huk : 0 < det u k)
    (hzero : 0 ∈ R) (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hxp : AgreeOn x p R) (hp : IsPeriod p u)
    (hproper : ¬HasDoublyPeriodicExtension p (halfPlane (embed u) 0))
    (zbad : Lattice) (hzbad : 0 ≤ det u zbad) (hbad : x zbad ≠ p zbad) :
    ¬IsPeriodic x := by
  obtain ⟨y, hy, hnotDP, Q, hQ, hyQ⟩ :=
    exists_singly_periodic_reference_limit x p E D R hR u k huk
      hzero hback hheight hxp hp hproper
  rintro ⟨h, hh, hxper⟩
  have hparallelQ : det h (Q • u) = 0 :=
    period_parallel_of_singly_periodic_limit
      (directionOrbitHull_mem_languageHull hy) hyQ hnotDP hxper
  have hparallel : det h u = 0 := by
    rw [det_nsmul_right] at hparallelQ
    have hQnz : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    exact (mul_eq_zero.mp hparallelQ).resolve_left hQnz
  obtain ⟨K, hK, hxK⟩ :=
    parallel_period_of_arbitrary_alphabet hxper hh u hparallel
  have heq := agree_on_upper_halfPlane_of_multiple_period x p D R hR u k huk
    hzero hback hheight hxp hp K hK hxK
  have hz : zbad ∈ halfPlane (embed u) 0 := by
    change (0 : ℝ) ≤ score (embed u) zbad
    have hz' : (0 : ℝ) ≤ (det u zbad : ℝ) := by exact_mod_cast hzbad
    simpa [score, embed, det] using hz'
  exact hbad (heq zbad hz)

end
end NivatTrial.ColleReferenceRigidity
