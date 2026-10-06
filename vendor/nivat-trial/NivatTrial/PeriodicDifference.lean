import NivatTrial.Periodicity

/-! Finite-group integration of a periodic difference, and two-component limits. -/

namespace NivatTrial.PeriodicDifference

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.Dynamics

variable {A : Type*} [AddCommGroup A]

def increment (f : Lattice → A) (d : Lattice) : Lattice → A := fun z => f (z+d)-f z

theorem increment_period {f : Lattice → A} {h : Lattice} (hp : IsPeriod f h)
    (d : Lattice) : IsPeriod (increment f d) h := by
  intro z
  simp only [increment]
  rw [show z+h+d=z+d+h by abel, hp, hp]

theorem increment_commute_period (f : Lattice → A) (d e : Lattice)
    (hp : IsPeriod (increment f d) e) : IsPeriod (increment f e) d := by
  intro z
  have h := hp z
  dsimp [increment] at h ⊢
  rw [show z+e+d=z+d+e by abel] at h
  apply sub_eq_sub_iff_add_eq_add.mpr
  have hh := sub_eq_sub_iff_add_eq_add.mp h
  convert hh using 1 <;> abel

theorem increment_nsmul (f : Lattice → A) (d : Lattice)
    (hp : IsPeriod (increment f d) d) (n : ℕ) (z : Lattice) :
    f (z+n•d) = f z + n • increment f d z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (hp.nsmul n) z
    change f (z+n•d+d)-f (z+n•d) = increment f d z at h
    rw [succ_nsmul, ← add_assoc, ← sub_add_cancel (f (z+n•d+d)) (f (z+n•d)), h, ih]
    rw [succ_nsmul]
    abel

theorem period_of_periodic_increment [Fintype A] (f : Lattice → A) (d : Lattice)
    (hp : IsPeriod (increment f d) d) : IsPeriod f (Fintype.card A • d) := by
  intro z
  simpa using increment_nsmul f d hp (Fintype.card A) z

/-- Lemma 8.13, for any finite additive abelian group. -/
theorem doublyPeriodic_of_increment [Fintype A] (f : Lattice → A)
    (h d : Lattice) (hh : IsPeriod f h) (hd : det h d ≠ 0)
    (hg : IsDoublyPeriodic (increment f d)) : IsDoublyPeriodic f := by
  obtain ⟨M, hM, hper⟩ := direction_period_of_finite_orbit (increment f d) d
    (finite_orbit_of_doublyPeriodic _ hg)
  have hinc := (increment_commute_period f d (M•d) hper).nsmul M
  have hp := period_of_periodic_increment f (M•d) hinc
  refine ⟨h, Fintype.card A • (M•d), ?_, hh, hp⟩
  rw [det_nsmul_right, det_nsmul_right]
  exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
    (mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hM) hd)

theorem doublyPeriodic_add (f g : Lattice → A)
    (hf : IsDoublyPeriodic f) (hg : IsDoublyPeriodic g) : IsDoublyPeriodic (f+g) := by
  let family : Bool → Lattice → A := fun b => if b then f else g
  have hp : ∀ b, IsDoublyPeriodic (family b) := by intro b; cases b <;> assumption
  simpa [family, add_comm] using doublyPeriodic_sum family hp

theorem doublyPeriodic_sub (f g : Lattice → A)
    (hf : IsDoublyPeriodic f) (hg : IsDoublyPeriodic g) : IsDoublyPeriodic (f-g) := by
  obtain ⟨h,k,hd,hh,hk⟩ := hg
  have hn : IsDoublyPeriodic (-g) := ⟨h,k,hd,hh.neg_config,hk.neg_config⟩
  simpa [sub_eq_add_neg] using doublyPeriodic_add f (-g) hf hn

theorem cramer_identity (h k d : Lattice) :
    det h k • d = det d k • h + det h d • k := by
  ext <;> simp [det] <;> ring

theorem exists_transverse (h : Lattice) (hh : h ≠ 0) : ∃ k : Lattice, det h k ≠ 0 := by
  by_cases hx : h.1 = 0
  · refine ⟨(1,0), ?_⟩
    have hy : h.2 ≠ 0 := by intro he; apply hh; ext <;> simp_all
    simpa [det] using hy
  · exact ⟨(0,1), by simpa [det] using hx⟩

theorem parallel_direction_period {f : Lattice → A} {h : Lattice}
    (hp : IsPeriod f h) (hh : h ≠ 0) (g : Lattice) (hg : det h g = 0) :
    ∃ M : ℕ, 0 < M ∧ IsPeriod f (M•g) := by
  obtain ⟨k, hk⟩ := exists_transverse h hh
  have heq : det h k • g = det g k • h := by simpa [hg] using cramer_identity h k g
  have hper : IsPeriod f (det h k • g) := by rw [heq]; exact hp.zsmul _
  refine ⟨(det h k).natAbs, Int.natAbs_pos.mpr hk, ?_⟩
  rw [← natCast_zsmul, Int.natCast_natAbs]
  exact hper.abs_zsmul

/-- If the sum acquires a period, one of two independent periodic components
which was not doubly periodic forces the other component to be doubly periodic. -/
theorem second_component_doublyPeriodic [Fintype A]
    (f g : Lattice → A) (h k : Lattice) (hf : IsPeriod f h) (hg : IsPeriod g k)
    (hdet : det h k ≠ 0) (hnf : ¬IsDoublyPeriodic f)
    (hsum : IsPeriodic (f+g)) : IsDoublyPeriodic g := by
  obtain ⟨d, hd, hperiod⟩ := hsum
  have heq : increment f d = -increment g d := by
    funext z
    have hh := hperiod z
    simp only [Pi.add_apply] at hh
    simp only [increment, Pi.neg_apply]
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      (f (z+d)-f z)+(g (z+d)-g z) =
          (f (z+d)+g (z+d))-(f z+g z) := by abel
      _ = 0 := by rw [hh, sub_self]
  by_cases hdh : det h d = 0
  · have hcommon : det h k • d = det d k • h := by
      simpa [hdh] using cramer_identity h k d
    have hfp : IsPeriod f (det h k • d) := by rw [hcommon]; exact hf.zsmul _
    have hgp : IsPeriod g (det h k • d) := by
      have hp := (hperiod.zsmul (det h k)).sub_config hfp
      simpa using hp
    have hdk : det d k ≠ 0 := by
      intro hzero
      have hpair : (det h d, det k d) = (det h 0, det k 0) := by
        simp [hdh, det_swap k d, hzero]
      exact hd ((det_pair_injective h k hdet) hpair)
    refine ⟨det h k • d, k, ?_, hgp, hg⟩
    rw [det_zsmul_left]
    exact mul_ne_zero hdet hdk
  · have hdelta_h := increment_period hf d
    have hdelta_k : IsPeriod (increment f d) k := by
      rw [heq]
      exact (increment_period hg d).neg_config
    exact (hnf (doublyPeriodic_of_increment f h d hf hdh
      ⟨h,k,hdet,hdelta_h,hdelta_k⟩)).elim

end NivatTrial.PeriodicDifference
