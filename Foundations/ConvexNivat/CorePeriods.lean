import ConvexNivat.Core
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic

namespace ConvexNivat

theorem hasPeriod_zero {A : Type*} (f : Configuration A) : HasPeriod f 0 := by
  intro z
  simp

theorem hasPeriod_add {A : Type*} (f : Configuration A) (h k : Lattice)
    (hh : HasPeriod f h) (hk : HasPeriod f k) : HasPeriod f (h + k) := by
  exact Function.Periodic.add_period hh hk

theorem hasPeriod_neg {A : Type*} (f : Configuration A) (h : Lattice)
    (hh : HasPeriod f h) : HasPeriod f (-h) := by
  exact Function.Periodic.neg hh

theorem hasPeriod_zsmul {A : Type*} (f : Configuration A) (h : Lattice)
    (hh : HasPeriod f h) (n : ℤ) : HasPeriod f (n • h) := by
  exact Function.Periodic.zsmul hh n

theorem hasPeriod_translate_iff {A : Type*} (f : Configuration A)
    (u h : Lattice) : HasPeriod (translate u f) h ↔ HasPeriod f h := by
  constructor
  · intro hp z
    have hshift : z - u + h + u = z + h := by
      rw [add_right_comm (z - u) h u, sub_add_cancel]
    simpa only [translate, hshift, sub_add_cancel] using hp (z - u)
  · intro hp z
    simpa [translate, add_assoc, add_comm, add_left_comm] using hp (z + u)

theorem periodic_translate_iff {A : Type*} (f : Configuration A) (u : Lattice) :
    Periodic (translate u f) ↔ Periodic f := by
  simp only [Periodic, hasPeriod_translate_iff]

theorem doublyPeriodic_translate_iff {A : Type*} (f : Configuration A) (u : Lattice) :
    DoublyPeriodic (translate u f) ↔ DoublyPeriodic f := by
  simp only [DoublyPeriodic, hasPeriod_translate_iff]

theorem doublyPeriodic_periodic {A : Type*} (f : Configuration A)
    (hf : DoublyPeriodic f) : Periodic f := by
  rcases hf with ⟨h, k, hInd, hh, hk⟩
  refine ⟨h, ?_, hh⟩
  intro hzero
  subst h
  simp [Nonparallel, det] at hInd

/-- Source §0.1's finite-index characterization, expressed as a contained grid. -/
theorem doublyPeriodic_iff_grid {A : Type*} (f : Configuration A) :
    DoublyPeriodic f ↔ ∃ N : ℕ, 0 < N ∧
      ∀ z : Lattice, HasPeriod f ((N : ℤ) • z) := by
  constructor
  · rintro ⟨h, k, hInd, hh, hk⟩
    refine ⟨(det h k).natAbs, Int.natAbs_pos.mpr hInd, ?_⟩
    intro z
    have hd : HasPeriod f ((det h k) • z) := by
      have hlin : (det h k) • z =
          (k.2 * z.1 - k.1 * z.2) • h +
          (h.1 * z.2 - h.2 * z.1) • k := by
        ext <;> simp [det] <;> ring
      rw [hlin]
      exact hasPeriod_add f _ _ (hasPeriod_zsmul f h hh _)
        (hasPeriod_zsmul f k hk _)
    rw [Int.natCast_natAbs]
    rcases le_total 0 (det h k) with hpos | hneg
    · simpa [abs_of_nonneg hpos] using hd
    · simpa [abs_of_nonpos hneg, neg_smul] using hasPeriod_neg f _ hd
  · rintro ⟨N, hN, hp⟩
    refine ⟨((N : ℤ), 0), (0, (N : ℤ)), ?_, ?_, ?_⟩
    · have hne : (N : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      simpa [Nonparallel, det] using mul_ne_zero hne hne
    · simpa [smul_eq_mul] using hp (1, 0)
    · simpa [smul_eq_mul] using hp (0, 1)

/-- Source Remark 0.1: a multiple of any direction preserves a periodic background. -/
theorem doublyPeriodic_multiple_period {A : Type*} (f : Configuration A)
    (hf : DoublyPeriodic f) (h : Lattice) :
    ∃ k : ℤ, 1 ≤ k ∧ HasPeriod f (k • h) := by
  rcases (doublyPeriodic_iff_grid f).mp hf with ⟨N, hN, hp⟩
  refine ⟨N, ?_, hp h⟩
  exact_mod_cast Nat.succ_le_of_lt hN

theorem hasPeriod_add_fields {A : Type*} [AddMonoid A]
    (f g : Configuration A) (h : Lattice)
    (hf : HasPeriod f h) (hg : HasPeriod g h) : HasPeriod (f + g) h := by
  exact Function.Periodic.add hf hg

theorem hasPeriod_sub_fields {A : Type*} [AddGroup A]
    (f g : Configuration A) (h : Lattice)
    (hf : HasPeriod f h) (hg : HasPeriod g h) : HasPeriod (f - g) h := by
  exact Function.Periodic.sub hf hg

theorem doublyPeriodic_add_fields {A : Type*} [AddCommMonoid A]
    (f g : Configuration A) (hf : DoublyPeriodic f) (hg : DoublyPeriodic g) :
    DoublyPeriodic (f + g) := by
  rcases (doublyPeriodic_iff_grid f).mp hf with ⟨N, hN, hp⟩
  rcases (doublyPeriodic_iff_grid g).mp hg with ⟨M, hM, hq⟩
  apply (doublyPeriodic_iff_grid (f + g)).mpr
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  intro z
  apply hasPeriod_add_fields
  · simpa only [Nat.cast_mul, smul_smul] using hp ((M : ℤ) • z)
  · simpa only [Nat.cast_mul, smul_smul, mul_comm] using hq ((N : ℤ) • z)

theorem doublyPeriodic_sub_fields {A : Type*} [AddCommGroup A]
    (f g : Configuration A) (hf : DoublyPeriodic f) (hg : DoublyPeriodic g) :
    DoublyPeriodic (f - g) := by
  rcases (doublyPeriodic_iff_grid f).mp hf with ⟨N, hN, hp⟩
  rcases (doublyPeriodic_iff_grid g).mp hg with ⟨M, hM, hq⟩
  apply (doublyPeriodic_iff_grid (f - g)).mpr
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  intro z
  apply hasPeriod_sub_fields
  · simpa only [Nat.cast_mul, smul_smul] using hp ((M : ℤ) • z)
  · simpa only [Nat.cast_mul, smul_smul, mul_comm] using hq ((N : ℤ) • z)

end ConvexNivat
