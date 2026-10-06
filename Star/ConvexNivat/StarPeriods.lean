import ConvexNivat.StarOperators
import ConvexNivat.CorePeriods
import ConvexNivat.CoreLattice

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section

/-- The finite-index intersection consequence used to choose the source `H_i`. -/
theorem commonTailPeriods_contains_scaled_lattice {p : ℕ} (d : StarData p) :
    ∃ N : ℕ, 0 < N ∧ ∀ z : Lattice, N • z ∈ commonTailPeriods d := by
  classical
  have ht : ∀ j : Fin d.m, ∃ N : ℕ, 0 < N ∧ ∀ z : Lattice,
      HasPeriod (d.component j).leftTail (N • z) ∧
        HasPeriod (d.component j).rightTail (N • z) := by
    intro j
    obtain ⟨L, hL, hLp⟩ := (doublyPeriodic_iff_grid _).mp
      (d.component j).left_doubly_periodic
    obtain ⟨R, hR, hRp⟩ := (doublyPeriodic_iff_grid _).mp
      (d.component j).right_doubly_periodic
    refine ⟨L * R, Nat.mul_pos hL hR, fun z => ?_⟩
    constructor
    · simpa only [Nat.cast_mul, smul_smul, natCast_zsmul] using hLp (R • z)
    · simpa only [Nat.cast_mul, mul_comm L R, smul_smul, natCast_zsmul] using hRp (L • z)
  choose n hn hp using ht
  refine ⟨∏ j, n j, Finset.prod_pos (fun j _ => hn j), ?_⟩
  intro z j
  have h := hp j ((∏ k ∈ Finset.univ.erase j, n k) • z)
  simpa only [← Finset.mul_prod_erase _ n (Finset.mem_univ j), mul_smul] using h

/-- Existence of admissible choices, independently of the paper's minimality convention. -/
theorem starPeriodData_exists {p : ℕ} (d : StarData p) : Nonempty (StarPeriodData d) := by
  classical
  obtain ⟨N, hN, hNp⟩ := commonTailPeriods_contains_scaled_lattice d
  choose k hk hp using fun i => (d.component i).tangential_period
  have hkn : ∀ i, 0 < (k i).toNat := by
    intro i
    have := hk i
    omega
  refine ⟨{
    multiplier := fun i => N * (k i).toNat
    multiplier_pos := fun i => Nat.mul_pos hN (hkn i)
    component_period := ?_
    all_tail_periods := ?_ }⟩
  · intro i
    have h := hasPeriod_zsmul (d.component i).field
      (k i • (d.component i).direction) (hp i) (N : ℤ)
    simpa only [Nat.cast_mul, Int.toNat_of_nonneg (by have := hk i; omega : 0 ≤ k i),
      smul_smul] using h
  · intro i
    have h := hNp ((k i).toNat • (d.component i).direction)
    simpa only [natCast_zsmul, smul_smul] using h

theorem StarPeriodData.vector_ne_zero {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (i : Fin d.m) : P.vector i ≠ 0 := by
  have hv := primitive_ne_zero (d.component i).direction (d.component i).primitive
  have hn : (P.multiplier i : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (P.multiplier_pos i))
  intro h
  have h' : (P.multiplier i : ℤ) * (d.component i).direction.1 = 0 ∧
      (P.multiplier i : ℤ) * (d.component i).direction.2 = 0 := by
    simpa [StarPeriodData.vector, Prod.ext_iff] using h
  exact hv (Prod.ext ((mul_eq_zero.mp h'.1).resolve_left hn)
    ((mul_eq_zero.mp h'.2).resolve_left hn))

end

end ConvexNivat
