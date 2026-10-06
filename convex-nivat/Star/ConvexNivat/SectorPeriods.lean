import ConvexNivat.SectorSpectralDefinitions
import ConvexNivat.CorePeriods
import ConvexNivat.CoreLattice
import ConvexNivat.OperatorAction

open scoped BigOperators
namespace ConvexNivat
noncomputable section

theorem applied_sector_background_common_period {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (ε : SectorSigns star) (a : ZMod p)
    (i : Fin star.m) :
    HasPeriod (appliedSectorBackground star periods ε a) (periods.vector i) := by
  classical
  have hp : HasPeriod (sectorBackground star ε) (periods.vector i) := by
    intro z
    change (∑ j, componentTail star j (ε j) (z + periods.vector i)) =
      ∑ j, componentTail star j (ε j) z
    apply Finset.sum_congr rfl
    intro j _
    cases hε : ε j with
    | left => exact periods.left_period i j z
    | right => exact periods.right_period i j z
  intro z
  change applyLaurent (exceptionalPolynomial star periods)
    (colorIndicator (sectorBackground star ε) a) (z + periods.vector i) = _
  simp only [applyLaurent, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  unfold colorIndicator
  rw [add_right_comm z (periods.vector i) u, hp]


theorem applied_sector_background_doubly_periodic {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (ε : SectorSigns star) (a : ZMod p) :
    DoublyPeriodic (appliedSectorBackground star periods ε a) := by
  let i : Fin star.m := ⟨0, by have := star.two_le; omega⟩
  let j : Fin star.m := ⟨1, by have := star.two_le; omega⟩
  refine ⟨periods.vector i, periods.vector j, ?_,
    applied_sector_background_common_period star periods ε a i,
    applied_sector_background_common_period star periods ε a j⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hn := star.pairwise_nonparallel i j hij
  have hi : (periods.multiplier i : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (periods.positive i)
  have hj : (periods.multiplier j : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (periods.positive j)
  have he : det (periods.vector i) (periods.vector j) =
      (periods.multiplier i : ℤ) * (periods.multiplier j : ℤ) *
        det (star.component i).direction (star.component j).direction := by
    simp [StarCommonPeriods.vector, det]
    ring
  unfold Nonparallel
  rw [he]
  exact mul_ne_zero (mul_ne_zero hi hj) hn



end
end ConvexNivat
