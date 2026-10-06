import ConvexNivat.SectorPeriods
import ConvexNivat.ExceptionalAnnihilation

open scoped BigOperators
namespace ConvexNivat
noncomputable section

theorem exceptional_polynomial_ray_backgrounds_equal {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (a : ZMod p) :
    applyLaurent (exceptionalPolynomial star periods)
      (colorIndicator (pureRayBackground star i σ .right) a) =
    applyLaurent (exceptionalPolynomial star periods)
      (colorIndicator (pureRayBackground star i σ .left) a) := by
  classical
  have hzero (f : LaurentPolynomial) : applyLaurent f 0 = 0 := by
    funext z
    simp [applyLaurent]
  have hsub (f : LaurentPolynomial) (d e : ScalarField) :
      applyLaurent f (d - e) = applyLaurent f d - applyLaurent f e := by
    funext z
    simp [applyLaurent, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]
  have hkill (side : TailSide) :
      applyLaurent (exceptionalPolynomial star periods)
        (exceptionalDifference star i σ side a) = 0 := by
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem
      (fun j => exceptionalDirectionPolynomial star periods j) (Finset.mem_univ i)
    change applyLaurent (∏ j, exceptionalDirectionPolynomial star periods j) _ = 0
    rw [hq, mul_comm, applyLaurent_mul,
      exceptional_direction_annihilates star periods i σ side a, hzero]
  have hr := hkill .right
  have hl := hkill .left
  rw [exceptionalDifference, hsub, sub_eq_zero] at hr hl
  exact hr.symm.trans hl

end
end ConvexNivat
