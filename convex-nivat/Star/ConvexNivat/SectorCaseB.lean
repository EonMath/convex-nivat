import ConvexNivat.SectorFiniteSupport
import ConvexNivat.OperatorDifferences
import ConvexNivat.OperatorFiniteSupport

open scoped BigOperators
namespace ConvexNivat
noncomputable section

theorem applied_colour_equals_background {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (ε : SectorSigns star) (hε : RealisedSector star ε) (a : ZMod p) :
    applyLaurent (exceptionalPolynomial star periods) (colorIndicator star.configuration a) =
      appliedSectorBackground star periods ε a := by
  classical
  let J : ScalarField :=
    applyLaurent (exceptionalPolynomial star periods) (colorIndicator star.configuration a) -
      appliedSectorBackground star periods ε a
  have hfin : ScalarHasFiniteSupport J :=
    applied_colour_difference_finite_support star periods ε hε a
  have hsub (f : LaurentPolynomial) (d e : ScalarField) :
      applyLaurent f (d - e) = applyLaurent f d - applyLaurent f e := by
    funext z
    simp [applyLaurent, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]
  have hzero (f : LaurentPolynomial) : applyLaurent f 0 = 0 := by
    funext z
    simp [applyLaurent]
  let i : Fin star.m := ⟨0, by have := star.two_le; omega⟩
  have hb : applyLaurent (starDifferencePolynomial star periods)
      (appliedSectorBackground star periods ε a) = 0 := by
    exact differenceProduct_kills_period Finset.univ periods.vector i
      (Finset.mem_univ i) _
      (applied_sector_background_common_period star periods ε a i)
  have hkill : applyLaurent (starDifferencePolynomial star periods) J = 0 := by
    dsimp only [J]
    rw [hsub, applyLaurent_commute, hB a, hzero, hb, sub_self]
  have hD : starDifferencePolynomial star periods ≠ 0 := by
    apply differenceProduct_ne_zero Finset.univ periods.vector
    intro j _
    have hn := primitive_ne_zero _ (star.component j).primitive
    have hm : (periods.multiplier j : ℤ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (periods.positive j)
    intro hz
    have hcases := smul_eq_zero.mp hz
    exact hcases.elim hm hn
  have hJ : J = 0 := by
    by_contra hne
    exact lemma_1_2 J hfin hne _ hD hkill
  exact sub_eq_zero.mp hJ

theorem encoded_star_applied_background {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (ε : SectorSigns star) (hε : RealisedSector star ε) (w : ZMod p → ℤ) :
    applyLaurent (exceptionalPolynomial star periods) (encodedStar star w) =
        encodedSectorBackground star periods ε w ∧
      DoublyPeriodic (encodedSectorBackground star periods ε w) ∧
      ∀ i, HasPeriod (encodedSectorBackground star periods ε w) (periods.vector i) := by
  classical
  let : NeZero p := ⟨star.prime.ne_zero⟩
  have hexp (χ : Configuration (ZMod p)) :
      (fun z => (w (χ z) : ℂ)) =
        ∑ b : ZMod p, (w b : ℂ) • colorIndicator χ b := by
    funext z
    simp [colorIndicator, Pi.smul_apply, smul_eq_mul, eq_comm]
  have hzero (f : LaurentPolynomial) : applyLaurent f 0 = 0 := by
    funext z
    simp [applyLaurent]
  have hsum (f : LaurentPolynomial) (s : Finset (ZMod p)) (d : ZMod p → ScalarField) :
      applyLaurent f (∑ b ∈ s, d b) = ∑ b ∈ s, applyLaurent f (d b) := by
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | @insert b s hb hs => simp [hb, applyLaurent_add_field, hs]
  have hbexp : encodedSectorBackground star periods ε w =
      ∑ b : ZMod p, (w b : ℂ) • appliedSectorBackground star periods ε b := by
    unfold encodedSectorBackground
    rw [hexp, hsum]
    simp only [applyLaurent_smul_field, appliedSectorBackground]
  have hmain : applyLaurent (exceptionalPolynomial star periods) (encodedStar star w) =
      encodedSectorBackground star periods ε w := by
    unfold encodedStar
    rw [hexp, hsum, hbexp]
    apply Finset.sum_congr rfl
    intro b _
    rw [applyLaurent_smul_field, applied_colour_equals_background star periods hB ε hε b]
  have hp (i : Fin star.m) :
      HasPeriod (encodedSectorBackground star periods ε w) (periods.vector i) := by
    rw [hbexp]
    intro z
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [applied_sector_background_common_period star periods ε b i z]
  refine ⟨hmain, ?_, hp⟩
  let i : Fin star.m := ⟨0, by have := star.two_le; omega⟩
  let j : Fin star.m := ⟨1, by have := star.two_le; omega⟩
  refine ⟨periods.vector i, periods.vector j, ?_, hp i, hp j⟩
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
