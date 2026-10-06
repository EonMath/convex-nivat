import ConvexNivat.Colle.GeneratingTransverse

namespace ConvexNivat.Colle
open scoped BigOperators
open Nivat.Algebra

private theorem difference_action (u : Lattice) (f : Configuration ℤ) :
    coefficientAct (AddMonoidAlgebra.single u (1 : ℤ) - 1) f =
      fun z => f (z + u) - f z := by
  funext z
  simp [coefficientAct_apply, Finsupp.sum_sub_index, sub_mul]
  change (Finsupp.single 0 (1 : ℤ)).sum (fun h a => a * f (z + h)) = f z
  simp

private theorem product_band_zero {ι : Type*} [DecidableEq ι]
    (n : RealPlane) (h : ι → Lattice) (I : Finset ι) (f : Configuration ℤ)
    (htrans : ∀ i ∈ I, realDot (embed (h i)) n ≠ 0)
    (hann : coefficientAct (∏ i ∈ I, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1)) f = 0)
    (hband : ∀ z, |realDot (embed z) n| ≤ ∑ i ∈ I, |realDot (embed (h i)) n| → f z = 0) :
    f = 0 := by
  classical
  let H : Lattice → ℝ := fun z => realDot (embed z) n
  have hadd (a b : Lattice) : H (a + b) = H a + H b := by
    dsimp [H, realDot, embed]
    push_cast
    ring
  have hsmul (a : Lattice) (k : ℤ) : H (k • a) = (k : ℝ) * H a := by
    dsimp [H, realDot, embed]
    push_cast
    ring
  have hneg (a : Lattice) : H (-a) = -H a := by
    simpa using hsmul a (-1)
  have hperiodzero (u : Lattice) (f : Configuration ℤ)
      (hu : H u ≠ 0) (hp : HasPeriod f u)
      (hf : ∀ z, |H z| ≤ |H u| → f z = 0) : f = 0 := by
    obtain ⟨v, hv, hper, habs⟩ :
        ∃ v : Lattice, 0 < H v ∧ HasPeriod f v ∧ |H v| = |H u| := by
      rcases lt_or_gt_of_ne hu with hneg' | hpos
      · exact ⟨-u, by rw [hneg]; linarith, Function.Periodic.neg hp, by rw [hneg, abs_neg]⟩
      · exact ⟨u, hpos, hp, rfl⟩
    funext z
    let k : ℤ := -⌊H z / H v⌋
    have hlow := (le_div_iff₀ hv).mp (Int.floor_le (H z / H v))
    have hupp := (div_lt_iff₀ hv).mp (Int.lt_floor_add_one (H z / H v))
    have hbetween : 0 ≤ H (z + k • v) ∧ H (z + k • v) ≤ H v := by
      rw [hadd, hsmul]
      dsimp only [k]
      rw [Int.cast_neg]
      constructor <;> nlinarith
    have hbound : |H (z + k • v)| ≤ |H u| := by
      rw [abs_of_nonneg hbetween.1, ← habs, abs_of_pos hv]
      exact hbetween.2
    exact (Function.Periodic.zsmul hper k z).symm.trans (hf _ hbound)
  revert f
  induction I using Finset.induction_on with
  | empty => intro f ha hb; simpa using ha
  | @insert i I hi ih =>
    intro f ha hb
    let g : Configuration ℤ := fun z => f (z + h i) - f z
    have hgann : coefficientAct
        (∏ j ∈ I, (AddMonoidAlgebra.single (h j) (1 : ℤ) - 1)) g = 0 := by
      rw [Finset.prod_insert hi, mul_comm, coefficientAct_mul, difference_action] at ha
      exact ha
    have hgband : ∀ z, |H z| ≤ ∑ j ∈ I, |H (h j)| → g z = 0 := by
      intro z hz
      have hI : (∑ j ∈ I, |H (h j)|) ≤ ∑ j ∈ insert i I, |H (h j)| := by
        rw [Finset.sum_insert hi]
        exact le_add_of_nonneg_left (abs_nonneg _)
      have hshift : |H (z + h i)| ≤ ∑ j ∈ insert i I, |H (h j)| := by
        rw [hadd, Finset.sum_insert hi]
        exact (abs_add_le _ _).trans (by linarith)
      dsimp [g]
      rw [hb _ hshift, hb _ (hz.trans hI), sub_self]
    have hgzero := ih (fun j hj => htrans j (Finset.mem_insert_of_mem hj)) g hgann hgband
    have hp : HasPeriod f (h i) := by
      intro z
      exact sub_eq_zero.mp (congrFun hgzero z)
    exact hperiodzero (h i) f (htrans i (Finset.mem_insert_self _ _)) hp (fun z hz =>
      hb z (hz.trans (by
        rw [Finset.sum_insert hi]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))))

/-- Colle Remark 2.9: the entire unoriented line has a component direction. -/
theorem minimal_decomposition_nonexpansive_direction (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (m : ℕ)
    (D : PeriodicDecomposition ℤ ξ m) (hminimal : MinimalPeriodicOrder ℤ ξ m)
    (n : RealPlane) (hn : NonexpansiveLine ξ n) :
    ∃ i, realDot (embed (D.period i)) n = 0 := by
  classical
  by_contra hnot
  push Not at hnot
  let W : ℝ := ∑ i : Fin m, |realDot (embed (D.period i)) n|
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨x, hx, y, hy, hxy, he⟩ := hn.2 (W + 1) (by linarith)
  let p : Nivat.Algebra.IntegerLaurent :=
    ∏ i : Fin m, (AddMonoidAlgebra.single (D.period i) (1 : ℤ) - 1)
  have ha (w : Configuration ℤ) (hw : w ∈ OrbitClosure ξ) : coefficientAct p w = 0 := by
    obtain ⟨E, hE⟩ := orbit_decomposition_same_periods ξ w m D
      (minimal_decomposition_pairwise ξ m D hminimal) hw
    have hm := mixedDifference_periodicDecomposition w m E
    rw [hE] at hm
    funext z
    have hexpand : coefficientAct p w z = mixedDifference D.period Finset.univ w z := by
      dsimp [p]
      simp_rw [sub_eq_add_neg]
      rw [Finset.prod_add, coefficientAct_finset_sum]
      simp only [Finset.sum_apply, mixedDifference]
      apply Finset.sum_congr rfl
      intro C hC
      have hCI : C ⊆ Finset.univ := Finset.mem_powerset.mp hC
      have hprod : (∏ i ∈ C, AddMonoidAlgebra.single (D.period i) (1 : ℤ)) =
          AddMonoidAlgebra.single (∑ i ∈ C, D.period i) (1 : ℤ) := by
        simp [AddMonoidAlgebra.prod_single]
      rw [hprod, Finset.prod_const, Finset.card_sdiff_of_subset hCI]
      have hneg (k : ℕ) : (-1 : Nivat.Algebra.IntegerLaurent) ^ k =
          AddMonoidAlgebra.single 0 ((-1 : ℤ) ^ k) := by
        change (-(AddMonoidAlgebra.single 0 (1 : ℤ))) ^ k = _
        rw [← AddMonoidAlgebra.single_neg, AddMonoidAlgebra.single_pow, nsmul_zero]
      rw [hneg]
      simp [coefficientAct_single, Nivat.shift]
    exact hexpand.trans (hm z)
  let f : Configuration ℤ := fun z => x z - y z
  have hfann : coefficientAct p f = 0 := by
    funext z
    rw [coefficientAct_apply]
    dsimp [f]
    simp_rw [mul_sub]
    rw [Finsupp.sum_sub]
    have hxz := congrFun (ha x hx) z
    have hyz := congrFun (ha y hy) z
    rw [coefficientAct_apply] at hxz hyz
    rw [hxz, hyz, sub_self]
  have hband : ∀ z, |realDot (embed z) n| ≤ W → f z = 0 := by
    intro z hz
    exact sub_eq_zero.mpr (he z (by change |realDot (embed z) n| ≤ W + 1; linarith))
  have hfzero := product_band_zero n D.period Finset.univ f
    (fun i _ => hnot i) hfann hband
  apply hxy
  funext z
  exact sub_eq_zero.mp (congrFun hfzero z)

end ConvexNivat.Colle
