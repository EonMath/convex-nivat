import ConvexNivat.Colle.GeneratingAlgebra
import ConvexNivat.Colle.GeneratingCount

namespace ConvexNivat.Colle
open scoped BigOperators
open Nivat.Algebra

private theorem product_half_zero {ι : Type*} [DecidableEq ι]
    (n : RealPlane) (h : ι → Lattice) (I : Finset ι) (f : Configuration ℤ)
    (htrans : ∀ i ∈ I, realDot (embed (h i)) n ≠ 0)
    (hann : coefficientAct (∏ i ∈ I, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1)) f = 0)
    (c : ℝ) (hhalf : ∀ z, c ≤ realDot (embed z) n → f z = 0) : f = 0 := by
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
  revert f
  induction I using Finset.induction_on with
  | empty =>
    intro f hann _
    simpa using hann
  | @insert i I hi ih =>
    intro f ha hf
    let p : Nivat.Algebra.IntegerLaurent :=
      ∏ j ∈ I, (AddMonoidAlgebra.single (h j) (1 : ℤ) - 1)
    let g : Configuration ℤ := coefficientAct p f
    have hg : HasPeriod g (h i) := by
      rw [Finset.prod_insert hi, coefficientAct_mul] at ha
      have hdiff : coefficientAct (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1) g =
          fun z => g (z + h i) - g z := by
        funext z
        simp [coefficientAct_apply, Finsupp.sum_sub_index, sub_mul, Nivat.shift]
        change (Finsupp.single 0 (1 : ℤ)).sum (fun h a => a * g (z + h)) = g z
        simp
      change coefficientAct (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1) g = 0 at ha
      rw [hdiff] at ha
      intro z
      exact sub_eq_zero.mp (congrFun ha z)
    have hgz : ∃ b : ℝ, ∀ z, b ≤ H z → g z = 0 := by
      by_cases hp : p.coeff.support.Nonempty
      · let a : ℝ := p.coeff.support.inf' hp H
        refine ⟨c - a, ?_⟩
        intro z hz
        change coefficientAct p f z = 0
        rw [coefficientAct_apply]
        apply Finset.sum_eq_zero
        intro u hu
        have huH : a ≤ H u := Finset.inf'_le H hu
        have hhu : c ≤ H (z + u) := by rw [hadd]; linarith
        change p.coeff u * f (z + u) = 0
        rw [hf (z + u) hhu, mul_zero]
      · have hp0 : p.coeff = 0 := by
          exact Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hp)
        have hpzero : p = 0 := by
          exact AddMonoidAlgebra.coeff_injective (by simpa using hp0)
        refine ⟨c, ?_⟩
        intro z hz
        simp [g, hpzero]
    obtain ⟨b, hb⟩ := hgz
    have hgi : g = 0 := by
      have hti : H (h i) ≠ 0 := htrans i (Finset.mem_insert_self _ _)
      obtain ⟨u, hu, hpu⟩ : ∃ u : Lattice, 0 < H u ∧ HasPeriod g u := by
        rcases lt_or_gt_of_ne hti with hneg' | hpos
        · exact ⟨-h i, by rw [hneg]; linarith, Function.Periodic.neg hg⟩
        · exact ⟨h i, hpos, hg⟩
      funext z
      obtain ⟨k, hk⟩ := exists_int_gt ((b - H z) / H u)
      have hlarge : b ≤ H (z + k • u) := by
        rw [hadd, hsmul]
        have he := (div_lt_iff₀ hu).mp hk
        linarith
      have hperiod : g (z + k • u) = g z := Function.Periodic.zsmul hpu k z
      exact hperiod.symm.trans (hb _ hlarge)
    apply ih (fun j hj => htrans j (Finset.mem_insert_of_mem hj)) f
    · exact hgi
    · exact hf

/-- Colle Lemma 2.8(ii): one-sided directions come from the actual factors. -/
theorem colle_2_8_nonexpansive (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (m : ℕ) (h : Fin m → Lattice)
    (hnonzero : ∀ i, h i ≠ 0)
    (hpairwise : Pairwise (fun i j => Nonparallel (h i) (h j)))
    (hann : Annihilates (differenceFactors m h) ξ)
    (n : RealPlane) (hn : OneSidedNonexpansive ξ n) :
    ∃ i, realDot (embed (h i)) n = 0 := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨_, x, hx, y, hy, hxy, he⟩ := hn
  let p : Nivat.Algebra.IntegerLaurent :=
    ∏ i : Fin m, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1)
  have ha (w : Configuration ℤ) (hw : w ∈ OrbitClosure ξ) :
      coefficientAct p (fun z => w (-z)) = 0 := by
    have hξ : ∀ z, integerLaurentAction ((differenceFactors m h).mapDomain Neg.neg) ξ z = 0 := by
      intro z
      rw [← laurentAction_reflection]
      exact hann z
    have hwann := orbitClosure_preserves_integer_annihilator ξ w
      ((differenceFactors m h).mapDomain Neg.neg) hw hξ
    funext z
    have hsource : laurentAction (differenceFactors m h) w (-z) = 0 := by
      rw [laurentAction_reflection]
      exact hwann (-z)
    rw [coefficientAct_apply]
    change p.coeff.sum (fun u a => a * w (-(z + u))) = 0
    simpa [differenceFactors, laurentAction, p, sub_eq_add_neg, add_comm,
      ← AddMonoidAlgebra.one_def] using hsource
  let f : Configuration ℤ := fun z => x (-z) - y (-z)
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
  have htrans : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      realDot (embed (h i)) (-n) ≠ 0 := by
    intro i hi
    simpa [realDot, add_comm] using neg_ne_zero.mpr (hnot i)
  have hhalf : ∀ z, (0 : ℝ) ≤ realDot (embed z) (-n) → f z = 0 := by
    intro z hz
    have heq : realDot (embed (-z)) n = realDot (embed z) (-n) := by
      simp [realDot, embed]
    exact sub_eq_zero.mpr (he (-z) (by
      change 0 ≤ realDot (embed (-z)) n
      rw [heq]
      exact hz))
  have hfzero := product_half_zero (-n) h Finset.univ f htrans hfann 0 hhalf
  apply hxy
  funext z
  have hz := congrFun hfzero (-z)
  simpa [f] using sub_eq_zero.mp hz

end ConvexNivat.Colle
