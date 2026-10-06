import ConvexNivat.Colle.GeneratingBand

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


/-- Colle Proposition 2.14 (Kari–Szabados Lemma 39), retaining the actual
half-plane periodic input and producing a global nonzero tangent period. -/
theorem colle_2_14 (ξ : Configuration ℤ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hann : HasNontrivialIntegerAnnihilator ξ) (v : Lattice) (hv : Primitive v)
    (b : ℤ) (hhalf : DirectionalPeriod ξ {z | b ≤ det v z} v) :
    ∃ k : ℤ, k ≠ 0 ∧ HasPeriod ξ (k • v) := by
  classical
  obtain ⟨m, h, hn, hp, ha⟩ := external8_4b_factors_obligation ξ A hA hann
  obtain ⟨f, hf, hs⟩ := external8_4b_decomposition_obligation m h hn hp ξ ha
  obtain ⟨_, k, hk, hper⟩ := hhalf
  let J : Finset (Fin m) := Finset.univ.filter (fun i => det v (h i) = 0)
  let K : ℤ := ∏ i ∈ J, if v.1 ≠ 0 then (h i).1 else (h i).2
  have hcoords (i : Fin m) (hi : i ∈ J) :
      (if v.1 ≠ 0 then (h i).1 else (h i).2) ≠ 0 := by
    have hdet := (Finset.mem_filter.mp hi).2
    by_cases hv1 : v.1 ≠ 0
    · rw [if_pos hv1]
      intro he
      have he2 : (h i).2 = 0 := by
        dsimp [det] at hdet
        rw [he, mul_zero, sub_zero] at hdet
        exact (mul_eq_zero.mp hdet).resolve_left hv1
      exact hn i (Prod.ext he he2)
    · rw [if_neg hv1]
      have hv2 : v.2 ≠ 0 := by
        intro he
        exact primitive_ne_zero v hv (Prod.ext (not_ne_iff.mp hv1) he)
      intro he
      have he1 : (h i).1 = 0 := by
        dsimp [det] at hdet
        rw [he, mul_zero, zero_sub, neg_eq_zero] at hdet
        exact (mul_eq_zero.mp hdet).resolve_left hv2
      exact hn i (Prod.ext he1 he)
  have hK : K ≠ 0 := Finset.prod_ne_zero_iff.mpr hcoords
  let q : ℤ := k * K
  have hq : q ≠ 0 := mul_ne_zero hk hK
  have hcommon (i : Fin m) (hi : i ∈ J) : HasPeriod (f i) (q • v) := by
    let c : ℤ := if v.1 ≠ 0 then (h i).1 else (h i).2
    have hdvd : c ∣ K := Finset.dvd_prod_of_mem _ hi
    obtain ⟨r, hr⟩ := hdvd
    have hvscale : c • v = (if v.1 ≠ 0 then v.1 else v.2) • h i := by
      have hdet := (Finset.mem_filter.mp hi).2
      by_cases hv1 : v.1 = 0
      · simp only [c, hv1, ne_eq, not_true_eq_false, ite_false]
        have he1 : (h i).1 = 0 := by
          have hv2 : v.2 ≠ 0 := by
            intro he
            exact primitive_ne_zero v hv (Prod.ext hv1 he)
          dsimp [det] at hdet
          rw [hv1, zero_mul, zero_sub, neg_eq_zero] at hdet
          exact (mul_eq_zero.mp hdet).resolve_left hv2
        ext <;> simp [hv1, he1, mul_comm]
      · simp only [c, hv1, ne_eq, not_false_eq_true, ite_true]
        ext
        · simp [mul_comm]
        · dsimp [det] at hdet
          change (h i).1 * v.2 = v.1 * (h i).2
          linarith
    have hstep : q • v = (k * r * (if v.1 ≠ 0 then v.1 else v.2)) • h i := by
      dsimp [q]
      rw [hr]
      calc
        (k * (c * r)) • v = (k * r) • (c • v) := by rw [smul_smul]; congr 1; ring
        _ = _ := by rw [hvscale, smul_smul]
    rw [hstep]
    exact Function.Periodic.zsmul (hf i) _
  have hhalfq : ∀ z, b ≤ det v z → ξ (z + q • v) = ξ z := by
    intro z hz
    let F : ℤ → ℤ := fun s => ξ (z + s • v)
    have htangent (s : ℤ) : det v (z + s • v) = det v z := by
      dsimp [det]
      ring
    have hpk : Function.Periodic F k := by
      intro s
      have he := hper (z + s • v) (by
        change b ≤ det v (z + s • v)
        rw [htangent]
        exact hz)
        (by
          change b ≤ det v (z + s • v + k • v)
          rw [add_assoc, ← add_smul, htangent]
          exact hz)
      simpa only [F, add_smul, add_assoc] using he
    have he := Function.Periodic.int_mul hpk K (0 : ℤ)
    simpa [F, q, mul_comm] using he
  let g : Configuration ℤ := fun z => ξ (z + q • v) - ξ z
  let a : Fin m → Configuration ℤ := fun i z => f i (z + q • v) - f i z
  have hgsum (z : Lattice) : g z = ∑ i ∈ Finset.univ \ J, a i z := by
    have he : g z = ∑ i, a i z := by
      dsimp only [g, a]
      rw [hs (z + q • v), hs z, Finset.sum_sub_distrib]
    rw [he]
    symm
    apply Finset.sum_subset (Finset.sdiff_subset : Finset.univ \ J ⊆ Finset.univ)
    intro i hi hnot
    have hiJ : i ∈ J := by simpa using hnot
    exact sub_eq_zero.mpr (hcommon i hiJ z)
  have haper (i : Fin m) : HasPeriod (a i) (h i) := by
    intro z
    dsimp [a]
    rw [show z + h i + q • v = (z + q • v) + h i by abel, hf i, hf i]
  let p : Nivat.Algebra.IntegerLaurent :=
    ∏ i ∈ Finset.univ \ J, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1)
  have hgann : coefficientAct p g = 0 := by
    have hkill (i : Fin m) (hi : i ∈ Finset.univ \ J) : coefficientAct p (a i) = 0 := by
      let factor (j : Fin m) : Nivat.Algebra.IntegerLaurent := AddMonoidAlgebra.single (h j) 1 - 1
      have he : p = (∏ j ∈ (Finset.univ \ J).erase i, factor j) * factor i := by
        exact (Finset.prod_erase_mul _ factor hi).symm
      rw [he, coefficientAct_mul]
      have hai : coefficientAct (factor i) (a i) = 0 := by
        funext z
        simp [factor, coefficientAct_apply, Finsupp.sum_sub_index, sub_mul]
        change a i (z + h i) - (Finsupp.single 0 (1 : ℤ)).sum
          (fun h c => c * a i (z + h)) = 0
        simp [haper i z]
      rw [hai, coefficientAct_config_zero]
    funext z
    rw [coefficientAct_apply]
    simp_rw [hgsum, Finset.mul_sum]
    rw [Finsupp.sum, Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    simpa only [coefficientAct_apply, Finsupp.sum, Pi.zero_apply] using congrFun (hkill i hi) z
  have htrans : ∀ i ∈ Finset.univ \ J, realDot (embed (h i)) (normal v) ≠ 0 := by
    intro i hi
    rw [normal_height]
    exact_mod_cast (show det v (h i) ≠ 0 by simpa [J] using (Finset.mem_sdiff.mp hi).2)
  have hgzero := product_half_zero (normal v) h (Finset.univ \ J) g htrans hgann b (by
    intro z hz
    rw [normal_height] at hz
    exact sub_eq_zero.mpr (hhalfq z (by exact_mod_cast hz)))
  exact ⟨q, hq, fun z => sub_eq_zero.mp (congrFun hgzero z)⟩

end ConvexNivat.Colle
