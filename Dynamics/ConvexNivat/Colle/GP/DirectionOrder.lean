import ConvexNivat.Colle.GP.Primitive
import Mathlib.Data.Fintype.Order

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

private theorem gp_labelled_order (m : ℕ) (h : Fin m → Lattice)
    (hne : ∀ i, h i ≠ 0) (hpair : Pairwise (fun i j => Nonparallel (h i) (h j))) :
    Nonempty (LabelledFactorOrder m h) := by
  classical
  choose k hk w hw heq using fun i => positive_primitive_integer_factor (h i) (hne i)
  let N : ℕ := 1 + ∑ i, (w i).1.natAbs
  let L : Lattice → ℤ := fun z => z.1 + (N : ℤ) * z.2
  have hL : ∀ i, L (w i) ≠ 0 := by
    intro i hz
    have hsum : (w i).1.natAbs ≤ ∑ j : Fin m, (w j).1.natAbs :=
      Finset.single_le_sum (f := fun j : Fin m => (w j).1.natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hN : ((w i).1.natAbs : ℤ) < N := by dsimp [N]; exact_mod_cast (by omega : (w i).1.natAbs < 1 + ∑ j : Fin m, (w j).1.natAbs)
    have habs := Int.le_natAbs (a := (w i).1)
    have habs' := Int.le_natAbs (a := -(w i).1)
    simp only [Int.natAbs_neg] at habs'
    dsimp [L] at hz
    have hy : (w i).2 = 0 := by
      by_contra hy
      rcases lt_or_gt_of_ne hy with hy | hy <;> nlinarith
    have hx : (w i).1 = 0 := by simp [hy] at hz; exact hz
    exact primitive_ne_zero (w i) (hw i) (Prod.ext hx hy)
  let d : Fin m → Lattice := fun i => if 0 < L (w i) then w i else -w i
  let σ : Fin m → ℤ := fun i => if 0 < L (w i) then 1 else -1
  have hdpos : ∀ i, 0 < L (d i) := by
    intro i
    dsimp [d]
    split_ifs with hpos
    · exact hpos
    · have hn : L (-w i) = -L (w i) := by simp [L]; ring
      rw [hn]
      have hne := hL i
      omega
  have hdprim : ∀ i, Primitive (d i) := by
    intro i
    dsimp [d]
    split_ifs
    · exact hw i
    · simpa [Primitive] using hw i
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := by intro i; dsimp [σ]; split_ifs <;> simp
  have hfactor : ∀ i, h i = (σ i * (k i : ℤ)) • d i := by
    intro i
    dsimp [σ, d]
    split_ifs <;> simpa using heq i
  have hnonpar : Pairwise (fun i j => det (d i) (d j) ≠ 0) := by
    intro i j hij hd
    have hbad := hpair hij
    apply hbad
    rw [hfactor i, hfactor j]
    have hdet : ∀ r s : ℤ, det (r • d i) (s • d j) = r * s * det (d i) (d j) := by
      intro r s; simp [det]; ring
    rw [hdet, hd, mul_zero]
  let slope : Fin m → ℝ := fun i => ((d i).2 : ℝ) / (L (d i) : ℝ)
  have hlin : ∀ i j, (det (d i) (d j) : ℝ) =
      (L (d i) : ℝ) * (d j).2 - (d i).2 * (L (d j) : ℝ) := by
    intro i j; simp [L, det]; ring
  have hinj : Function.Injective slope := by
    intro i j he
    by_contra hij
    have hi : (L (d i) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hdpos i))
    have hj : (L (d j) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hdpos j))
    have hcross := (div_eq_div_iff hi hj).mp he
    have hzero : (det (d i) (d j) : ℝ) = 0 := by rw [hlin]; linarith
    exact hnonpar hij (by exact_mod_cast hzero)
  let T := {i : Fin m // True}
  letI inst : LinearOrder T := LinearOrder.lift' (fun i => slope i.val)
    (fun i j hh => Subtype.ext (hinj hh))
  letI : LE T := inst.toLE
  letI : LT T := inst.toLT
  let e := Fintype.orderIsoFinOfCardEq T (k := m) (by simp [T])
  let label : Fin m ≃ Fin m :=
    { toFun := fun i => (e i).val
      invFun := fun i => e.symm ⟨i, trivial⟩
      left_inv := by intro i; exact e.symm_apply_apply i
      right_inv := by intro i; exact congrArg Subtype.val (e.apply_symm_apply ⟨i, trivial⟩) }
  refine ⟨{
    label := label
    direction := fun i => d (label i)
    scale := fun i => k (label i)
    sign := fun i => σ (label i)
    primitive := fun i => hdprim (label i)
    scale_positive := fun i => hk (label i)
    sign_unit := fun i => hσ (label i)
    factor_eq := fun i => hfactor (label i)
    ordered_turn := ?_
  }⟩
  intro i j hij
  have hs : slope (label i) < slope (label j) :=
    @OrderIso.strictMono _ _ _ inst.toPreorder e i j hij
  have hi : (0 : ℝ) < L (d (label i)) := by exact_mod_cast hdpos (label i)
  have hj : (0 : ℝ) < L (d (label j)) := by exact_mod_cast hdpos (label j)
  have hcross := (div_lt_div_iff₀ hi hj).mp hs
  have hdet : (0 : ℝ) < det (d (label i)) (d (label j)) := by rw [hlin]; linarith
  exact_mod_cast hdet

private theorem gp_cycle_congr {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j k : ℤ)
    (he : j % (2 * (m : ℤ)) = k % (2 * (m : ℤ))) :
    labelledCycleDirection O j = labelledCycleDirection O k := by
  unfold labelledCycleDirection
  rw [he]

private theorem gp_cycle_periodic {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) :
    labelledCycleDirection O (j + 2 * (m : ℤ)) = labelledCycleDirection O j := by
  apply gp_cycle_congr
  simp

private theorem gp_cycle_first {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i : ℕ) (hi : i < m) :
    labelledCycleDirection O (i : ℤ) = O.direction ⟨i, hi⟩ := by
  have hm : 0 < m := by omega
  have hmod : (i : ℤ) % (2 * (m : ℤ)) = i :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  simp [labelledCycleDirection, hm, hmod, Nat.mod_eq_of_lt hi, hi]

private theorem gp_cycle_second {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i : ℕ) (hi : m ≤ i) (hi2 : i < 2 * m) :
    labelledCycleDirection O (i : ℤ) = -O.direction ⟨i - m, by omega⟩ := by
  have hm : 0 < m := by omega
  have hmod : (i : ℤ) % (2 * (m : ℤ)) = i :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  have hnat : i % m = i - m := by
    rw [Nat.mod_eq_sub_mod hi, Nat.mod_eq_of_lt (by omega)]
  simp [labelledCycleDirection, hm, hmod, show ¬ i < m by omega, hnat]

private theorem gp_cycle_antipodal {m : ℕ} (hm : 0 < m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) :
    labelledCycleDirection O (j + (m : ℤ)) = -labelledCycleDirection O j := by
  let r := (j % (2 * (m : ℤ))).toNat
  have hr0 : 0 ≤ j % (2 * (m : ℤ)) := Int.emod_nonneg _ (by omega)
  have hr2 : j % (2 * (m : ℤ)) < 2 * (m : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hr : (r : ℤ) = j % (2 * (m : ℤ)) := Int.toNat_of_nonneg hr0
  have hrm : r < 2 * m := by omega
  have hred : labelledCycleDirection O j = labelledCycleDirection O (r : ℤ) := by
    apply gp_cycle_congr
    rw [hr, Int.emod_emod]
  have hred' : labelledCycleDirection O (j + m) = labelledCycleDirection O ((r : ℤ) + m) := by
    apply gp_cycle_congr
    simp only [Int.add_emod, hr, Int.emod_emod]
  rw [hred', hred]
  by_cases hlt : r < m
  · rw [gp_cycle_first O r hlt]
    have he : (r : ℤ) + m = ((r + m : ℕ) : ℤ) := by omega
    rw [he, gp_cycle_second O (r + m) (by omega) (by omega)]
    simp
  · have hle : m ≤ r := by omega
    rw [gp_cycle_second O r hle hrm]
    have he : (r : ℤ) + m = ((r - m : ℕ) : ℤ) + 2 * (m : ℤ) := by omega
    rw [he, gp_cycle_periodic, gp_cycle_first O (r - m) (by omega)]
    simp

private theorem gp_order_no_parallel {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i j : Fin m) (he : det (O.direction i) (O.direction j) = 0) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hh := O.ordered_turn i j hij
    omega
  · have hh := O.ordered_turn j i hji
    have ha : det (O.direction j) (O.direction i) = -det (O.direction i) (O.direction j) := by
      simp [det]; ring
    rw [ha, he] at hh
    omega

private theorem gp_order_not_neg {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i j : Fin m) : O.direction i ≠ -O.direction j := by
  intro he
  have hdet : det (O.direction i) (O.direction j) = 0 := by rw [he]; simp [det]; ring
  have hij := gp_order_no_parallel O i j hdet
  subst j
  have hz : O.direction i = 0 := by
    apply Prod.ext
    · have hh := congrArg Prod.fst he
      change (O.direction i).1 = -(O.direction i).1 at hh
      change (O.direction i).1 = 0
      omega
    · have hh := congrArg Prod.snd he
      change (O.direction i).2 = -(O.direction i).2 at hh
      change (O.direction i).2 = 0
      omega
  exact primitive_ne_zero _ (O.primitive i) hz

private theorem gp_cycle_injective {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) :
    Function.Injective (fun i : Fin (2 * m) => labelledCycleDirection O (i.val : ℤ)) := by
  intro i j he
  change labelledCycleDirection O (i.val : ℤ) = labelledCycleDirection O (j.val : ℤ) at he
  by_cases hi : i.val < m <;> by_cases hj : j.val < m
  · rw [gp_cycle_first O i.val hi, gp_cycle_first O j.val hj] at he
    have hdet : det (O.direction ⟨i.val, hi⟩) (O.direction ⟨j.val, hj⟩) = 0 := by rw [he]; simp [det]; ring
    have hij := gp_order_no_parallel O ⟨i.val, hi⟩ ⟨j.val, hj⟩ hdet
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hij)
  · rw [gp_cycle_first O i.val hi, gp_cycle_second O j.val (by omega) j.isLt] at he
    exact (gp_order_not_neg O _ _ he).elim
  · rw [gp_cycle_second O i.val (by omega) i.isLt, gp_cycle_first O j.val hj] at he
    exact (gp_order_not_neg O _ _ he.symm).elim
  · rw [gp_cycle_second O i.val (by omega) i.isLt, gp_cycle_second O j.val (by omega) j.isLt] at he
    have he' := neg_injective he
    have hdet : det (O.direction ⟨i.val - m, by omega⟩) (O.direction ⟨j.val - m, by omega⟩) = 0 := by
      rw [he']; simp [det]; ring
    have hij := gp_order_no_parallel O _ _ hdet
    have hh := congrArg Fin.val hij
    apply Fin.ext
    dsimp at hh
    omega

private theorem gp_cycle_turn_first {m : ℕ} (hm : 2 ≤ m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i : ℕ) (hi : i < m) :
    0 < det (labelledCycleDirection O (i : ℤ))
      (labelledCycleDirection O ((i : ℤ) + 1)) := by
  rw [gp_cycle_first O i hi]
  have hcast : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by omega
  rw [hcast]
  by_cases hs : i + 1 < m
  · rw [gp_cycle_first O (i + 1) hs]
    exact O.ordered_turn _ _ (by change i < i + 1; omega)
  · have his : i + 1 = m := by omega
    rw [his, gp_cycle_second O m (le_refl _) (by omega)]
    have hzero : m - m = 0 := Nat.sub_self _
    have hz : (⟨m - m, by omega⟩ : Fin m) = ⟨0, by omega⟩ := by apply Fin.ext; omega
    rw [hz]
    have heq : det (O.direction ⟨i, hi⟩) (-O.direction ⟨0, by omega⟩) =
        det (O.direction ⟨0, by omega⟩) (O.direction ⟨i, hi⟩) := by simp [det]; ring
    rw [heq]
    exact O.ordered_turn _ _ (by change 0 < i; omega)

private theorem gp_cycle_turn {m : ℕ} (hm : 2 ≤ m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) :
    0 < det (labelledCycleDirection O j) (labelledCycleDirection O (j + 1)) := by
  let r := (j % (2 * (m : ℤ))).toNat
  have hr0 : 0 ≤ j % (2 * (m : ℤ)) := Int.emod_nonneg _ (by omega)
  have hr2 : j % (2 * (m : ℤ)) < 2 * (m : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hr : (r : ℤ) = j % (2 * (m : ℤ)) := Int.toNat_of_nonneg hr0
  have hrm : r < 2 * m := by omega
  have hred : labelledCycleDirection O j = labelledCycleDirection O (r : ℤ) := by
    apply gp_cycle_congr
    rw [hr, Int.emod_emod]
  have hred' : labelledCycleDirection O (j + 1) = labelledCycleDirection O ((r : ℤ) + 1) := by
    apply gp_cycle_congr
    simp only [Int.add_emod, hr, Int.emod_emod]
  rw [hred, hred']
  by_cases hlt : r < m
  · exact gp_cycle_turn_first hm O r hlt
  · have he : (r : ℤ) = ((r - m : ℕ) : ℤ) + m := by omega
    have he' : (r : ℤ) + 1 = (((r - m : ℕ) : ℤ) + 1) + m := by omega
    rw [he', he, gp_cycle_antipodal (by omega), gp_cycle_antipodal (by omega)]
    have hdet : ∀ x y : Lattice, det (-x) (-y) = det x y := by intro x y; simp [det]
    rw [hdet]
    exact gp_cycle_turn_first hm O (r - m) (by omega)

/-- GP07: arbitrary factor labels are retained in the generic determinant sort. -/
theorem generic_labelled_antipodal_direction_order (m : ℕ) (hm : 2 ≤ m)
    (h : Fin m → Lattice) (hne : ∀ i, h i ≠ 0)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j))) :
    ∃ O : LabelledFactorOrder m h,
      Function.Injective (fun i : Fin (2 * m) => labelledCycleDirection O (i.val : ℤ)) ∧
      (∀ j : ℤ, labelledCycleDirection O (j + 2 * (m : ℤ)) = labelledCycleDirection O j) ∧
      (∀ j : ℤ, labelledCycleDirection O (j + (m : ℤ)) = -labelledCycleDirection O j) ∧
      ∀ j : ℤ, 0 < det (labelledCycleDirection O j) (labelledCycleDirection O (j + 1)) := by
  obtain ⟨O⟩ := gp_labelled_order m h hne hpair
  exact ⟨O, gp_cycle_injective O, gp_cycle_periodic O,
    gp_cycle_antipodal (by omega) O, gp_cycle_turn hm O⟩

end
end ConvexNivat.Colle
