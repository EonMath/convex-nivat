import ConvexNivat.Colle.GP.ProductDirections
import ConvexNivat.Colle.GP.Primitive

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

private theorem pg_embed_zsmul (k : ℤ) (v : Lattice) :
    embed (k • v) = (k : ℝ) • embed v := by
  ext <;> simp [embed, smul_eq_mul]

private theorem pg_embed_sum {m : ℕ} (v : Fin m → Lattice) :
    embed (∑ i, v i) = ∑ i, embed (v i) := by
  ext <;> simp [embed, Prod.fst_sum, Prod.snd_sum]

private theorem pg_oriented_hull {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) :
    reflectedFactorHull m h =
      {x | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ (O.scale i : ℝ)) ∧
        x = embed (labelledHullAnchor O) + ∑ i, t i • embed (O.direction i)} := by
  classical
  have he (i : Fin m) : embed (-h (O.label i)) =
      ((-(O.sign i : ℝ)) * (O.scale i : ℝ)) • embed (O.direction i) := by
    rw [O.factor_eq i]
    ext <;> simp [embed, smul_eq_mul] <;> ring
  have ha : embed (labelledHullAnchor O) = ∑ i,
      if O.sign i = 1 then -(O.scale i : ℝ) • embed (O.direction i) else 0 := by
    rw [labelledHullAnchor, pg_embed_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hs
    · rw [he, hs]; simp
    · simp [embed]
  have hp (i : Fin m) : (0 : ℝ) < O.scale i := Nat.cast_pos.mpr (O.scale_positive i)
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    let u (i : Fin m) := if O.sign i = 1 then
      (1 - t (O.label i)) * (O.scale i : ℝ) else t (O.label i) * (O.scale i : ℝ)
    refine ⟨u, ?_, ?_⟩
    · intro i
      dsimp [u]
      split_ifs <;> constructor <;> nlinarith [(ht (O.label i)).1, (ht (O.label i)).2, hp i]
    · rw [hx, ha, ← Finset.sum_add_distrib, ← O.label.sum_comp]
      apply Finset.sum_congr rfl
      intro i hi
      rw [he]
      rcases O.sign_unit i with hs | hs
      · simp only [u, hs, ite_true, Int.cast_one, neg_mul, one_mul, smul_smul, ← add_smul]
        congr 1
        ring
      · simp only [u, hs, show (-1 : ℤ) ≠ 1 by omega, ite_false, Int.cast_neg,
          Int.cast_one, neg_neg, one_mul, zero_add, smul_smul]
  · rintro ⟨u, hu, hx⟩
    let t (j : Fin m) := if O.sign (O.label.symm j) = 1 then
      1 - u (O.label.symm j) / (O.scale (O.label.symm j) : ℝ)
      else u (O.label.symm j) / (O.scale (O.label.symm j) : ℝ)
    have ht : ∀ j, 0 ≤ t j ∧ t j ≤ 1 := by
      intro j
      have hl := div_nonneg (hu (O.label.symm j)).1 (hp (O.label.symm j)).le
      have hh := (div_le_one (hp (O.label.symm j))).mpr (hu (O.label.symm j)).2
      dsimp [t]
      split_ifs <;> constructor <;> linarith
    refine ⟨t, ht, ?_⟩
    rw [hx, ha, ← Finset.sum_add_distrib]
    conv_rhs => rw [← O.label.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he]
    simp only [t, O.label.symm_apply_apply]
    rcases O.sign_unit i with hs | hs
    · simp only [hs, ite_true, Int.cast_one, neg_mul, one_mul, smul_smul, ← add_smul]
      congr 1
      field_simp [(hp i).ne']
      ring
    · simp only [hs, show (-1 : ℤ) ≠ 1 by omega, ite_false, Int.cast_neg,
        Int.cast_one, neg_neg, one_mul, zero_add, smul_smul]
      rw [div_mul_cancel₀ _ (hp i).ne']

private theorem pg_support_real_face (S : Finset Lattice) (hc : LatticeConvex S)
    (n : RealPlane) (z : Lattice) :
    z ∈ supportFace S n ↔ embed z ∈ windowHull S ∧
      ∀ y ∈ windowHull S, realDot (embed z) n ≤ realDot y n := by
  constructor
  · intro hz
    obtain ⟨hz, hmin⟩ := Finset.mem_filter.mp hz
    refine ⟨(hc z).mpr hz, ?_⟩
    apply convexHull_min
    · rintro _ ⟨q, hq, rfl⟩
      exact hmin q hq
    · refine convex_halfSpace_ge (f := fun x : RealPlane => realDot x n) ?_ _
      constructor
      · intro a b; simp [realDot]; ring
      · intro a b; simp [realDot]; ring
  · rintro ⟨hz, hmin⟩
    exact Finset.mem_filter.mpr ⟨(hc z).mp hz, fun q hq => hmin _ ((hc q).mpr hq)⟩

private theorem pg_dot_translate (a x n : RealPlane) :
    realDot (a + x) n = realDot a n + realDot x n := by
  simp [realDot]
  ring

private theorem pg_oriented_face {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (hne : ∀ i, h i ≠ 0)
    (n : RealPlane) (hn : n ≠ 0) (z : Lattice) :
    z ∈ supportFace (supportWindow (differenceFactors m h)) n ↔
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
      (∀ i, realDot (embed ((O.scale i : ℤ) • O.direction i)) n < 0 → t i = 1) ∧
      (∀ i, 0 < realDot (embed ((O.scale i : ℤ) • O.direction i)) n → t i = 0) ∧
      embed z = embed (labelledHullAnchor O) +
        ∑ i, t i • embed ((O.scale i : ℤ) • O.direction i) := by
  let g : Fin m → Lattice := fun i => -((O.scale i : ℤ) • O.direction i)
  let Z : IntegralZonotope m := ⟨O.direction, O.scale, O.scale_positive⟩
  have hz : reflectedFactorHull m g = Z.carrier :=
    reflected_factor_hull_integral_zonotope m g Z (by intro i; simp [g, Z])
  have hh : windowHull (supportWindow (differenceFactors m h)) =
      (fun x => embed (labelledHullAnchor O) + x) '' reflectedFactorHull m g := by
    rw [(reflected_difference_product_actual_zonotope m h hne).2, pg_oriented_hull,
      hz]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
  have hc : LatticeConvex (supportWindow (differenceFactors m h)) := by
    intro q
    rw [supportWindow, convexLatticeWindow_hull]
    exact (lattice_windowHull_finite _).mem_toFinset.symm
  rw [pg_support_real_face _ hc, hh]
  have he := zonotope_exposed_face_parameter_classification m g n hn
  simp only [g, neg_neg] at he
  constructor
  · rintro ⟨⟨x, hx, hxe⟩, hmin⟩
    have hm : ∀ y ∈ reflectedFactorHull m g, realDot x n ≤ realDot y n := by
      intro y hy
      have hh := hmin (embed (labelledHullAnchor O) + y) ⟨y, hy, rfl⟩
      rw [← hxe, pg_dot_translate, pg_dot_translate] at hh
      linarith
    have hxp : x ∈ {x | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
        (∀ i, realDot (embed ((O.scale i : ℤ) • O.direction i)) n < 0 → t i = 1) ∧
        (∀ i, 0 < realDot (embed ((O.scale i : ℤ) • O.direction i)) n → t i = 0) ∧
        x = ∑ i, t i • embed ((O.scale i : ℤ) • O.direction i)} := by
      rw [← he]
      exact ⟨hx, hm⟩
    obtain ⟨t, ht, htn, htp, hte⟩ := hxp
    exact ⟨t, ht, htn, htp, by rw [← hxe, hte]⟩
  · rintro ⟨t, ht, htn, htp, hte⟩
    let x : RealPlane := ∑ i, t i • embed ((O.scale i : ℤ) • O.direction i)
    have hxp : x ∈ reflectedFactorHull m g ∧
        ∀ y ∈ reflectedFactorHull m g, realDot x n ≤ realDot y n := by
      change x ∈ {x | x ∈ reflectedFactorHull m g ∧
        ∀ y ∈ reflectedFactorHull m g, realDot x n ≤ realDot y n}
      rw [he]
      exact ⟨t, ht, htn, htp, rfl⟩
    refine ⟨⟨x, hxp.1, hte.symm⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hte, pg_dot_translate, pg_dot_translate]
    simpa only [add_comm] using add_le_add_left (hxp.2 y hy)
      (realDot (embed (labelledHullAnchor O)) n)

private def pg_lowerVertex {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (n : RealPlane) : Lattice :=
  labelledHullAnchor O + ∑ j, if realDot (embed ((O.scale j : ℤ) • O.direction j)) n < 0
    then (O.scale j : ℤ) • O.direction j else 0

private theorem pg_face_segment {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (hne : ∀ i, h i ≠ 0)
    (n : RealPlane) (hn : n ≠ 0) (i : Fin m)
    (hi : realDot (embed ((O.scale i : ℤ) • O.direction i)) n = 0)
    (hother : ∀ j, j ≠ i → realDot (embed ((O.scale j : ℤ) • O.direction j)) n ≠ 0)
    (z : Lattice) :
    z ∈ supportFace (supportWindow (differenceFactors m h)) n ↔
      embed z ∈ segment ℝ (embed (pg_lowerVertex O n))
        (embed (pg_lowerVertex O n + (O.scale i : ℤ) • O.direction i)) := by
  classical
  let E (j : Fin m) := (O.scale j : ℤ) • O.direction j
  let c (j : Fin m) := realDot (embed (E j)) n
  let s (j : Fin m) : ℝ := if c j < 0 then 1 else 0
  have hsi : s i = 0 := by simp only [s, c, E, hi, lt_self_iff_false, ite_false]
  have hbase : embed (pg_lowerVertex O n) = embed (labelledHullAnchor O) +
      ∑ j, s j • embed (E j) := by
    rw [pg_lowerVertex, embed_add, pg_embed_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [s, c, E]
    split_ifs <;> simp [embed]
  have hsum (r : ℝ) :
      embed (labelledHullAnchor O) + ∑ j,
        (s j + if j = i then r else 0) • embed (E j) =
      embed (pg_lowerVertex O n) + r • embed (E i) := by
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hbase]
    abel
  have hsegment : embed z ∈ segment ℝ (embed (pg_lowerVertex O n))
      (embed (pg_lowerVertex O n + E i)) ↔
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
        embed z = embed (pg_lowerVertex O n) + r • embed (E i) := by
    rw [segment_eq_image]
    constructor
    · rintro ⟨r, hr, he⟩
      refine ⟨r, hr.1, hr.2, ?_⟩
      rw [← he, embed_add]
      ext <;> simp <;> ring
    · rintro ⟨r, hr0, hr1, he⟩
      refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
      rw [he, embed_add]
      ext <;> simp <;> ring
  rw [pg_oriented_face O hne n hn z, hsegment]
  constructor
  · rintro ⟨t, ht, htn, htp, hte⟩
    have hformula (j : Fin m) : t j = s j + if j = i then t i else 0 := by
      by_cases hji : j = i
      · subst j; simp [hsi]
      · rcases lt_or_gt_of_ne (hother j hji) with hj | hj
        · simp only [hji, s, c, E, hj, htn j hj, ite_true, ite_false, add_zero]
        · simp only [hji, s, c, E, not_lt_of_ge hj.le, htp j hj, ite_false, add_zero]
    refine ⟨t i, (ht i).1, (ht i).2, ?_⟩
    rw [hte]
    have hfun : t = fun j => s j + if j = i then t i else 0 := funext hformula
    calc
      _ = embed (labelledHullAnchor O) + ∑ j,
          (s j + if j = i then t i else 0) • embed (E j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun a : ℝ => a • embed (E j)) (hformula j)
      _ = _ := hsum (t i)
  · rintro ⟨r, hr0, hr1, he⟩
    refine ⟨fun j => s j + if j = i then r else 0, ?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j; simpa [hsi] using And.intro hr0 hr1
      · simp only [hji, ite_false, add_zero, s]
        split_ifs <;> norm_num
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; rw [hi] at hj; linarith
      simp only [hji, s, c, E, hj, ite_true, ite_false, add_zero]
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; rw [hi] at hj; linarith
      simp only [hji, s, c, E, not_lt_of_ge hj.le, ite_false, add_zero]
    · exact he.trans (hsum r).symm

private def pg_prefix {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (r : ℕ) : Lattice :=
  ∑ i, if i.val < r then (O.scale i : ℤ) • O.direction i else 0

private def pg_suffix {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (r : ℕ) : Lattice :=
  ∑ i, if r ≤ i.val then (O.scale i : ℤ) • O.direction i else 0

private theorem pg_prefix_succ {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i : Fin m) :
    pg_prefix O (i.val + 1) = pg_prefix O i.val + (O.scale i : ℤ) • O.direction i := by
  classical
  have he (j : Fin m) : (if j.val < i.val + 1 then (O.scale j : ℤ) • O.direction j else 0) =
      (if j.val < i.val then (O.scale j : ℤ) • O.direction j else 0) +
        if j = i then (O.scale i : ℤ) • O.direction i else 0 := by
    by_cases hj : j = i
    · subst j; simp
    · have hji : j.val ≠ i.val := fun hh => hj (Fin.ext hh)
      split_ifs <;> simp_all <;> omega
  simp only [pg_prefix, he, Finset.sum_add_distrib]
  simp

private theorem pg_suffix_succ {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i : Fin m) :
    pg_suffix O i.val = pg_suffix O (i.val + 1) + (O.scale i : ℤ) • O.direction i := by
  classical
  have he (j : Fin m) : (if i.val ≤ j.val then (O.scale j : ℤ) • O.direction j else 0) =
      (if i.val + 1 ≤ j.val then (O.scale j : ℤ) • O.direction j else 0) +
        if j = i then (O.scale i : ℤ) • O.direction i else 0 := by
    by_cases hj : j = i
    · subst j; simp
    · have hji : j.val ≠ i.val := fun hh => hj (Fin.ext hh)
      split_ifs <;> simp_all <;> omega
  simp only [pg_suffix, he, Finset.sum_add_distrib]
  simp

private theorem pg_scaled_normal_dot {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i j : Fin m) :
    realDot (embed ((O.scale j : ℤ) • O.direction j)) (normal (O.direction i)) =
      (O.scale j : ℝ) * (det (O.direction i) (O.direction j) : ℝ) := by
  rw [normal_height]
  simp [det, smul_eq_mul]
  ring

private theorem pg_dot_sign {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i j : Fin m) :
    (realDot (embed ((O.scale j : ℤ) • O.direction j)) (normal (O.direction i)) < 0 ↔ j < i) ∧
    (0 < realDot (embed ((O.scale j : ℤ) • O.direction j)) (normal (O.direction i)) ↔ i < j) := by
  rw [pg_scaled_normal_dot]
  have hp : (0 : ℝ) < O.scale j := Nat.cast_pos.mpr (O.scale_positive j)
  rcases lt_trichotomy i j with hij | hij | hij
  · have ht : (0 : ℝ) < det (O.direction i) (O.direction j) := by
      exact_mod_cast O.ordered_turn i j hij
    constructor <;> constructor <;> intro hh <;> first
      | exact hij
      | exact (mul_pos hp ht)
      | exact (not_lt_of_ge (mul_pos hp ht).le hh).elim
      | exact (not_lt_of_ge hij.le hh).elim
  · subst j
    simp [det, mul_comm]
  · have ha : det (O.direction i) (O.direction j) = -det (O.direction j) (O.direction i) := by
      simp [det]; ring
    have ht : (det (O.direction i) (O.direction j) : ℝ) < 0 := by
      rw [ha, Int.cast_neg]
      exact neg_neg_of_pos (by exact_mod_cast O.ordered_turn j i hij)
    constructor <;> constructor <;> intro hh <;> first
      | exact hij
      | exact (mul_neg_of_pos_of_neg hp ht)
      | exact (not_lt_of_ge (mul_neg_of_pos_of_neg hp ht).le hh).elim
      | exact (not_lt_of_ge hij.le hh).elim

private theorem pg_normal_ne (d : Lattice) (hd : Primitive d) : normal d ≠ 0 := by
  intro he
  apply primitive_ne_zero d hd
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  exact Prod.ext (by simpa [normal] using h2) (by simpa [normal] using h1)

private theorem pg_first_segment {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (hne : ∀ i, h i ≠ 0) (i : Fin m) (z : Lattice) :
    z ∈ supportRow (supportWindow (differenceFactors m h)) (O.direction i) ↔
      embed z ∈ segment ℝ (embed (labelledHullAnchor O + pg_prefix O i.val))
        (embed (labelledHullAnchor O + pg_prefix O (i.val + 1))) := by
  classical
  have hbase : pg_lowerVertex O (normal (O.direction i)) =
      labelledHullAnchor O + pg_prefix O i.val := by
    unfold pg_lowerVertex pg_prefix
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [(pg_dot_sign O i j).1, Fin.lt_def]
  have hi : realDot (embed ((O.scale i : ℤ) • O.direction i))
      (normal (O.direction i)) = 0 := by
    rw [pg_scaled_normal_dot]
    simp [det, mul_comm]
  have hother (j : Fin m) (hj : j ≠ i) :
      realDot (embed ((O.scale j : ℤ) • O.direction j)) (normal (O.direction i)) ≠ 0 := by
    rcases lt_or_gt_of_ne hj with hji | hij
    · exact ne_of_lt ((pg_dot_sign O i j).1.mpr hji)
    · exact ne_of_gt ((pg_dot_sign O i j).2.mpr hij)
  have he := pg_face_segment O hne _ (pg_normal_ne _ (O.primitive i)) i hi hother z
  rw [hbase] at he
  rw [pg_prefix_succ]
  simpa only [supportRow, add_assoc] using he

private theorem pg_second_segment {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (hne : ∀ i, h i ≠ 0) (i : Fin m) (z : Lattice) :
    z ∈ supportRow (supportWindow (differenceFactors m h)) (-O.direction i) ↔
      embed z ∈ segment ℝ (embed (labelledHullAnchor O + pg_suffix O i.val))
        (embed (labelledHullAnchor O + pg_suffix O (i.val + 1))) := by
  classical
  have hdot (j : Fin m) : realDot (embed ((O.scale j : ℤ) • O.direction j))
      (normal (-O.direction i)) =
      -realDot (embed ((O.scale j : ℤ) • O.direction j)) (normal (O.direction i)) := by
    simp [normal, realDot]
    ring
  have hbase : pg_lowerVertex O (normal (-O.direction i)) =
      labelledHullAnchor O + pg_suffix O (i.val + 1) := by
    unfold pg_lowerVertex pg_suffix
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have he : i < j ↔ i.val + 1 ≤ j.val := by omega
    simp only [hdot, neg_lt_zero, (pg_dot_sign O i j).2, he]
  have hi : realDot (embed ((O.scale i : ℤ) • O.direction i))
      (normal (-O.direction i)) = 0 := by
    rw [hdot, pg_scaled_normal_dot]
    simp [det, mul_comm]
  have hother (j : Fin m) (hj : j ≠ i) :
      realDot (embed ((O.scale j : ℤ) • O.direction j)) (normal (-O.direction i)) ≠ 0 := by
    rw [hdot]
    apply neg_ne_zero.mpr
    rcases lt_or_gt_of_ne hj with hji | hij
    · exact ne_of_lt ((pg_dot_sign O i j).1.mpr hji)
    · exact ne_of_gt ((pg_dot_sign O i j).2.mpr hij)
  have hn : normal (-O.direction i) ≠ 0 := pg_normal_ne _ (by simpa [Primitive] using O.primitive i)
  have he := pg_face_segment O hne _ hn i hi hother z
  rw [hbase] at he
  rw [pg_suffix_succ O i, segment_symm]
  simpa only [supportRow, add_assoc] using he

private theorem pg_cycle_congr {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j k : ℤ)
    (he : j % (2 * (m : ℤ)) = k % (2 * (m : ℤ))) :
    labelledCycleDirection O j = labelledCycleDirection O k := by
  unfold labelledCycleDirection
  rw [he]

private theorem pg_cycle_periodic {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) :
    labelledCycleDirection O (j + 2 * (m : ℤ)) = labelledCycleDirection O j := by
  apply pg_cycle_congr
  simp

private theorem pg_cycle_first {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i : ℕ) (hi : i < m) :
    labelledCycleDirection O (i : ℤ) = O.direction ⟨i, hi⟩ := by
  have hm : 0 < m := by omega
  have hmod : (i : ℤ) % (2 * (m : ℤ)) = i :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  simp [labelledCycleDirection, hm, hmod, Nat.mod_eq_of_lt hi, hi]

private theorem pg_cycle_second {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i : ℕ) (hi : m ≤ i) (hi2 : i < 2 * m) :
    labelledCycleDirection O (i : ℤ) = -O.direction ⟨i - m, by omega⟩ := by
  have hm : 0 < m := by omega
  have hmod : (i : ℤ) % (2 * (m : ℤ)) = i :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  have hnat : i % m = i - m := by
    rw [Nat.mod_eq_sub_mod hi, Nat.mod_eq_of_lt (by omega)]
  simp [labelledCycleDirection, hm, hmod, show ¬ i < m by omega, hnat]

private theorem pg_vertex_periodic {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) :
    labelledCycleVertex O (j + 2 * (m : ℤ)) = labelledCycleVertex O j := by
  have he : (j + 2 * (m : ℤ)) % (2 * (m : ℤ)) = j % (2 * (m : ℤ)) := by simp
  simp only [labelledCycleVertex, he]

private theorem pg_vertex_first {m : ℕ} (hm : 0 < m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (r : ℕ) (hr : r ≤ m) :
    labelledCycleVertex O (r : ℤ) = labelledHullAnchor O + pg_prefix O r := by
  have hmod : (r : ℤ) % (2 * (m : ℤ)) = r :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  simp only [labelledCycleVertex, hmod, Int.toNat_natCast, hr, ite_true, pg_prefix]

private theorem pg_vertex_second {m : ℕ} (hm : 0 < m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (r : ℕ) (hr : r ≤ m) :
    labelledCycleVertex O ((m : ℤ) + r) = labelledHullAnchor O + pg_suffix O r := by
  by_cases hr0 : r = 0
  · subst r
    rw [Nat.cast_zero, add_zero, pg_vertex_first hm O m le_rfl]
    simp [pg_prefix, pg_suffix]
  by_cases hrm : r = m
  · subst r
    rw [show (m : ℤ) + m = 0 + 2 * (m : ℤ) by ring, pg_vertex_periodic]
    simp [labelledCycleVertex, pg_suffix, hm, show ∀ i : Fin m, ¬m ≤ i.val by
      intro i; exact Nat.not_le.mpr i.isLt]
  · have hmod : ((m : ℤ) + r) % (2 * (m : ℤ)) = (m : ℤ) + r :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have hnat : ((m : ℤ) + r).toNat = m + r := by omega
    simp [labelledCycleVertex, hmod, hnat, show ¬m + r ≤ m by omega, pg_suffix]

private theorem pg_cycle_antipodal {m : ℕ} (hm : 0 < m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (j : ℤ) :
    labelledCycleDirection O (j + (m : ℤ)) = -labelledCycleDirection O j := by
  let r := (j % (2 * (m : ℤ))).toNat
  have hr0 : 0 ≤ j % (2 * (m : ℤ)) := Int.emod_nonneg _ (by omega)
  have hr2 : j % (2 * (m : ℤ)) < 2 * (m : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hr : (r : ℤ) = j % (2 * (m : ℤ)) := Int.toNat_of_nonneg hr0
  have hrm : r < 2 * m := by omega
  have hred : labelledCycleDirection O j = labelledCycleDirection O (r : ℤ) := by
    apply pg_cycle_congr
    rw [hr, Int.emod_emod]
  have hred' : labelledCycleDirection O (j + m) = labelledCycleDirection O ((r : ℤ) + m) := by
    apply pg_cycle_congr
    simp only [Int.add_emod, hr, Int.emod_emod]
  rw [hred', hred]
  by_cases hlt : r < m
  · rw [pg_cycle_first O r hlt]
    have he : (r : ℤ) + m = ((r + m : ℕ) : ℤ) := by omega
    rw [he, pg_cycle_second O (r + m) (by omega) (by omega)]
    simp
  · have hle : m ≤ r := by omega
    rw [pg_cycle_second O r hle hrm]
    have he : (r : ℤ) + m = ((r - m : ℕ) : ℤ) + 2 * (m : ℤ) := by omega
    rw [he, pg_cycle_periodic, pg_cycle_first O (r - m) (by omega)]
    simp

private theorem pg_order_no_parallel {m : ℕ} {h : Fin m → Lattice}
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

private theorem pg_order_not_neg {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (i j : Fin m) : O.direction i ≠ -O.direction j := by
  intro he
  have hdet : det (O.direction i) (O.direction j) = 0 := by rw [he]; simp [det]; ring
  have hij := pg_order_no_parallel O i j hdet
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

private theorem pg_cycle_injective {m : ℕ} {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) :
    Function.Injective (fun i : Fin (2 * m) => labelledCycleDirection O (i.val : ℤ)) := by
  intro i j he
  change labelledCycleDirection O (i.val : ℤ) = labelledCycleDirection O (j.val : ℤ) at he
  by_cases hi : i.val < m <;> by_cases hj : j.val < m
  · rw [pg_cycle_first O i.val hi, pg_cycle_first O j.val hj] at he
    have hdet : det (O.direction ⟨i.val, hi⟩) (O.direction ⟨j.val, hj⟩) = 0 := by rw [he]; simp [det]; ring
    have hij := pg_order_no_parallel O ⟨i.val, hi⟩ ⟨j.val, hj⟩ hdet
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hij)
  · rw [pg_cycle_first O i.val hi, pg_cycle_second O j.val (by omega) j.isLt] at he
    exact (pg_order_not_neg O _ _ he).elim
  · rw [pg_cycle_second O i.val (by omega) i.isLt, pg_cycle_first O j.val hj] at he
    exact (pg_order_not_neg O _ _ he.symm).elim
  · rw [pg_cycle_second O i.val (by omega) i.isLt, pg_cycle_second O j.val (by omega) j.isLt] at he
    have he' := neg_injective he
    have hdet : det (O.direction ⟨i.val - m, by omega⟩) (O.direction ⟨j.val - m, by omega⟩) = 0 := by
      rw [he']; simp [det]; ring
    have hij := pg_order_no_parallel O _ _ hdet
    have hh := congrArg Fin.val hij
    apply Fin.ext
    dsimp at hh
    omega


private theorem pg_finite_edges {m : ℕ} (hm : 0 < m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (hne : ∀ i, h i ≠ 0) (r : ℕ) (hr : r < 2 * m) :
    Primitive (labelledCycleDirection O (r : ℤ)) ∧
    (∃ k : ℤ, 1 ≤ k ∧ labelledCycleVertex O ((r : ℤ) + 1) - labelledCycleVertex O r =
      k • labelledCycleDirection O r) ∧
    (∀ z : Lattice, z ∈ supportRow (supportWindow (differenceFactors m h))
      (labelledCycleDirection O r) ↔ embed z ∈ segment ℝ
        (embed (labelledCycleVertex O r)) (embed (labelledCycleVertex O ((r : ℤ) + 1)))) := by
  by_cases hrm : r < m
  · let i : Fin m := ⟨r, hrm⟩
    rw [pg_cycle_first O r hrm, pg_vertex_first hm O r hrm.le,
      show (r : ℤ) + 1 = ((r + 1 : ℕ) : ℤ) by omega,
      pg_vertex_first hm O (r + 1) (by omega)]
    refine ⟨O.primitive i, ⟨(O.scale i : ℤ), by exact_mod_cast O.scale_positive i, ?_⟩,
      pg_first_segment O hne i⟩
    have he := pg_prefix_succ O i
    dsimp only [i] at he
    rw [he]
    abel
  · let i : Fin m := ⟨r - m, by omega⟩
    rw [pg_cycle_second O r (by omega) hr]
    have hr0 : (r : ℤ) = (m : ℤ) + (i.val : ℤ) := by dsimp [i]; omega
    have hr1 : (r : ℤ) + 1 = (m : ℤ) + ((i.val + 1 : ℕ) : ℤ) := by dsimp [i]; omega
    rw [hr1, hr0, pg_vertex_second hm O i.val i.isLt.le,
      pg_vertex_second hm O (i.val + 1) (by have := i.isLt; omega)]
    refine ⟨by simpa [Primitive] using O.primitive i,
      ⟨(O.scale i : ℤ), by exact_mod_cast O.scale_positive i, ?_⟩, pg_second_segment O hne i⟩
    rw [pg_suffix_succ O i, smul_neg]
    abel

private theorem pg_all_edges {m : ℕ} (hm : 0 < m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (hne : ∀ i, h i ≠ 0) (j : ℤ) :
    Primitive (labelledCycleDirection O j) ∧
    (∃ k : ℤ, 1 ≤ k ∧ labelledCycleVertex O (j + 1) - labelledCycleVertex O j =
      k • labelledCycleDirection O j) ∧
    (∀ z : Lattice, z ∈ supportRow (supportWindow (differenceFactors m h))
      (labelledCycleDirection O j) ↔ embed z ∈ segment ℝ
        (embed (labelledCycleVertex O j)) (embed (labelledCycleVertex O (j + 1)))) := by
  let r := (j % (2 * (m : ℤ))).toNat
  have hr0 := Int.emod_nonneg j (by omega : 2 * (m : ℤ) ≠ 0)
  have hr2 := Int.emod_lt_of_pos j (by omega : 0 < 2 * (m : ℤ))
  have hr : (r : ℤ) = j % (2 * (m : ℤ)) := Int.toNat_of_nonneg hr0
  have hrm : r < 2 * m := by omega
  have he : j % (2 * (m : ℤ)) = (r : ℤ) % (2 * (m : ℤ)) := by
    rw [hr, Int.emod_emod]
  have he1 : (j + 1) % (2 * (m : ℤ)) = ((r : ℤ) + 1) % (2 * (m : ℤ)) := by
    calc
      _ = (j % (2 * (m : ℤ)) + 1 % (2 * (m : ℤ))) % (2 * (m : ℤ)) :=
        Int.add_emod _ _ _
      _ = ((r : ℤ) % (2 * (m : ℤ)) + 1 % (2 * (m : ℤ))) % (2 * (m : ℤ)) := by rw [he]
      _ = _ := (Int.add_emod _ _ _).symm
  have hD := pg_cycle_congr O j r he
  have hV : labelledCycleVertex O j = labelledCycleVertex O r := by
    unfold labelledCycleVertex
    rw [he]
  have hV1 : labelledCycleVertex O (j + 1) = labelledCycleVertex O ((r : ℤ) + 1) := by
    unfold labelledCycleVertex
    rw [he1]
  rw [hD, hV, hV1]
  exact pg_finite_edges hm O hne r hrm

private theorem pg_direction_covers {m : ℕ} (hm : 2 ≤ m) {h : Fin m → Lattice}
    (O : LabelledFactorOrder m h) (hne : ∀ i, h i ≠ 0)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j))) (d : Lattice) :
    d ∈ edgeDirections (supportWindow (differenceFactors m h)) ↔
      ∃ i : Fin (2 * m), labelledCycleDirection O (i.val : ℤ) = d := by
  have he (d : Lattice) (j : Fin m) : det d (h (O.label j)) =
      (O.sign j * (O.scale j : ℤ)) * det d (O.direction j) := by
    rw [O.factor_eq j]
    simp [det]
    ring
  have hscale (j : Fin m) : O.sign j * (O.scale j : ℤ) ≠ 0 := by
    apply mul_ne_zero
    · rcases O.sign_unit j with hj | hj <;> simp [hj]
    · exact_mod_cast (O.scale_positive j).ne'
  constructor
  · intro hd
    obtain ⟨i, hi⟩ :=
      (zonotope_exposed_face_direction_classification m hm h hne hpair d hd.1).1.mp hd
    let j := O.label.symm i
    have hj : det d (O.direction j) = 0 := by
      have hh : det d (h (O.label j)) = 0 := by simpa [j] using hi
      rw [he] at hh
      exact (mul_eq_zero.mp hh).resolve_left (hscale j)
    rcases primitive_parallel_orientation d (O.direction j) hd.1 (O.primitive j) hj with hp | hp
    · refine ⟨⟨j.val, by have := j.isLt; omega⟩, ?_⟩
      exact (pg_cycle_first O j.val j.isLt).trans hp
    · refine ⟨⟨m + j.val, by have := j.isLt; omega⟩, ?_⟩
      rw [pg_cycle_second O (m + j.val) (by omega) (by have := j.isLt; omega)]
      simpa only [Nat.add_sub_cancel_left, neg_neg] using congrArg Neg.neg hp
  · rintro ⟨i, rfl⟩
    have hp := (pg_all_edges (by omega) O hne (i.val : ℤ)).1
    apply (zonotope_exposed_face_direction_classification m hm h hne hpair _ hp).1.mpr
    by_cases hi : i.val < m
    · rw [pg_cycle_first O i.val hi]
      refine ⟨O.label ⟨i.val, hi⟩, ?_⟩
      rw [he]
      simp [det, mul_comm]
    · rw [pg_cycle_second O i.val (by omega) i.isLt]
      refine ⟨O.label ⟨i.val - m, by have := i.isLt; omega⟩, ?_⟩
      rw [he]
      simp only [det, Prod.fst_neg, Prod.snd_neg]
      ring

theorem antipodal_zonotope_actual_support_vertices (m : ℕ) (hm : 2 ≤ m)
    (h : Fin m → Lattice) (hne : ∀ i, h i ≠ 0)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j))) (O : LabelledFactorOrder m h) :
    (windowHull (supportWindow (differenceFactors m h)) =
      {x | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ (O.scale i : ℝ)) ∧
        x = embed (labelledHullAnchor O) + ∑ i, t i • embed (O.direction i)}) ∧
    ∃ C : AntipodalEdgeCycle (supportWindow (differenceFactors m h)) m,
      C.direction = labelledCycleDirection O ∧ C.vertex = labelledCycleVertex O := by
  have hm0 : 0 < m := by omega
  refine ⟨?_, ?_⟩
  · rw [(reflected_difference_product_actual_zonotope m h hne).2, pg_oriented_hull O]
  · refine ⟨{
      at_least_two := hm
      direction := labelledCycleDirection O
      vertex := labelledCycleVertex O
      direction_periodic := pg_cycle_periodic O
      vertex_periodic := pg_vertex_periodic O
      antipodal := pg_cycle_antipodal hm0 O
      primitive := fun j => (pg_all_edges hm0 O hne j).1
      distinct := pg_cycle_injective O
      covers := pg_direction_covers hm O hne hpair
      initial_mem := ?_
      terminal_mem := ?_
      edge_length := fun j => (pg_all_edges hm0 O hne j).2.1
      support_segment := ?_
    }, rfl, rfl⟩
    · intro j
      exact ((pg_all_edges hm0 O hne j).2.2 _).mpr (left_mem_segment ℝ _ _)
    · intro j
      exact ((pg_all_edges hm0 O hne j).2.2 _).mpr (right_mem_segment ℝ _ _)
    · intro j z
      constructor
      · intro hz
        exact ⟨(Finset.mem_filter.mp hz).1, ((pg_all_edges hm0 O hne j).2.2 z).mp hz⟩
      · rintro ⟨_, hz⟩
        exact ((pg_all_edges hm0 O hne j).2.2 z).mpr hz

end
end ConvexNivat.Colle
