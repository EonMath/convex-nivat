import ConvexNivat.Colle.GP.ProductHull
import ConvexNivat.Colle.Shared.RowCoordinates
import ConvexNivat.Colle.GP.Support

namespace ConvexNivat.Colle
open scoped BigOperators
noncomputable section

private theorem product_window_convex (m : ℕ) (h : Fin m → Lattice) :
    LatticeConvex (supportWindow (differenceFactors m h)) := by
  intro z
  rw [supportWindow, convexLatticeWindow_hull]
  exact (lattice_windowHull_finite _).mem_toFinset.symm

private theorem product_normal_ne (d : Lattice) (hd : Primitive d) : normal d ≠ 0 := by
  intro he
  apply primitive_ne_zero d hd
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  apply Prod.ext
  · simpa [normal] using h2
  · simpa [normal] using h1

private theorem support_real_face (S : Finset Lattice) (hc : LatticeConvex S)
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
      · intro a b
        simp [realDot]
        ring
      · intro a b
        simp [realDot]
        ring
  · rintro ⟨hz, hmin⟩
    exact Finset.mem_filter.mpr ⟨(hc z).mp hz,
      fun q hq => hmin _ ((hc q).mpr hq)⟩

private theorem product_face_parameters (m : ℕ) (h : Fin m → Lattice)
    (hne : ∀ i, h i ≠ 0) (n : RealPlane) (hn : n ≠ 0) (z : Lattice) :
    z ∈ supportFace (supportWindow (differenceFactors m h)) n ↔
      ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
        (∀ i, realDot (embed (-h i)) n < 0 → t i = 1) ∧
        (∀ i, 0 < realDot (embed (-h i)) n → t i = 0) ∧
        embed z = ∑ i, t i • embed (-h i) := by
  rw [support_real_face _ (product_window_convex m h),
    (reflected_difference_product_actual_zonotope m h hne).2]
  exact congrArg (fun P : Set RealPlane => embed z ∈ P)
    (zonotope_exposed_face_parameter_classification m h n hn) |> Iff.of_eq

private theorem product_edge_has_factor (m : ℕ) (h : Fin m → Lattice)
    (hne : ∀ i, h i ≠ 0) (d : Lattice)
    (hd : d ∈ edgeDirections (supportWindow (differenceFactors m h))) :
    ∃ i, det d (h i) = 0 := by
  classical
  by_contra! hnot
  have hs : (supportRow (supportWindow (differenceFactors m h)) d).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨t, ht, htn, htp, hte⟩ :=
      (product_face_parameters m h hne (normal d) (product_normal_ne d hd.1) p).mp hp
    obtain ⟨u, hu, hun, hup, hue⟩ :=
      (product_face_parameters m h hne (normal d) (product_normal_ne d hd.1) q).mp hq
    have htu : t = u := by
      funext i
      have hci : realDot (embed (-h i)) (normal d) ≠ 0 := by
        rw [normal_height]
        have he : det d (-h i) = -det d (h i) := by simp [det]; ring
        rw [he, Int.cast_neg]
        exact neg_ne_zero.mpr (by exact_mod_cast hnot i)
      rcases lt_or_gt_of_ne hci with hc | hc
      · rw [htn i hc, hun i hc]
      · rw [htp i hc, hup i hc]
    exact embed_injective (hte.trans (htu ▸ hue.symm))
  have := hd.2.2
  omega

private theorem product_factor_is_edge (m : ℕ) (hm : 2 ≤ m) (h : Fin m → Lattice)
    (hne : ∀ i, h i ≠ 0) (hpair : Pairwise (fun i j => Nonparallel (h i) (h j)))
    (d : Lattice) (hd : Primitive d) (i : Fin m) (hi : det d (h i) = 0) :
    d ∈ edgeDirections (supportWindow (differenceFactors m h)) := by
  classical
  let c : Fin m → ℝ := fun j => realDot (embed (-h j)) (normal d)
  let t : Fin m → ℝ := fun j => if c j < 0 then 1 else 0
  let a : Lattice := ∑ j, if c j < 0 then -h j else 0
  let b : Lattice := a - h i
  have hc : c i = 0 := by
    dsimp [c]
    rw [normal_height]
    have he : det d (-h i) = -det d (h i) := by simp [det]; ring
    rw [he, hi]
    norm_num
  have ht : ∀ j, 0 ≤ t j ∧ t j ≤ 1 := by
    intro j
    dsimp [t]
    split_ifs <;> norm_num
  have ht0 : t i = 0 := by simp [t, hc]
  have hea : embed a = ∑ j, t j • embed (-h j) := by
    ext <;> simp only [a, t, embed, Prod.fst_sum, Prod.snd_sum, Int.cast_sum,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    all_goals apply Finset.sum_congr rfl
    all_goals intro j hj
    all_goals split_ifs <;> simp
  have ha : a ∈ supportRow (supportWindow (differenceFactors m h)) d := by
    apply (product_face_parameters m h hne (normal d) (product_normal_ne d hd) a).mpr
    exact ⟨t, ht, fun j hj => by simp [t, c, hj],
      fun j hj => by simp [t, c, not_lt_of_ge hj.le], hea⟩
  have heb : embed b = ∑ j, (t j + (Pi.single i (1 : ℝ) : Fin m → ℝ) j) • embed (-h j) := by
    simp only [add_smul, Finset.sum_add_distrib, ← hea]
    simp only [Pi.single_apply, ite_smul, zero_smul, one_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ext <;> simp [b, embed, sub_eq_add_neg]
  have hb : b ∈ supportRow (supportWindow (differenceFactors m h)) d := by
    apply (product_face_parameters m h hne (normal d) (product_normal_ne d hd) b).mpr
    refine ⟨fun j => t j + (Pi.single i (1 : ℝ) : Fin m → ℝ) j, ?_, ?_, ?_, heb⟩
    · intro j
      by_cases hj : j = i
      · subst j; simp [ht0]
      · simpa [Pi.single_apply, hj] using ht j
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; change c i < 0 at hj; rw [hc] at hj; linarith
      simp [Pi.single_apply, hji, t, c, hj]
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; change 0 < c i at hj; rw [hc] at hj; linarith
      simp [Pi.single_apply, hji, t, c, not_lt_of_ge hj.le]
  refine ⟨hd, reflected_difference_product_interior m hm h hne hpair, ?_⟩
  have hlt : 1 < (supportRow (supportWindow (differenceFactors m h)) d).card :=
    Finset.one_lt_card.mpr ⟨a, ha, b, hb, ?_⟩
  · omega
  · intro he
    apply hne i
    have hz : a - h i = a := he.symm
    exact sub_eq_self.mp hz

theorem zonotope_exposed_face_direction_classification (m : ℕ) (hm : 2 ≤ m)
    (h : Fin m → Lattice) (hne : ∀ i, h i ≠ 0)
    (hpair : Pairwise (fun i j => Nonparallel (h i) (h j))) (d : Lattice)
    (hd : Primitive d) :
    (d ∈ edgeDirections (supportWindow (differenceFactors m h)) ↔ ∃ i, det d (h i) = 0) ∧
    ((∃ i, det d (h i) = 0) → ∃ a b : Lattice,
      BoundaryRun (supportWindow (differenceFactors m h)) d a b ∧
      (∀ z : Lattice, z ∈ supportRow (supportWindow (differenceFactors m h)) d ↔
        embed z ∈ segment ℝ (embed a) (embed b))) := by
  have he : d ∈ edgeDirections (supportWindow (differenceFactors m h)) ↔
      ∃ i, det d (h i) = 0 := ⟨product_edge_has_factor m h hne d,
        fun ⟨i, hi⟩ => product_factor_is_edge m hm h hne hpair d hd i hi⟩
  refine ⟨he, ?_⟩
  intro hi
  have hcard := (he.mpr hi).2.2
  have hnonempty : (supportWindow (differenceFactors m h)).Nonempty := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega :
      0 < (supportRow (supportWindow (differenceFactors m h)) d).card)
    exact ⟨a, (Finset.mem_filter.mp ha).1⟩
  obtain ⟨a, b, hrun, hb, _, _⟩ := minimum_support_row_generated_endpoints _ hnonempty
    (product_window_convex m h) d hd hcard
  refine ⟨a, b, hrun, ?_⟩
  intro z
  have hseg := (primitive_row_coordinates d hd).2.2 a 0
    (((supportRow (supportWindow (differenceFactors m h)) d).card - 1 : ℕ) : ℤ)
    (by positivity) z
  simp only [zero_smul, add_zero, ← hb] at hseg
  rw [hrun.1 z, hseg]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨(t : ℤ), by omega, by omega, hz⟩
  · rintro ⟨t, ht, htb, hz⟩
    exact ⟨t.toNat, by omega, by simpa [Int.toNat_of_nonneg ht] using hz⟩

end
end ConvexNivat.Colle
