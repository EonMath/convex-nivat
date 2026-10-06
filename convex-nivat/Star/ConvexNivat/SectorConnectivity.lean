import ConvexNivat.SectorRayEquality

open scoped BigOperators Topology
namespace ConvexNivat
noncomputable section

theorem realised_sector_applied_backgrounds_equal {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (ε ε' : SectorSigns star)
    (hε : RealisedSector star ε) (hε' : RealisedSector star ε') (a : ZMod p) :
    applyLaurent (exceptionalPolynomial star periods)
      (colorIndicator (sectorBackground star ε) a) =
    applyLaurent (exceptionalPolynomial star periods)
      (colorIndicator (sectorBackground star ε') a) := by
  classical
  let X := {x : RealPlane // x ≠ 0}
  have hconn : IsConnected {x : RealPlane | x ≠ 0} := by
    have hs : ({0}ᶜ : Set RealPlane) = {x : RealPlane | x ≠ 0} := by
      ext x
      simp
    rw [← hs]
    exact isConnected_compl_singleton_of_one_lt_rank
      (E := RealPlane) (by rw [← Module.finrank_eq_rank]; norm_num [Module.finrank_prod]) (0 : RealPlane)
  let : PreconnectedSpace X := Subtype.preconnectedSpace hconn.isPreconnected
  let δ : RealPlane → SectorSigns star := fun x i =>
    if 0 < realHeight (star.component i).direction x then .right else .left
  let F : X → ScalarField := fun x =>
    applyLaurent (exceptionalPolynomial star periods)
      (colorIndicator (sectorBackground star (δ x.val)) a)
  have hbg (i : Fin star.m) (σ : RayOrientation) (η : SectorSigns star)
      (hη : ∀ j, j ≠ i → η j = raySide star i j σ) :
      sectorBackground star η = pureRayBackground star i σ (η i) := by
    funext z
    change (∑ j : Fin star.m, componentTail star j (η j) z) =
      componentTail star i (η i) z + ∑ j ∈ Finset.univ.erase i, rayTail star i j σ z
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hη j (Finset.mem_erase.mp hj).1]
    simp only [raySide, rayTail]
    split_ifs <;> rfl
  have hother (x : X) (i j : Fin star.m) (hji : j ≠ i)
      (hi : realHeight (star.component i).direction x.val = 0) :
      realHeight (star.component j).direction x.val ≠ 0 := by
    intro hj
    have hd : (det (star.component i).direction (star.component j).direction : ℝ) ≠ 0 := by
      exact_mod_cast star.pairwise_nonparallel i j hji.symm
    have h₁ : (det (star.component i).direction (star.component j).direction : ℝ) * x.val.1 = 0 := by
      dsimp [realHeight] at hi hj
      simp only [det, Int.cast_sub, Int.cast_mul]
      linear_combination (star.component j).direction.1 * hi - (star.component i).direction.1 * hj
    have h₂ : (det (star.component i).direction (star.component j).direction : ℝ) * x.val.2 = 0 := by
      dsimp [realHeight] at hi hj
      simp only [det, Int.cast_sub, Int.cast_mul]
      linear_combination (star.component j).direction.2 * hi - (star.component i).direction.2 * hj
    apply x.property
    exact Prod.ext ((mul_eq_zero.mp h₁).resolve_left hd) ((mul_eq_zero.mp h₂).resolve_left hd)
  have hray (x : X) (i : Fin star.m)
      (hi : realHeight (star.component i).direction x.val = 0) :
      ∃ σ : RayOrientation, ∀ j, j ≠ i → δ x.val j = raySide star i j σ := by
    obtain ⟨u, hu⟩ := primitive_height_surjective (star.component i).direction
      (star.component i).primitive 1
    have hb : (star.component i).direction.1 * (u.2 : ℝ) -
        (star.component i).direction.2 * (u.1 : ℝ) = 1 := by
      exact_mod_cast hu
    let c : ℝ := -realHeight u x.val
    have hx : x.val = c • embed (star.component i).direction := by
      dsimp [realHeight] at hi
      apply Prod.ext
      · change x.val.1 = c * (star.component i).direction.1
        dsimp [c, realHeight]
        linear_combination -x.val.1 * hb + (u.1 : ℝ) * hi
      · change x.val.2 = c * (star.component i).direction.2
        dsimp [c, realHeight]
        linear_combination -x.val.2 * hb + (u.2 : ℝ) * hi
    have hc : c ≠ 0 := by
      intro hc
      apply x.property
      simpa only [hc, zero_smul] using hx
    have he (j : Fin star.m) : realHeight (star.component j).direction x.val =
        c * (det (star.component j).direction (star.component i).direction : ℝ) := by
      rw [hx]
      simp [realHeight, embed, det]
      ring
    by_cases hp : 0 < c
    · refine ⟨.positive, ?_⟩
      intro j _
      dsimp only [δ, raySide, RayOrientation.sign]
      simp only [one_mul, he, mul_pos_iff_of_pos_left hp]
      have hh : (0 : ℝ) < (det (star.component j).direction (star.component i).direction : ℝ) ↔
          (0 : ℤ) < det (star.component j).direction (star.component i).direction := by
        exact_mod_cast Iff.rfl
      simp only [hh]
    · refine ⟨.negative, ?_⟩
      intro j hji
      have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hc
      dsimp only [δ, raySide, RayOrientation.sign]
      simp only [he, neg_one_mul]
      have hh : 0 < c * (det (star.component j).direction (star.component i).direction : ℝ) ↔
          0 < -det (star.component j).direction (star.component i).direction := by
        have hprod : 0 < c * (det (star.component j).direction (star.component i).direction : ℝ) ↔
            (det (star.component j).direction (star.component i).direction : ℝ) < 0 := by
          constructor
          · intro hm
            by_contra hn
            have hle : 0 ≤ (det (star.component j).direction (star.component i).direction : ℝ) :=
              le_of_not_gt hn
            nlinarith
          · exact fun hm => mul_pos_of_neg_of_neg hcneg hm
        rw [hprod]
        have hcst : (det (star.component j).direction (star.component i).direction : ℝ) < 0 ↔
            det (star.component j).direction (star.component i).direction < 0 := by
          exact_mod_cast Iff.rfl
        rw [hcst]
        omega
      simp only [hh]
  have hsign (x : X) (i : Fin star.m)
      (hi : realHeight (star.component i).direction x.val ≠ 0) :
      ∀ᶠ y in 𝓝 x, δ y.val i = δ x.val i := by
    have hc : Continuous (fun y : X => realHeight (star.component i).direction y.val) := by
      unfold realHeight
      fun_prop
    by_cases hp : 0 < realHeight (star.component i).direction x.val
    · have ho : IsOpen {y : X | 0 < realHeight (star.component i).direction y.val} :=
        isOpen_lt continuous_const hc
      filter_upwards [ho.mem_nhds hp] with y hy
      simp [δ, hp, hy]
    · have hn : realHeight (star.component i).direction x.val < 0 :=
        lt_of_le_of_ne (le_of_not_gt hp) hi
      have ho : IsOpen {y : X | realHeight (star.component i).direction y.val < 0} :=
        isOpen_lt hc continuous_const
      filter_upwards [ho.mem_nhds hn] with y hy
      simp only [δ, ite_eq_right hp, ite_eq_right (not_lt.mpr hy.le)]
  have hF : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_eventually_eq F).mpr
    intro x
    have hev : ∀ᶠ y in 𝓝 x, ∀ i : Fin star.m,
        realHeight (star.component i).direction x.val ≠ 0 → δ y.val i = δ x.val i := by
      rw [Filter.eventually_all]
      intro i
      by_cases hi : realHeight (star.component i).direction x.val ≠ 0
      · exact (hsign x i hi).mono (fun y hy _ => hy)
      · exact Filter.Eventually.of_forall (fun _ hh => False.elim (hi hh))
    filter_upwards [hev] with y hy
    by_cases hb : ∃ i, realHeight (star.component i).direction x.val = 0
    · obtain ⟨i, hi⟩ := hb
      obtain ⟨σ, hσ⟩ := hray x i hi
      have hyr : ∀ j, j ≠ i → δ y.val j = raySide star i j σ := by
        intro j hji
        exact (hy j (hother x i j hji hi)).trans (hσ j hji)
      dsimp only [F]
      rw [hbg i σ (δ y.val) hyr, hbg i σ (δ x.val) hσ]
      have hr := exceptional_polynomial_ray_backgrounds_equal star periods i σ a
      cases hyi : δ y.val i <;> cases hxi : δ x.val i
      · rfl
      · exact hr.symm
      · exact hr
      · rfl
    · have heq : δ y.val = δ x.val := by
        funext i
        exact hy i (fun hh => hb ⟨i, hh⟩)
      dsimp only [F]
      rw [heq]
  have hcone (η : SectorSigns star) (x : RealPlane) (hx : x ∈ sectorCone star η) :
      x ≠ 0 ∧ δ x = η := by
    constructor
    · intro hz
      let i : Fin star.m := ⟨0, by have := star.two_le; omega⟩
      have hi := hx i
      rw [hz] at hi
      cases he : η i <;> simp [realHeight, he] at hi
    · funext i
      have hi := hx i
      cases he : η i
      · simp only [he] at hi
        exact ite_eq_right (not_lt.mpr (le_of_lt hi))
      · simp only [he] at hi
        exact ite_eq_left hi
  obtain ⟨x, hx⟩ := hε
  obtain ⟨y, hy⟩ := hε'
  have hc₁ := hcone ε x hx
  have hc₂ := hcone ε' y hy
  have hf := hF.apply_eq_of_preconnectedSpace (⟨x, hc₁.1⟩ : X) (⟨y, hc₂.1⟩ : X)
  simpa only [F, hc₁.2, hc₂.2] using hf

end
end ConvexNivat
