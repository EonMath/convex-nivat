import ConvexNivat.SectorConnectivity

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

theorem applied_colour_difference_finite_support {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (ε : SectorSigns star)
    (hε : RealisedSector star ε) (a : ZMod p) :
    ScalarHasFiniteSupport
      (applyLaurent (exceptionalPolynomial star periods)
        (colorIndicator star.configuration a) - appliedSectorBackground star periods ε a) := by
  classical
  let A := exceptionalPolynomial star periods
  let M := A.coeff.support
  let c : Fin star.m → ℕ := fun i =>
    (star.component i).lower.natAbs + (star.component i).upper.natAbs + 1
  let R : Fin star.m → ℕ := fun i =>
    c i + M.sup (fun s => (height (star.component i).direction s).natAbs)
  have hR (i : Fin star.m) : 0 < R i := by
    dsimp [R, c]
    omega
  have hM (i : Fin star.m) (s : Lattice) (hs : s ∈ M) :
      -((M.sup (fun s => (height (star.component i).direction s).natAbs) : ℕ) : ℤ) ≤
          height (star.component i).direction s ∧
      height (star.component i).direction s ≤
        ((M.sup (fun s => (height (star.component i).direction s).natAbs) : ℕ) : ℤ) := by
    have h := Finset.le_sup (s := M)
      (f := fun s => (height (star.component i).direction s).natAbs) hs
    have hc : ((height (star.component i).direction s).natAbs : ℤ) ≤
        ((M.sup (fun s => (height (star.component i).direction s).natAbs) : ℕ) : ℤ) := by
      exact_mod_cast h
    have h₁ := Int.le_natAbs (a := height (star.component i).direction s)
    have h₂ := Int.le_natAbs (a := -height (star.component i).direction s)
    rw [Int.natAbs_neg] at h₂
    omega
  have hlocal (z : Lattice) (χ : Configuration (ZMod p))
      (hz : ∀ s ∈ M, star.configuration (z + s) = χ (z + s)) :
      applyLaurent A (colorIndicator star.configuration a) z =
        applyLaurent A (colorIndicator χ a) z := by
    unfold applyLaurent
    apply Finset.sum_congr rfl
    intro s hs
    simp only [colorIndicator, hz s hs]
  have hnone (z : Lattice)
      (hz : ∀ i, R i < (height (star.component i).direction z).natAbs) :
      applyLaurent A (colorIndicator star.configuration a) z =
        appliedSectorBackground star periods ε a z := by
    let δ : SectorSigns star := fun i =>
      if 0 < height (star.component i).direction z then .right else .left
    have hδ : RealisedSector star δ := by
      refine ⟨embed z, ?_⟩
      intro i
      have hn : height (star.component i).direction z ≠ 0 := by
        intro he
        have hi := hz i
        simp [he] at hi
      dsimp [δ]
      split_ifs with hp
      · change 0 < realHeight (star.component i).direction (embed z)
        have he : realHeight (star.component i).direction (embed z) =
            (height (star.component i).direction z : ℝ) := by
          simp [realHeight, height, embed, det]
        rw [he]
        exact_mod_cast hp
      · change realHeight (star.component i).direction (embed z) < 0
        have he : realHeight (star.component i).direction (embed z) =
            (height (star.component i).direction z : ℝ) := by
          simp [realHeight, height, embed, det]
        rw [he]
        exact_mod_cast lt_of_le_of_ne (le_of_not_gt hp) hn
    have hagree : ∀ s ∈ M,
        star.configuration (z + s) = sectorBackground star δ (z + s) := by
      intro s hs
      unfold StarData.configuration sectorBackground
      apply Finset.sum_congr rfl
      intro i _
      have hbound := hM i s hs
      have hlo := Int.le_natAbs (a := -(star.component i).lower)
      rw [Int.natAbs_neg] at hlo
      have hup := Int.le_natAbs (a := (star.component i).upper)
      have habs := hz i
      have hcast : (R i : ℤ) < ((height (star.component i).direction z).natAbs : ℤ) := by
        exact_mod_cast habs
      have hr : (R i : ℤ) =
          (star.component i).lower.natAbs + (star.component i).upper.natAbs + 1 +
            ((M.sup (fun s => (height (star.component i).direction s).natAbs) : ℕ) : ℤ) := by
        simp [R, c]
      dsimp [δ]
      split_ifs with hp
      · change (star.component i).field (z + s) = (star.component i).rightTail (z + s)
        apply (star.component i).right_agreement
        change (star.component i).upper < height (star.component i).direction (z + s)
        rw [height_add]
        rw [Int.natAbs_of_nonneg (le_of_lt hp)] at hcast
        omega
      · change (star.component i).field (z + s) = (star.component i).leftTail (z + s)
        apply (star.component i).left_agreement
        change height (star.component i).direction (z + s) < (star.component i).lower
        rw [height_add]
        have he : ((height (star.component i).direction z).natAbs : ℤ) =
            -height (star.component i).direction z := by
          rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hp)]
        rw [he] at hcast
        omega
    rw [hlocal z (sectorBackground star δ) hagree]
    exact congrFun (realised_sector_applied_backgrounds_equal star periods δ ε hδ hε a) z
  have hXi (i : Fin star.m) (σ : RayOrientation) :
      applyLaurent A (colorIndicator (isolatingConfiguration star i σ) a) =
        appliedSectorBackground star periods ε a := by
    obtain ⟨u, hu⟩ := primitive_height_surjective (star.component i).direction
      (star.component i).primitive 1
    let N : ℕ := Finset.univ.sup (fun j : Fin star.m =>
      (height (star.component j).direction u).natAbs) + 1
    let x : Lattice := (N : ℤ) • (σ.sign • (star.component i).direction) + u
    let δ : SectorSigns star := fun j => if j = i then .right else raySide star i j σ
    have hδ : RealisedSector star δ := by
      refine ⟨embed x, ?_⟩
      intro j
      have he : realHeight (star.component j).direction (embed x) =
          (height (star.component j).direction x : ℝ) := by
        simp [realHeight, height, embed, det]
      by_cases hji : j = i
      · subst j
        simp only [δ, ite_eq_left rfl]
        change 0 < realHeight (star.component i).direction (embed x)
        rw [he]
        have hx : height (star.component i).direction x = 1 := by
          simp only [x, height_add, height_zsmul, height_self, mul_zero, zero_add, hu]
        rw [hx]
        norm_num
      · have hn : (height (star.component j).direction u).natAbs < N := by
          exact lt_of_le_of_lt (Finset.le_sup (s := Finset.univ) (f := fun j =>
            (height (star.component j).direction u).natAbs) (Finset.mem_univ j))
            (Nat.lt_succ_self _)
        have hn' : ((height (star.component j).direction u).natAbs : ℤ) < N := by
          exact_mod_cast hn
        have ha := Int.le_natAbs (a := height (star.component j).direction u)
        have hb := Int.le_natAbs (a := -height (star.component j).direction u)
        rw [Int.natAbs_neg] at hb
        have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg N
        have hx : height (star.component j).direction x =
            (N : ℤ) * (σ.sign * det (star.component j).direction (star.component i).direction) +
              height (star.component j).direction u := by
          simp [x, height, det]
          ring
        have hdet : σ.sign * det (star.component j).direction (star.component i).direction ≠ 0 := by
          apply mul_ne_zero
          · cases σ <;> simp [RayOrientation.sign]
          · exact star.pairwise_nonparallel j i hji
        dsimp only [δ]
        rw [ite_eq_right hji]
        unfold raySide
        split_ifs with hp
        · change 0 < realHeight (star.component j).direction (embed x)
          rw [he]
          have hpos : 0 < height (star.component j).direction x := by
            rw [hx]
            have hm := mul_le_mul_of_nonneg_left (show 1 ≤
              σ.sign * det (star.component j).direction (star.component i).direction by omega) hN
            nlinarith
          exact_mod_cast hpos
        · change realHeight (star.component j).direction (embed x) < 0
          rw [he]
          have hneg : height (star.component j).direction x < 0 := by
            rw [hx]
            have hm := mul_le_mul_of_nonneg_left (show
              σ.sign * det (star.component j).direction (star.component i).direction ≤ -1 by omega) hN
            nlinarith
          exact_mod_cast hneg
    have hbg : sectorBackground star δ = pureRayBackground star i σ .right := by
      funext z
      change (∑ j : Fin star.m, componentTail star j (δ j) z) =
        componentTail star i .right z + ∑ j ∈ Finset.univ.erase i, rayTail star i j σ z
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [δ, ite_eq_left rfl]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.mem_erase.mp hj).1]
      simp only [raySide, rayTail]
      split_ifs <;> rfl
    have hzero (f : LaurentPolynomial) : applyLaurent f 0 = 0 := by
      funext z
      simp [applyLaurent]
    have hsub (f : LaurentPolynomial) (d e : ScalarField) :
        applyLaurent f (d - e) = applyLaurent f d - applyLaurent f e := by
      funext z
      simp [applyLaurent, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]
    have hk : applyLaurent A (exceptionalDifference star i σ .right a) = 0 := by
      obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem
        (fun j => exceptionalDirectionPolynomial star periods j) (Finset.mem_univ i)
      change applyLaurent (∏ j, exceptionalDirectionPolynomial star periods j) _ = 0
      rw [hq, mul_comm, applyLaurent_mul,
        exceptional_direction_annihilates star periods i σ .right a, hzero]
    rw [exceptionalDifference, hsub, sub_eq_zero] at hk
    have heq := realised_sector_applied_backgrounds_equal star periods δ ε hδ hε a
    rw [hbg] at heq
    exact hk.trans heq
  let u : Fin star.m → Lattice := fun i => Classical.choose
    (primitive_height_surjective (star.component i).direction (star.component i).primitive 1)
  have hu (i : Fin star.m) : height (star.component i).direction (u i) = 1 :=
    Classical.choose_spec
      (primitive_height_surjective (star.component i).direction (star.component i).primitive 1)
  let t : Fin star.m → Lattice → ℤ := fun i z => det z (u i)
  have hcoord (i : Fin star.m) (z : Lattice) :
      z = t i z • (star.component i).direction +
        height (star.component i).direction z • u i := by
    have hb := hu i
    dsimp [height, det] at hb
    apply Prod.ext
    · change z.1 =
        (z.1 * (u i).2 - z.2 * (u i).1) * (star.component i).direction.1 +
          ((star.component i).direction.1 * z.2 - (star.component i).direction.2 * z.1) * (u i).1
      linear_combination -z.1 * hb
    · change z.2 =
        (z.1 * (u i).2 - z.2 * (u i).1) * (star.component i).direction.2 +
          ((star.component i).direction.1 * z.2 - (star.component i).direction.2 * z.1) * (u i).2
      linear_combination -z.2 * hb
  let reps (i : Fin star.m) : Finset Lattice :=
    ((Finset.Icc (0 : ℤ) (periods.multiplier i - 1)).product
      (Finset.Icc (-(R i : ℤ)) (R i))).image
      (fun q => q.1 • (star.component i).direction + q.2 • u i)
  let W (i : Fin star.m) := reps i + M
  let N (i : Fin star.m) (σ : RayOrientation) : ℕ := Classical.choose
    (isolating_configuration_finite_stabilisation star periods i σ (W i))
  have hN (i : Fin star.m) (σ : RayOrientation) := Classical.choose_spec
    (isolating_configuration_finite_stabilisation star periods i σ (W i))
  let K (i : Fin star.m) : ℕ := N i .positive + N i .negative + 1
  have hNK (i : Fin star.m) (σ : RayOrientation) : N i σ ≤ K i := by
    cases σ <;> dsimp [K] <;> omega
  have hfar (i : Fin star.m) (r q : ℤ)
      (hr : 0 ≤ r ∧ r < (periods.multiplier i : ℤ))
      (hq : -(R i : ℤ) ≤ q ∧ q ≤ R i)
      (σ : RayOrientation) (n : ℕ) (hn : K i ≤ n) :
      applyLaurent A (colorIndicator star.configuration a)
        ((r • (star.component i).direction + q • u i) +
          ((n : ℤ) * σ.sign) • periods.vector i) =
      appliedSectorBackground star periods ε a
        ((r • (star.component i).direction + q • u i) +
          ((n : ℤ) * σ.sign) • periods.vector i) := by
    let x := r • (star.component i).direction + q • u i
    let h := ((n : ℤ) * σ.sign) • periods.vector i
    have hx : x ∈ reps i := by
      dsimp only [reps]
      apply Finset.mem_image.mpr
      refine ⟨(r, q), ?_, rfl⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hr.1, by omega⟩, Finset.mem_Icc.mpr hq⟩
    have hagree : ∀ s ∈ M,
        star.configuration ((x + h) + s) = isolatingConfiguration star i σ ((x + h) + s) := by
      intro s hs
      have hxs : x + s ∈ W i := Finset.add_mem_add hx hs
      have hz := hN i σ n ((hNK i σ).trans hn) (x + s) hxs
      have hp := hasPeriod_zsmul _ _
        (isolating_configuration_period star periods i σ) ((n : ℤ) * σ.sign) (x + s)
      dsimp only [h]
      simpa only [add_right_comm x _ s] using hz.trans hp.symm
    exact (hlocal (x + h) _ hagree).trans (congrFun (hXi i σ) (x + h))
  let B (i : Fin star.m) : ℤ := (K i : ℤ) * periods.multiplier i + periods.multiplier i
  let box (i : Fin star.m) : Set Lattice :=
    {z | (-(R i : ℤ) ≤ height (star.component i).direction z ∧
        height (star.component i).direction z ≤ R i) ∧
      (-B i ≤ t i z ∧ t i z ≤ B i)}
  have hbox (i : Fin star.m) : (box i).Finite := by
    apply Set.Finite.of_injOn (f := fun z : Lattice =>
      (height (star.component i).direction z, t i z))
      (t := Set.Icc (-(R i : ℤ)) (R i) ×ˢ Set.Icc (-B i) (B i))
    · intro z hz
      exact hz
    · intro z _ y _ hzy
      have h₁ := congrArg Prod.fst hzy
      have h₂ := congrArg Prod.snd hzy
      rw [hcoord i z, hcoord i y]
      exact congrArg₂ (fun r q => r • (star.component i).direction + q • u i) h₂ h₁
    · exact (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  apply (Set.finite_iUnion hbox).subset
  intro z hz
  have hzne : applyLaurent A (colorIndicator star.configuration a) z ≠
      appliedSectorBackground star periods ε a z := by
    simpa only [Function.mem_support, Pi.sub_apply, sub_ne_zero] using hz
  by_cases ha : ∃ i : Fin star.m, (height (star.component i).direction z).natAbs ≤ R i
  · obtain ⟨i, hi⟩ := ha
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hq : -(R i : ℤ) ≤ height (star.component i).direction z ∧
        height (star.component i).direction z ≤ R i := by
      have hi' : ((height (star.component i).direction z).natAbs : ℤ) ≤ R i := by
        exact_mod_cast hi
      have h₁ := Int.le_natAbs (a := height (star.component i).direction z)
      have h₂ := Int.le_natAbs (a := -height (star.component i).direction z)
      rw [Int.natAbs_neg] at h₂
      omega
    let κ : ℤ := periods.multiplier i
    let d := t i z / κ
    let r := t i z % κ
    have hκ : 0 < κ := by
      change (0 : ℤ) < (periods.multiplier i : ℤ)
      exact_mod_cast periods.positive i
    have hr : 0 ≤ r ∧ r < κ :=
      ⟨Int.emod_nonneg _ (ne_of_gt hκ), Int.emod_lt_of_pos _ hκ⟩
    have ht : d * κ + r = t i z := Int.ediv_mul_add_emod _ _
    have hKpos : (0 : ℤ) ≤ K i := Int.natCast_nonneg _
    have hshiftcoord : (r • (star.component i).direction +
        height (star.component i).direction z • u i) +
          (d * κ) • (star.component i).direction = z := by
      calc
        _ = (d * κ + r) • (star.component i).direction +
            height (star.component i).direction z • u i := by module
        _ = z := by rw [ht]; exact (hcoord i z).symm
    have hd : -(K i : ℤ) < d ∧ d < K i := by
      constructor
      · by_contra hbad
        have hh : 0 ≤ -d := by omega
        let n := (-d).toNat
        have hn' : (n : ℤ) = -d := Int.toNat_of_nonneg hh
        have hn : K i ≤ n := by exact_mod_cast (show (K i : ℤ) ≤ (n : ℤ) by omega)
        have hshift : (r • (star.component i).direction +
            height (star.component i).direction z • u i) +
              ((n : ℤ) * RayOrientation.negative.sign) • periods.vector i = z := by
          simp only [RayOrientation.sign, StarCommonPeriods.vector, hn']
          rw [smul_smul]
          have he : (-d * -1) * κ = d * κ := by ring
          change _ + ((-d * -1) * κ) • (star.component i).direction = _
          rw [he]
          exact hshiftcoord
        have heq := hfar i r _ hr hq .negative n hn
        rw [hshift] at heq
        exact hzne heq
      · by_contra hbad
        have hh : 0 ≤ d := by omega
        let n := d.toNat
        have hn' : (n : ℤ) = d := Int.toNat_of_nonneg hh
        have hn : K i ≤ n := by exact_mod_cast (show (K i : ℤ) ≤ (n : ℤ) by omega)
        have hshift : (r • (star.component i).direction +
            height (star.component i).direction z • u i) +
              ((n : ℤ) * RayOrientation.positive.sign) • periods.vector i = z := by
          simp only [RayOrientation.sign, StarCommonPeriods.vector, hn', mul_one, smul_smul]
          change _ + (d * κ) • (star.component i).direction = _
          exact hshiftcoord
        have heq := hfar i r _ hr hq .positive n hn
        rw [hshift] at heq
        exact hzne heq
    refine ⟨hq, ?_⟩
    change -((K i : ℤ) * κ + κ) ≤ t i z ∧ t i z ≤ (K i : ℤ) * κ + κ
    have hlo := mul_le_mul_of_nonneg_right (le_of_lt hd.1) (le_of_lt hκ)
    have hup := mul_le_mul_of_nonneg_right (le_of_lt hd.2) (le_of_lt hκ)
    constructor <;> nlinarith
  · exact False.elim (hzne (hnone z (fun i => lt_of_not_ge (fun h => ha ⟨i, h⟩))))

end
end ConvexNivat
