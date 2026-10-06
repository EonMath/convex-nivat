import NivatTrial.ColleOppositeDirections
import NivatTrial.RealHalfPlaneRecurrence
import NivatTrial.ExternalInputs
import NivatTrial.ColleDirectionalPropagation
import NivatTrial.HorizontalCoordinates

/-! A nonexpansive real direction in a configuration with an actual integer
periodic decomposition must be parallel to one of its lattice period vectors.
Both orientations are retained when the real scale is negative. -/

namespace NivatTrial.ColleRationalDirections

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.OneSidedRecurrence
open NivatTrial.IncrementSupport NivatTrial.RealHalfPlaneRecurrence
open NivatTrial.ExternalInputs NivatTrial.Dynamics
open NivatTrial.ColleDirectionalPropagation NivatTrial.HorizontalCoordinates
open scoped Classical
noncomputable section

abbrev Plane := ℝ × ℝ

theorem tangent_factor_of_nonexpansive {M n : ℕ}
    (θ : Lattice → Fin M) (E : IntegerDecomposition (integerField θ) n)
    (v : Plane) (hnear : OneSidedNonexpansive θ v) :
    ∃ i : Fin n, score v (E.period i) = 0 := by
  have hann : iteratedIncrement (Finset.univ.toList.map E.period)
      (integerField θ) = 0 := by
    have he := congrArg (iteratedIncrement (Finset.univ.toList.map E.period)) E.sum_eq
    exact he.symm.trans
      (decomposition_annihilator E.component E.period E.component_period)
  by_contra hnone
  have htrans : ∀ h ∈ Finset.univ.toList.map E.period, score v h ≠ 0 := by
    intro h hh hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hh
    exact hnone ⟨i,hz⟩
  exact (oneSidedExpansive_of_transverse_product θ integerCode
    (integerCode_injective M) _ v htrans hann) hnear

theorem exists_nonzero_real_scale (v : Plane) (u : Lattice)
    (hv : v ≠ 0) (hu : u ≠ 0) (hscore : score v u = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ v = c • embed u := by
  by_cases hux : u.1 = 0
  · have huy : u.2 ≠ 0 := by
      intro hy
      exact hu (Prod.ext hux hy)
    have huyR : (u.2 : ℝ) ≠ 0 := by exact_mod_cast huy
    have hvx : v.1 = 0 := by
      have hs := hscore
      simp only [score, hux, Int.cast_zero, mul_zero, sub_zero] at hs
      exact (mul_eq_zero.mp hs).resolve_right huyR
    have hvy : v.2 ≠ 0 := by
      intro hy
      exact hv (Prod.ext hvx hy)
    let c : ℝ := v.2 / (u.2 : ℝ)
    refine ⟨c, div_ne_zero hvy huyR, ?_⟩
    apply Prod.ext
    · simp [c, embed, hux, hvx, smul_eq_mul]
    · change v.2 = c * (u.2 : ℝ)
      simp [c, huyR]
  · have huxR : (u.1 : ℝ) ≠ 0 := by exact_mod_cast hux
    have hvx : v.1 ≠ 0 := by
      intro hx
      have hvy : v.2 = 0 := by
        have hs := hscore
        dsimp [score] at hs
        rw [hx] at hs
        have hprod : v.2 * (u.1 : ℝ) = 0 := by nlinarith [hs]
        exact (mul_eq_zero.mp hprod).resolve_right huxR
      exact hv (Prod.ext hx hvy)
    let c : ℝ := v.1 / (u.1 : ℝ)
    refine ⟨c, div_ne_zero hvx huxR, ?_⟩
    apply Prod.ext
    · change v.1 = c * (u.1 : ℝ)
      simp [c, huxR]
    · change v.2 = c * (u.2 : ℝ)
      apply (mul_left_cancel₀ huxR)
      calc
        (u.1 : ℝ) * v.2 = v.1 * (u.2 : ℝ) := by
          dsimp [score] at hscore
          nlinarith
        _ = (u.1 : ℝ) * (c * (u.2 : ℝ)) := by
          dsimp [c]
          field_simp

theorem score_real_smul (c : ℝ) (v : Plane) (z : Lattice) :
    score (c • v) z = c * score v z := by
  simp [score,smul_eq_mul]
  ring

theorem halfPlane_pos_smul (c : ℝ) (hc : 0 < c) (v : Plane) :
    halfPlane (c • v) 0 = halfPlane v 0 := by
  ext z
  change 0 ≤ score (c • v) z ↔ 0 ≤ score v z
  rw [score_real_smul]
  constructor
  · intro h
    by_contra hn
    have hneg : score v z < 0 := lt_of_not_ge hn
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hc hneg)) h
  · intro h
    exact mul_nonneg hc.le h

theorem nonexpansive_pos_smul {A : Type*} (θ : Lattice → A)
    (c : ℝ) (hc : 0 < c) (v : Plane) :
    OneSidedNonexpansive θ (c • v) ↔ OneSidedNonexpansive θ v := by
  simp only [OneSidedNonexpansive, halfPlane_pos_smul c hc v]

/-- The real direction and its opposite are both replaced by the actual
period vector and its opposite, without silently reversing the half-plane. -/
theorem opposite_nonexpansive_of_scale {A : Type*}
    (θ : Lattice → A) (v : Plane) (u : Lattice)
    (c : ℝ) (hc : c ≠ 0) (heq : v = c • embed u)
    (hpos : OneSidedNonexpansive θ v)
    (hneg : OneSidedNonexpansive θ (-v)) :
    OneSidedNonexpansive θ (embed u) ∧
      OneSidedNonexpansive θ (-(embed u)) := by
  rcases lt_or_gt_of_ne hc with hcn | hcp
  · have hcpos : 0 < -c := neg_pos.mpr hcn
    have heqpos : v = (-c) • (-(embed u)) := by
      rw [neg_smul,smul_neg,neg_neg]
      exact heq
    have heqneg : -v = (-c) • embed u := by
      rw [heq,neg_smul]
    constructor
    · rw [heqneg] at hneg
      exact (nonexpansive_pos_smul θ (-c) hcpos (embed u)).mp hneg
    · rw [heqpos] at hpos
      exact (nonexpansive_pos_smul θ (-c) hcpos (-(embed u))).mp hpos
  · constructor
    · rw [heq] at hpos
      exact (nonexpansive_pos_smul θ c hcp (embed u)).mp hpos
    · have heqneg : -v = c • (-(embed u)) := by rw [heq,smul_neg]
      rw [heqneg] at hneg
      exact (nonexpansive_pos_smul θ c hcp (-(embed u))).mp hneg

theorem opposite_nonexpansive_component_direction {M n : ℕ}
    (θ : Lattice → Fin M) (E : IntegerDecomposition (integerField θ) n)
    (v : Plane) (hv : v ≠ 0)
    (hpos : OneSidedNonexpansive θ v)
    (hneg : OneSidedNonexpansive θ (-v)) :
    ∃ i : Fin n, OneSidedNonexpansive θ (embed (E.period i)) ∧
      OneSidedNonexpansive θ (-(embed (E.period i))) := by
  obtain ⟨i,hi⟩ := tangent_factor_of_nonexpansive θ E v hpos
  obtain ⟨c,hc,heq⟩ := exists_nonzero_real_scale v (E.period i)
    hv (E.period_ne_zero i) hi
  exact ⟨i,opposite_nonexpansive_of_scale θ v (E.period i) c hc heq hpos hneg⟩

theorem nonexpansive_comp_equiv {A : Type*} (e : Lattice ≃+ Lattice)
    (θ : Lattice → A) (v : Plane)
    (h : OneSidedNonexpansive θ v) :
    OneSidedNonexpansive (θ ∘ e) (dualNormal e v) := by
  obtain ⟨x,hx,y,hy,hne,hagree⟩ := h
  refine ⟨x ∘ e, mem_languageHull_comp_equiv e hx,
    y ∘ e, mem_languageHull_comp_equiv e hy, ?_, ?_⟩
  · intro heq
    apply hne
    funext z
    have hz := congrFun heq (e.symm z)
    simpa using hz
  · intro z hz
    apply hagree (e z)
    change 0 ≤ score v (e z)
    rw [score_mapWindow]
    exact hz

theorem dualNormal_neg (e : Lattice ≃+ Lattice) (v : Plane) :
    dualNormal e (-v) = -(dualNormal e v) := by
  apply Prod.ext <;> simp [dualNormal, score_neg_direction]

theorem dualNormal_ne_zero (e : Lattice ≃+ Lattice)
    (u : Lattice) (hu : u ≠ 0) : dualNormal e (embed u) ≠ 0 := by
  obtain ⟨k,huk⟩ := PeriodicDifference.exists_transverse u hu
  intro hzero
  have hs : score (embed u) k = 0 := by
    have h := score_mapWindow e (embed u) (e.symm k)
    rw [e.apply_symm_apply, hzero] at h
    simpa [score] using h
  have hs' : (det u k : ℝ) = 0 := by
    simpa [score,embed,det] using hs
  exact huk (by exact_mod_cast hs')

theorem dualNormal_tangent_horizontal (e : Lattice ≃+ Lattice)
    (u : Lattice) (c : ℕ) (hc : 0 < c)
    (he : e (c • RowDetermination.horizontal) = u) :
    score (dualNormal e (embed u)) RowDetermination.horizontal = 0 := by
  have hs : score (embed u) u = 0 := by
    dsimp [score,embed]
    ring
  have hs' : (c : ℝ) * score (dualNormal e (embed u))
      RowDetermination.horizontal = 0 := by
    calc
      _ = score (dualNormal e (embed u)) (c • RowDetermination.horizontal) :=
        (score_nsmul _ _ _).symm
      _ = score (embed u) (e (c • RowDetermination.horizontal)) :=
        (score_mapWindow e (embed u) _).symm
      _ = score (embed u) u := by rw [he]
      _ = 0 := hs
  have hcnz : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  exact (mul_eq_zero.mp hs').resolve_left hcnz

/-- An actual integral change of basis sends the selected opposite
nonexpansive directions to the two horizontal orientations. -/
theorem exists_horizontal_opposite_nonexpansive {M n : ℕ}
    (hn : 2 ≤ n) (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) n)
    (v : Plane) (hv : v ≠ 0)
    (hpos : OneSidedNonexpansive θ v)
    (hneg : OneSidedNonexpansive θ (-v)) :
    ∃ i j : Fin n, ∃ c : ℕ, ∃ e : Lattice ≃+ Lattice,
      i ≠ j ∧ 0 < c ∧
      e (c • RowDetermination.horizontal) = E.period i ∧
      (e.symm (E.period j)).2 ≠ 0 ∧
      OneSidedNonexpansive (θ ∘ e) (1, 0) ∧
      OneSidedNonexpansive (θ ∘ e) (-(1, 0)) := by
  obtain ⟨i, hpi, hni⟩ :=
    opposite_nonexpansive_component_direction θ E v hv hpos hneg
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  have hij : i ≠ j := hji.symm
  obtain ⟨c,e,hc,he,ht⟩ :=
    exists_horizontal_coordinates (E.period i) (E.period j) (E.independent i j hij)
  let d := dualNormal e (embed (E.period i))
  have hdp : OneSidedNonexpansive (θ ∘ e) d :=
    nonexpansive_comp_equiv e θ (embed (E.period i)) hpi
  have hdn : OneSidedNonexpansive (θ ∘ e) (-d) := by
    simpa only [d, dualNormal_neg] using
      nonexpansive_comp_equiv e θ (-(embed (E.period i))) hni
  have hdne : d ≠ 0 := dualNormal_ne_zero e (E.period i) (E.period_ne_zero i)
  have hdscore : score d RowDetermination.horizontal = 0 :=
    dualNormal_tangent_horizontal e (E.period i) c hc he
  obtain ⟨r,hr,hdr⟩ := exists_nonzero_real_scale d RowDetermination.horizontal
    hdne (by simp [RowDetermination.horizontal]) hdscore
  obtain ⟨horizP,horizN⟩ := opposite_nonexpansive_of_scale
    (θ ∘ e) d RowDetermination.horizontal r hr hdr hdp hdn
  refine ⟨i,j,c,e,hij,hc,he,ht,?_,?_⟩
  · simpa [RowDetermination.horizontal, embed] using horizP
  · simpa [RowDetermination.horizontal, embed] using horizN

end
end NivatTrial.ColleRationalDirections
