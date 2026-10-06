import NivatTrial.RealDirectionGeometry
import NivatTrial.ColleRegions

/-! A self-contained additive version of Colle's Proposition 2.12. A sum of
periodic components that is periodic along a rational boundary on one side
acquires a (possibly larger) global period in the same direction. -/

namespace NivatTrial.ColleHalfPlanePeriod

open NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.RealHalfPlaneRecurrence
open NivatTrial.RealDirectionGeometry
open NivatTrial.Nonexpansive NivatTrial.Zonotope NivatTrial.Geometry
open NivatTrial.ColleRegions
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

theorem score_embed_self (u : G) : score (embed u) u = 0 := by
  simp [score, embed]
  ring

theorem det_eq_zero_of_score_embed_zero (u h : G)
    (hs : score (embed u) h = 0) : det h u = 0 := by
  have heq : ((det h u : ℤ) : ℝ) = -score (embed u) h := by
    simp [det, score, embed]
    ring
  rw [hs] at heq
  exact_mod_cast heq

variable {ι B : Type*} [Fintype ι] [AddCommGroup B]

/-- The actual half-plane period extends globally for any finite additive
periodic decomposition. Pairwise independence is unnecessary for this step. -/
theorem halfPlane_period_extends_of_tangent
    (F : ι → G → B) (h : ι → G) (hper : ∀ i, IsPeriod (F i) (h i))
    (hzero : ∀ i, h i ≠ 0)
    (v : Plane) (hv : v ≠ 0) (u : G) (hu : score v u = 0) (b : ℝ)
    (hregional : ∀ z, b ≤ score v z →
      (∑ i, F i) (z+u) = (∑ i, F i) z) :
    ∃ Q : ℕ, 0 < Q ∧ IsPeriod (∑ i, F i) (Q • u) := by
  let P : ι → G → B := fun i =>
    if score v (h i) = 0 then F i else 0
  let T : ι → G → B := fun i =>
    if score v (h i) = 0 then 0 else F i
  have hsplit : (∑ i, F i) = (∑ i, P i) + (∑ i, T i) := by
    funext z
    simp only [Pi.add_apply, Finset.sum_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [P, T]
    split_ifs <;> simp
  have hchosen (i : ι) :
      ∃ q : ℕ, 0 < q ∧ IsPeriod (P i) (q • u) := by
    by_cases hi : score v (h i) = 0
    · obtain ⟨q,hq,hpq⟩ := parallel_direction_period (hper i) (hzero i) u
        (det_eq_zero_of_scores_zero v hv (h i) u hi hu)
      exact ⟨q,hq,by simpa [P,hi] using hpq⟩
    · exact ⟨1,by omega,by simp [P,hi,IsPeriod]⟩
  let q (i : ι) : ℕ := Classical.choose (hchosen i)
  have hq (i : ι) : 0 < q i ∧ IsPeriod (P i) (q i • u) :=
    Classical.choose_spec (hchosen i)
  let Q := ∏ i, q i
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => (hq i).1)
  have hp : IsPeriod (∑ i, P i) (Q • u) := by
    apply IsPeriod.sum_config Finset.univ P
    intro i _
    have hdiv : q i ∣ Q := Finset.dvd_prod_of_mem q (Finset.mem_univ i)
    obtain ⟨k,hk⟩ := hdiv
    rw [hk]
    simpa only [mul_comm (q i) k, mul_smul] using (hq i).2.nsmul k
  have hregion : PeriodicOn (∑ i, F i) (halfPlane v b) u := by
    constructor
    · intro z hz
      change b ≤ score v (z+u)
      rw [score_add, hu]
      simpa [halfPlane] using hz
    · intro z hz
      exact hregional z hz
  have hregionQ := hregion.nsmul Q
  let hs : List G :=
    ((Finset.univ.filter (fun i => score v (h i) ≠ 0)).toList.map h)
  have htrans : ∀ k ∈ hs, score v k ≠ 0 := by
    intro k hk
    obtain ⟨i,hi,hik⟩ := List.mem_map.mp hk
    have hi' := (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    simpa [hik] using hi'
  have htann : iteratedIncrement hs (∑ i, T i) = 0 := by
    rw [iteratedIncrement_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : score v (h i) = 0
    · simp [T, hi]
    · have himem : h i ∈ hs := by
        apply List.mem_map.mpr
        exact ⟨i,Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩),rfl⟩
      simpa [T, hi] using factor_kills_of_mem hs (h i) himem (F i) (hper i)
  have htiann : iteratedIncrement hs (increment (∑ i, T i) (Q • u)) = 0 := by
    rw [iteratedIncrement_commute, htann]
    funext z
    simp [PeriodicDifference.increment]
  have hzeroTail : ∀ z, b ≤ score v z →
      increment (∑ i, T i) (Q • u) z = 0 := by
    intro z hz
    have hreg := hregionQ.2 z hz
    have hzP := hp z
    have hsumz := congrFun hsplit z
    have hsumzQ := congrFun hsplit (z+Q•u)
    simp only [Pi.add_apply] at hsumz hsumzQ
    apply sub_eq_zero.mpr
    rw [hsumz, hsumzQ] at hreg
    exact add_right_cancel (by
      calc
        (∑ i, T i) (z+Q•u) + (∑ i, P i) z =
            (∑ i, P i) (z+Q•u) + (∑ i, T i) (z+Q•u) := by rw [hzP]; abel
        _ = (∑ i, P i) z + (∑ i, T i) z := hreg
        _ = (∑ i, T i) z + (∑ i, P i) z := add_comm _ _)
  have htglobal := eq_zero_of_transverse_product hs
    (increment (∑ i, T i) (Q • u)) v b htrans htiann hzeroTail
  have ht : IsPeriod (∑ i, T i) (Q • u) := by
    intro z
    exact sub_eq_zero.mp (congrFun htglobal z)
  refine ⟨Q,hQ,?_⟩
  rw [hsplit]
  exact hp.add_config ht

/-- Rational-boundary specialization, retaining the original convenient
integer-direction interface. -/
theorem halfPlane_period_extends
    (F : ι → G → B) (h : ι → G) (hper : ∀ i, IsPeriod (F i) (h i))
    (hzero : ∀ i, h i ≠ 0)
    (u : G) (b : ℝ)
    (hregional : ∀ z, b ≤ score (embed u) z →
      (∑ i, F i) (z+u) = (∑ i, F i) z) :
    ∃ Q : ℕ, 0 < Q ∧ IsPeriod (∑ i, F i) (Q • u) := by
  by_cases hu : u = 0
  · subst u
    exact ⟨1, by omega, by simp [IsPeriod]⟩
  · have hv : embed u ≠ 0 := by
      intro he
      exact hu (embed_injective (by simpa using he))
    exact halfPlane_period_extends_of_tangent F h hper hzero
      (embed u) hv u (score_embed_self u) b hregional

end

end NivatTrial.ColleHalfPlanePeriod
