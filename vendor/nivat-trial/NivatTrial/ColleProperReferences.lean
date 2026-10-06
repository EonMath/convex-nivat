import NivatTrial.ColleRegions

/-! A proper half-plane interface selects a reference whose slightly larger
half-plane cannot agree with any doubly periodic configuration. This local
obstruction survives the boundary orbit-limit used in Colle's second case. -/

namespace NivatTrial.ColleProperReferences

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Periodicity
open NivatTrial.Nonexpansive NivatTrial.ColleRegions
open scoped Classical
noncomputable section

def HasDoublyPeriodicExtension {A : Type*} (x : Lattice → A) (R : Set Lattice) : Prop :=
  ∃ p : Lattice → A, IsDoublyPeriodic p ∧ AgreeOn x p R

theorem doublyPeriodic_eq_of_shifted_halfPlane_agreement {A : Type*}
    {x y : Lattice → A} (hx : IsDoublyPeriodic x) (hy : IsDoublyPeriodic y)
    (v : ℝ×ℝ) (hv : v ≠ 0) (b : ℝ)
    (hxy : AgreeOn x y (halfPlane v b)) : x = y := by
  obtain ⟨g,hg⟩ := exists_positive_score hv
  obtain ⟨n,hn⟩ := exists_nat_gt (b/score v g)
  have hbound : b ≤ score v (n•g) := by
    rw [score_nsmul]
    exact ((div_lt_iff₀ hg).mp hn).le
  apply shift_injective (n•g)
  apply doublyPeriodic_eq_of_halfPlane_agreement (hx.shift _) (hy.shift _) hv
  intro z hz
  apply hxy
  change b ≤ score v (n•g+z)
  rw [score_add]
  have hz' : 0 ≤ score v z := hz
  linarith

theorem no_double_extension_for_both_sides {A : Type*}
    (x y : Lattice → A) (v : ℝ×ℝ) (hv : v ≠ 0) (b : ℝ)
    (hxy : AgreeOn x y (halfPlane v b))
    (R : Set Lattice) (hR : halfPlane v b ⊆ R)
    (hbad : ∃ z ∈ R, x z ≠ y z) :
    ¬HasDoublyPeriodicExtension x R ∨ ¬HasDoublyPeriodicExtension y R := by
  by_contra hn
  push Not at hn
  obtain ⟨p,hp,hxp⟩ := hn.1
  obtain ⟨q,hq,hyq⟩ := hn.2
  have hpq : p = q := doublyPeriodic_eq_of_shifted_halfPlane_agreement hp hq v hv b
    (fun z hz => (hxp z (hR hz)).symm.trans ((hxy z hz).trans (hyq z (hR hz))))
  obtain ⟨z,hz,hne⟩ := hbad
  exact hne ((hxp z hz).trans ((congrFun hpq z).trans (hyq z hz).symm))

theorem not_doublyPeriodic_of_reference_agreement {A : Type*}
    {p x : Lattice → A} {R : Set Lattice}
    (hp : ¬HasDoublyPeriodicExtension p R) (hpx : AgreeOn p x R) :
    ¬IsDoublyPeriodic x := fun hx => hp ⟨x,hx,hpx⟩

theorem extension_iff_tangent_shift {A : Type*}
    (p : Lattice → A) (v : ℝ×ℝ) (b : ℝ) (c : Lattice) (hc : score v c = 0) :
    HasDoublyPeriodicExtension (shift c p) (halfPlane v b) ↔
      HasDoublyPeriodicExtension p (halfPlane v b) := by
  constructor
  · rintro ⟨q,hq,hpq⟩
    refine ⟨shift (-c) q,hq.shift _,?_⟩
    intro z hz
    have hm : -c+z ∈ halfPlane v b := by
      change b ≤ score v (-c+z)
      simpa only [score_add,score_neg,hc,neg_zero,zero_add] using (show b ≤ score v z from hz)
    have he := hpq (-c+z) hm
    simpa only [shift_apply,add_neg_cancel_left] using he
  · rintro ⟨q,hq,hpq⟩
    refine ⟨shift c q,hq.shift _,?_⟩
    intro z hz
    have hm : c+z ∈ halfPlane v b := by
      change b ≤ score v (c+z)
      simpa only [score_add,hc,zero_add] using (show b ≤ score v z from hz)
    exact hpq (c+z) hm

end
end NivatTrial.ColleProperReferences
