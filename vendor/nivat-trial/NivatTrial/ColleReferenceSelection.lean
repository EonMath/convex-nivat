import NivatTrial.ColleProperReferences

/-! A pair of genuinely distinct periodic interface configurations selects
a periodic reference whose boundary half-plane admits no doubly periodic
extension. The boundary is moved through an actual disagreement site. -/

namespace NivatTrial.ColleReferenceSelection

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.ColleProperReferences
open scoped Classical
noncomputable section

theorem extension_shift_iff {A : Type*}
    (p : Lattice → A) (v : ℝ×ℝ) (b : ℝ) (c : Lattice) :
    HasDoublyPeriodicExtension (shift c p) (halfPlane v b) ↔
      HasDoublyPeriodicExtension p (halfPlane v (b+score v c)) := by
  constructor
  · rintro ⟨q,hq,hpq⟩
    refine ⟨shift (-c) q,hq.shift _,?_⟩
    intro z hz
    have hm : -c+z ∈ halfPlane v b := by
      change b ≤ score v (-c+z)
      rw [score_add,score_neg]
      change b+score v c ≤ score v z at hz
      linarith
    have he := hpq (-c+z) hm
    simpa only [shift_apply,add_neg_cancel_left] using he
  · rintro ⟨q,hq,hpq⟩
    refine ⟨shift c q,hq.shift _,?_⟩
    intro z hz
    have hm : c+z ∈ halfPlane v (b+score v c) := by
      change b+score v c ≤ score v (c+z)
      rw [score_add]
      change b ≤ score v z at hz
      linarith
    exact hpq (c+z) hm

theorem exists_proper_periodic_reference_of_interface {A : Type*}
    (θ x y : Lattice → A) (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (u : Lattice)
    (hpx : ∃ q : ℕ, 0 < q ∧ IsPeriod x (q•u))
    (hpy : ∃ q : ℕ, 0 < q ∧ IsPeriod y (q•u))
    (v : ℝ×ℝ) (hv : v ≠ 0) (b : ℝ)
    (hxy : AgreeOn x y (halfPlane v b)) (hne : x ≠ y) :
    ∃ p ∈ languageHull θ, (∃ q : ℕ, 0 < q ∧ IsPeriod p (q•u)) ∧
      ¬HasDoublyPeriodicExtension p (halfPlane v 0) := by
  obtain ⟨z,hz⟩ : ∃ z, x z ≠ y z := by
    by_contra hn
    apply hne
    funext z
    by_contra he
    exact hn ⟨z,he⟩
  have hzscore : score v z < b := by
    by_contra hs
    exact hz (hxy z (le_of_not_gt hs))
  have hsub : halfPlane v b ⊆ halfPlane v (score v z) := by
    intro w hw
    exact hzscore.le.trans hw
  have hbad : ∃ w ∈ halfPlane v (score v z), x w ≠ y w :=
    ⟨z,by simp [halfPlane],hz⟩
  obtain hxp | hyp := no_double_extension_for_both_sides x y v hv b hxy
    (halfPlane v (score v z)) hsub hbad
  · obtain ⟨q,hq,hqperiod⟩ := hpx
    refine ⟨shift z x,shift_mem_languageHull hx z,⟨q,hq,hqperiod.shift z⟩,?_⟩
    intro he
    apply hxp
    simpa only [zero_add] using (extension_shift_iff x v 0 z).mp he
  · obtain ⟨q,hq,hqperiod⟩ := hpy
    refine ⟨shift z y,shift_mem_languageHull hy z,⟨q,hq,hqperiod.shift z⟩,?_⟩
    intro he
    apply hyp
    simpa only [zero_add] using (extension_shift_iff y v 0 z).mp he

end
end NivatTrial.ColleReferenceSelection
