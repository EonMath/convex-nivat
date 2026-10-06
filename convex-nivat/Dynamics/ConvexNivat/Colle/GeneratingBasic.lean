import ConvexNivat.Colle.Definitions

namespace ConvexNivat.Colle
open scoped BigOperators

theorem normal_height (v z : Lattice) : realDot (embed z) (normal v) = (det v z : ℝ) := by
  simp only [realDot, embed, normal, det, Int.cast_sub, Int.cast_mul]
  ring

theorem laurentAction_reflection (φ : IntegerLaurent) (ξ : Configuration ℤ) (z : Lattice) :
    laurentAction φ ξ z = integerLaurentAction (φ.mapDomain Neg.neg) ξ z := by
  unfold laurentAction integerLaurentAction
  rw [Finsupp.sum_mapDomain_index_inj (neg_injective : Function.Injective (Neg.neg : Lattice → Lattice))]
  simp only [sub_eq_add_neg]

theorem annihilator_source_bridge (ξ : Configuration ℤ) :
    HasNontrivialIntegerAnnihilator ξ ↔ ∃ φ : IntegerLaurent, φ ≠ 0 ∧ Annihilates φ ξ := by
  have invol (φ : IntegerLaurent) :
      (φ.mapDomain Neg.neg).mapDomain Neg.neg = φ := by
    rw [← Finsupp.mapDomain_fun_comp]
    simpa only [neg_neg, id_eq] using Finsupp.mapDomain_id (v := φ)
  constructor
  · rintro ⟨φ, hφ, hann⟩
    refine ⟨φ.mapDomain Neg.neg, ?_, ?_⟩
    · intro hz
      have := invol φ
      rw [hz, Finsupp.mapDomain_zero] at this
      exact hφ this.symm
    · intro z
      rw [laurentAction_reflection, invol]
      exact hann z
  · rintro ⟨φ, hφ, hann⟩
    refine ⟨φ.mapDomain Neg.neg, ?_, ?_⟩
    · intro hz
      have := invol φ
      rw [hz, Finsupp.mapDomain_zero] at this
      exact hφ this.symm
    · intro z
      rw [← laurentAction_reflection]
      exact hann z

theorem minimal_order_nonperiodic_ge_two (ξ : Configuration ℤ) (m : ℕ)
    (hξ : ¬ Periodic ξ) (hminimal : MinimalPeriodicOrder ℤ ξ m) : 2 ≤ m := by
  rcases hminimal.1 with ⟨D⟩
  by_contra hm
  have hm : m = 0 ∨ m = 1 := by omega
  rcases hm with rfl | rfl
  · apply hξ
    refine ⟨(1, 0), by simp, ?_⟩
    intro z
    rw [D.sum_eq, D.sum_eq]
    simp
  · apply hξ
    refine ⟨D.period 0, D.period_nonzero 0, ?_⟩
    intro z
    rw [D.sum_eq, D.sum_eq]
    simpa using D.has_period 0 z

end ConvexNivat.Colle
