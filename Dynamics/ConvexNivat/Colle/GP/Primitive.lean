import ConvexNivat.Colle.GP.Definitions

namespace ConvexNivat.Colle
noncomputable section

/-- GP00: the sign belongs to the primitive direction and the multiplier is positive. -/
theorem positive_primitive_integer_factor (h : Lattice) (hh : h ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ∃ v : Lattice, Primitive v ∧ h = (k : ℤ) • v := by
  have hg : 0 < Int.gcd h.1 h.2 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hc := Int.gcd_eq_zero_iff.mp hz
    exact hh (Prod.ext hc.1 hc.2)
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hg
  refine ⟨Int.gcd h.1 h.2, hg, (a, b), hab, ?_⟩
  exact Prod.ext (by simpa [mul_comm] using ha) (by simpa [mul_comm] using hb)

theorem primitive_parallel_orientation (v d : Lattice)
    (hv : Primitive v) (hd : Primitive d) (hparallel : det v d = 0) :
    d = v ∨ d = -v := by
  obtain ⟨u, hu⟩ := primitive_height_surjective v hv 1
  obtain ⟨w, hw⟩ := primitive_height_surjective d hd 1
  change det v u = 1 at hu
  change det d w = 1 at hw
  have hbasis : det v u • d = det d u • v + det v d • u := by
    ext <;> simp [det] <;> ring
  have heq : d = det d u • v := by simpa [hu, hparallel] using hbasis
  have hprod : det d u * det v w = 1 := by
    rw [heq] at hw
    simpa [det, mul_sub, mul_assoc] using hw
  have ht : det d u = 1 ∨ det d u = -1 := by
    exact Int.eq_one_or_neg_one_of_mul_eq_one hprod
  rcases ht with ht | ht
  · left; simpa [ht] using heq
  · right; simpa [ht] using heq

end
end ConvexNivat.Colle
