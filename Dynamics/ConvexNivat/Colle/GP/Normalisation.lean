import ConvexNivat.Colle.GP.Definitions

namespace ConvexNivat.Colle
noncomputable section

/-- GP10: normalization retains the original witness pair and uses plus-sampling shifts. -/
theorem highest_exterior_disagreement_normalisation (ξ x₀ y₀ : Configuration ℤ)
    (hx : x₀ ∈ OrbitClosure ξ) (hy : y₀ ∈ OrbitClosure ξ) (hne : x₀ ≠ y₀)
    (v : Lattice) (hv : Primitive v)
    (hagrees : AgreesOn x₀ y₀ (upperHalf v 0)) :
    ∃ b : ℤ, b < 0 ∧ (∃ z, det v z = b ∧ x₀ z ≠ y₀ z) ∧
      AgreesOn x₀ y₀ (upperHalf v (b + 1)) ∧
      ∀ μ : ℤ, ∃ a : Lattice, det v a = b - μ ∧
        translate a x₀ ∈ OrbitClosure ξ ∧ translate a y₀ ∈ OrbitClosure ξ ∧
        AgreesOn (translate a x₀) (translate a y₀) (upperHalf v (μ + 1)) ∧
        ∃ z, det v z = μ ∧ translate a x₀ z ≠ translate a y₀ z := by
  classical
  have hbad : ∃ z, x₀ z ≠ y₀ z := Function.ne_iff.mp hne
  have hbound : ∀ z, x₀ z ≠ y₀ z → det v z < 0 := by
    intro z hz
    exact lt_of_not_ge (fun hz0 => hz (hagrees z hz0))
  obtain ⟨b, ⟨z, hzb, hzbad⟩, hbmax⟩ := Int.exists_greatest_of_bdd
    (P := fun t => ∃ z, det v z = t ∧ x₀ z ≠ y₀ z)
    ⟨0, by rintro t ⟨z, rfl, hz⟩; exact (hbound z hz).le⟩
    (by obtain ⟨z, hz⟩ := hbad; exact ⟨det v z, z, rfl, hz⟩)
  have hequal : AgreesOn x₀ y₀ (upperHalf v (b + 1)) := by
    intro q hq
    by_contra hne
    have hqmax := hbmax (det v q) ⟨q, rfl, hne⟩
    change b + 1 ≤ det v q at hq
    omega
  refine ⟨b, by rw [← hzb]; exact hbound z hzbad, ⟨z, hzb, hzbad⟩, hequal, ?_⟩
  intro μ
  obtain ⟨a, ha⟩ := primitive_height_surjective v hv (b - μ)
  change det v a = b - μ at ha
  refine ⟨a, ha, orbitClosure_translate_member ξ x₀ hx a,
    orbitClosure_translate_member ξ y₀ hy a, ?_, z - a, ?_, ?_⟩
  · intro q hq
    apply hequal (q + a)
    have hadd := height_add v q a
    change det v (q + a) = det v q + det v a at hadd
    change μ + 1 ≤ det v q at hq
    change b + 1 ≤ det v (q + a)
    omega
  · dsimp [det] at ha hzb ⊢
    nlinarith
  · simpa [translate] using hzbad

end
end ConvexNivat.Colle
