import NivatTrial.KariSzabados

/-!
# Integral annihilators and periodic decompositions in a language hull

Both the finite alphabet condition and a fixed Laurent annihilator pass to
every finite-window limit of translates. Consequently the same algebraic
decomposition theorem applies to each point of the hull, with directions
chosen for that point.
-/

namespace NivatTrial.HullIntegerDecomposition

open NivatTrial.Dynamics NivatTrial.LaurentAction
open NivatTrial.Geometry NivatTrial.Periodicity

open scoped Classical
noncomputable section

theorem finite_range_of_languageHull (x ξ : Lattice → ℤ)
    (hx : (Set.range x).Finite) (hξ : ξ ∈ languageHull x) :
    (Set.range ξ).Finite := by
  apply hx.subset
  rintro a ⟨z, rfl⟩
  obtain ⟨u, hu⟩ := hξ {z}
  exact ⟨u + z, hu z (by simp)⟩

/-- The action has finite support in every output coordinate, so a local
Laurent relation is inherited by every element of the language hull. -/
theorem annihilator_passes_to_languageHull (f : RingLaurent ℤ)
    (x ξ : Lattice → ℤ) (hξ : ξ ∈ languageHull x)
    (hann : act f x = 0) : act f ξ = 0 := by
  funext z
  obtain ⟨u, hu⟩ := hξ (f.coeff.support.image (fun e => z + e))
  calc
    act f ξ z = act f x (u + z) := by
      simp only [act, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro e he
      have hz : x (u + (z + e)) = ξ (z + e) :=
        hu (z + e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      rw [show u + z + e = u + (z + e) by abel, hz]
    _ = 0 := congrFun hann (u + z)

/-- Each hull point inherits the annihilator and admits an actual integer
sum of periodic components in pairwise independent directions. -/
theorem decomposition_at_languageHull (x ξ : Lattice → ℤ)
    (hx : (Set.range x).Finite) (hξ : ξ ∈ languageHull x)
    (f : RingLaurent ℤ) (hf : f ≠ 0) (hann : act f x = 0) :
    ∃ (n : ℕ) (h : Fin n → Lattice) (F : Fin n → Lattice → ℤ),
      (∀ i, h i ≠ 0) ∧
      (∀ i j, i ≠ j → det (h i) (h j) ≠ 0) ∧
      (∀ i, IsPeriod (F i) (h i)) ∧
      (∑ i, F i) = ξ := by
  exact NivatTrial.KariSzabados.decomposition_of_integer_annihilator ξ
    (finite_range_of_languageHull x ξ hx hξ) f hf
    (annihilator_passes_to_languageHull f x ξ hξ hann)

end
end NivatTrial.HullIntegerDecomposition
