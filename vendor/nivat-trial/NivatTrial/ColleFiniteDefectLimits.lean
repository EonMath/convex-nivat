import NivatTrial.ColleEnvelopeLimits

/-! A finite set of possible disagreement sites is enough to retain a
genuine defect under compactness, even when the chosen site varies. -/

namespace NivatTrial.ColleFiniteDefectLimits

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.NonexpansiveExistence NivatTrial.ColleEnvelopeLimits
open Filter
open scoped Classical
noncomputable section

theorem limit_on_increasing_region_with_finite_defect {A : Type*} [Fintype A]
    (θ p : Lattice → A) (T : ℕ → Finset Lattice)
    (hmono : ∀ m n, m ≤ n → T m ⊆ T n)
    (x : ℕ → Lattice → A) (hx : ∀ n, x n ∈ languageHull θ)
    (hagree : ∀ n, ∀ z ∈ T n, x n z = p z)
    (S : Finset Lattice) (hbad : ∀ n, ∃ z ∈ S, x n z ≠ p z) :
    ∃ y ∈ languageHull θ, AgreeOn y p (increasingRegion T) ∧
      ∃ z ∈ S, y z ≠ p z := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨y,hy,φ,hφ,hlim⟩ := (isCompact_languageHull θ).tendsto_subseq hx
  refine ⟨y,hy,?_,?_⟩
  · rintro z ⟨m,hz⟩
    have hlarge : ∀ᶠ n : ℕ in atTop, m ≤ φ n :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop m)
    obtain ⟨n,hn,heq⟩ := (hlarge.and (eventually_coordinate_eq hlim z)).exists
    exact heq.symm.trans (hagree (φ n) z (hmono m (φ n) hn hz))
  · by_contra hn
    have hall : ∀ z ∈ S, y z = p z := by
      intro z hz
      by_contra he
      exact hn ⟨z,hz,he⟩
    have hevent : ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, x (φ n) z = y z := by
      apply S.eventually_all.mpr
      intro z hz
      simpa only [Function.comp_apply] using (eventually_coordinate_eq hlim z)
    obtain ⟨n,heq⟩ := hevent.exists
    obtain ⟨z,hz,hbadz⟩ := hbad (φ n)
    exact hbadz ((heq z hz).trans (hall z hz))

end
end NivatTrial.ColleFiniteDefectLimits
