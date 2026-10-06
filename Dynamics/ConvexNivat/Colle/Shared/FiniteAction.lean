import ConvexNivat.Colle.Shared.Definitions

namespace ConvexNivat.Colle
noncomputable section

theorem finite_action_and_difference_orbit_transports (φ : IntegerLaurent)
    (ξ : Configuration ℤ) :
    (∀ u, laurentAction φ (translate u ξ) = translate u (laurentAction φ ξ)) ∧
    (∀ f : ℕ → Configuration ℤ, ∀ x, PointwiseLimit f x →
      PointwiseLimit (fun j => laurentAction φ (f j)) (laurentAction φ x)) ∧
    (∀ x ∈ OrbitClosure ξ, laurentAction φ x ∈ OrbitClosure (laurentAction φ ξ)) := by
  classical
  have htranslate (η : Configuration ℤ) (u : Lattice) :
      laurentAction φ (translate u η) = translate u (laurentAction φ η) := by
    funext z
    simp only [laurentAction, translate, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro q hq
    congr 2
    abel
  refine ⟨htranslate ξ, ?_, ?_⟩
  · intro f x hlim z
    have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ q ∈ φ.support,
        f n (z-q) = x (z-q) := by
      rw [Filter.eventually_all_finset]
      intro q hq
      exact Filter.eventually_atTop.2 (hlim (z-q))
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 hall
    refine ⟨N, ?_⟩
    intro n hn
    simp only [laurentAction,Finsupp.sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hN n hn q hq]
  · intro x hx S
    let T : Finset Lattice := (S.product φ.support).image (fun p => p.1-p.2)
    obtain ⟨u,hu⟩ := hx T
    refine ⟨u, ?_⟩
    intro z hz
    simp only [laurentAction,Finsupp.sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hT : z-q ∈ T := by
      exact Finset.mem_image.mpr ⟨(z,q),Finset.mem_product.mpr ⟨hz,hq⟩,rfl⟩
    rw [hu (z-q) hT]
    congr 2
    abel



end
end ConvexNivat.Colle
