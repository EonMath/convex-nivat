import ConvexNivat.Colle.Shared.AlgebraDefinitions
import ConvexNivat.Colle.Shared.Definitions
import ConvexNivat.SpectralNewton

namespace ConvexNivat.Colle
open scoped BigOperators Pointwise
noncomputable section

theorem convexLatticeWindow_hull (T : Finset Lattice) :
    windowHull (convexLatticeWindow T) = windowHull T := by
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨z, hz, rfl⟩
    exact (lattice_windowHull_finite T).mem_toFinset.mp hz
  · apply convexHull_mono
    apply Set.image_mono
    intro z hz
    exact (lattice_windowHull_finite T).mem_toFinset.mpr
      (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)

theorem reflected_windowHull (T : Finset Lattice) :
    windowHull (T.image Neg.neg) = -windowHull T := by
  have he : embed '' (↑(T.image Neg.neg) : Set Lattice) =
      -(embed '' (T : Set Lattice)) := by
    ext x
    simp only [Finset.coe_image, Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, by ext <;> simp [embed]⟩
    · rintro ⟨u, hu, he⟩
      refine ⟨-u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← neg_inj] at he
      simpa [embed] using he
  unfold windowHull
  rw [he, convexHull_neg]

theorem complex_support_product_hull (φ ψ : ComplexLaurent) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    windowHull (complexSupportWindow (φ * ψ)) =
      realMinkowski (windowHull (complexSupportWindow φ))
        (windowHull (complexSupportWindow ψ)) := by
  unfold complexSupportWindow
  simp_rw [convexLatticeWindow_hull, reflected_windowHull]
  rw [laurent_newton_polygon_mul φ ψ hφ hψ]
  have hm (A B : Set RealPlane) : realMinkowski A B = A + B := by
    ext x
    simp [realMinkowski, Set.mem_add, eq_comm]
  rw [hm]
  change -(windowHull φ.coeff.support + windowHull ψ.coeff.support) =
    (-windowHull φ.coeff.support) + (-windowHull ψ.coeff.support)
  exact neg_add _ _


theorem complexSupportWindow_mem_hull (φ : ComplexLaurent) (z : Lattice) :
    z ∈ complexSupportWindow φ ↔ embed z ∈ windowHull (complexSupportWindow φ) := by
  unfold complexSupportWindow
  rw [convexLatticeWindow_hull]
  exact (lattice_windowHull_finite _).mem_toFinset

theorem complexSupportWindow_of_support (φ : ComplexLaurent) (z : Lattice)
    (hz : z ∈ φ.coeff.support) : -z ∈ complexSupportWindow φ := by
  apply (complexSupportWindow_mem_hull φ (-z)).mpr
  unfold complexSupportWindow
  rw [convexLatticeWindow_hull]
  exact window_mem_hull _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

theorem hull_det_lower (S : Finset Lattice) (v : Lattice) (c : ℤ)
    (hS : ∀ z ∈ S, c ≤ det v z) (z : Lattice) (hz : embed z ∈ windowHull S) :
    c ≤ det v z := by
  let L : RealPlane →ₗ[ℝ] ℝ :=
    (v.1 : ℝ) • LinearMap.snd ℝ ℝ ℝ - (v.2 : ℝ) • LinearMap.fst ℝ ℝ ℝ
  have he (q : Lattice) : L (embed q) = (det v q : ℝ) := by simp [L, embed, det]
  have hHull : windowHull S ⊆ {x | (c : ℝ) ≤ L x} := by
    apply convexHull_min
    · rintro x ⟨q, hq, rfl⟩
      change (c : ℝ) ≤ L (embed q)
      rw [he]
      exact_mod_cast hS q hq
    · exact (convex_Ici (c : ℝ)).linear_preimage L
  have hh := hHull hz
  change (c : ℝ) ≤ L (embed z) at hh
  rw [he] at hh
  exact_mod_cast hh

theorem line_factor_support_edge (φ ψ : ComplexLaurent) (v : Lattice)
    (hline : LinePolynomial φ v) (hψ : ψ ≠ 0) (hdivides : φ ∣ ψ)
    (harea : (interior (windowHull (complexSupportWindow ψ))).Nonempty) :
    ∃ d ∈ edgeDirections (complexSupportWindow ψ), det d v = 0 := by
  classical
  obtain ⟨hprim, hcard, o, hlineall⟩ := hline
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < φ.coeff.support.card)
  have hφ : φ ≠ 0 := by
    intro he
    simpa [he] using hp
  obtain ⟨χ, rfl⟩ := hdivides
  have hχ : χ ≠ 0 := by
    intro he
    simp [he] at hψ
  have hχS : χ.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun he => hχ (AddMonoidAlgebra.coeff_injective he))
  obtain ⟨u, hu, hmax⟩ := χ.coeff.support.exists_max_image (det v) hχS
  have hlevel (r : Lattice) (hr : r ∈ φ.coeff.support) : det v r = det v o := by
    obtain ⟨a, rfl⟩ := hlineall r hr
    simp [det]
    ring
  have hbound (z : Lattice) (hz : z ∈ (φ * χ).coeff.support.image Neg.neg) :
      -(det v o + det v u) ≤ det v z := by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset φ χ hr)
    have he : det v (-(a + b)) = -(det v a + det v b) := by simp [det]; ring
    rw [he, hlevel a ha]
    have hh := hmax b hb
    omega
  have hbelow (z : Lattice) (hz : z ∈ complexSupportWindow (φ * χ)) :
      -(det v o + det v u) ≤ det v z := by
    exact hull_det_lower _ v _ hbound z ((lattice_windowHull_finite _).mem_toFinset.mp hz)
  have hmem (r : Lattice) (hr : r ∈ φ.coeff.support) :
      -(r + u) ∈ complexSupportWindow (φ * χ) := by
    apply (complexSupportWindow_mem_hull _ _).mpr
    rw [complex_support_product_hull φ χ hφ hχ]
    refine ⟨embed (-r), window_mem_hull _ (complexSupportWindow_of_support φ r hr),
      embed (-u), window_mem_hull _ (complexSupportWindow_of_support χ u hu), ?_⟩
    ext <;> simp [embed] <;> ring
  have hrow (r : Lattice) (hr : r ∈ φ.coeff.support) :
      -(r + u) ∈ supportRow (complexSupportWindow (φ * χ)) v := by
    refine Finset.mem_filter.mpr ⟨hmem r hr, ?_⟩
    intro z hz
    have he : det v (-(r + u)) = -(det v o + det v u) := by
      rw [show det v (-(r + u)) = -(det v r + det v u) by simp [det]; ring, hlevel r hr]
    have hh : det v (-(r + u)) ≤ det v z := by rw [he]; exact hbelow z hz
    have cast : (det v (-(r + u)) : ℝ) ≤ (det v z : ℝ) := by exact_mod_cast hh
    simp only [realDot, embed, normal, det, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_add, Prod.snd_add, Int.cast_sub, Int.cast_mul] at cast ⊢
    nlinarith
  refine ⟨v, ⟨hprim, harea, ?_⟩, ?_⟩
  · have htwo : 1 < (supportRow (complexSupportWindow (φ * χ)) v).card :=
      Finset.one_lt_card.mpr ⟨-(p + u), hrow p hp, -(q + u), hrow q hq, ?_⟩
    · omega
    · intro he
      exact hpq (add_right_cancel (neg_injective he))
  · simp [det, mul_comm]

end
end ConvexNivat.Colle
