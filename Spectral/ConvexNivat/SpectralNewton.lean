import ConvexNivat.SpectralLaurentBridge
import ConvexNivat.Geometry.Basic

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

/-- Newton-polygon additivity, the genuine supporting obligation in (2.3). -/
theorem laurent_newton_polygon_mul (f g : LaurentPolynomial) (hf : f ≠ 0) (hg : g ≠ 0) :
    windowHull (f * g).coeff.support = windowHull f.coeff.support +
      windowHull g.coeff.support := by
  classical
  have hfS : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun h => hf (AddMonoidAlgebra.coeff_injective h))
  have hgS : g.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun h => hg (AddMonoidAlgebra.coeff_injective h))
  have hmax (l : StrongDual ℝ RealPlane) :
      ∃ a ∈ f.coeff.support, ∃ b ∈ g.coeff.support,
        (∀ x ∈ f.coeff.support, l (embed x) ≤ l (embed a)) ∧
        (∀ y ∈ g.coeff.support, l (embed y) ≤ l (embed b)) ∧
        ∃ r ∈ (f * g).coeff.support, l (embed r) = l (embed a) + l (embed b) := by
    obtain ⟨a, ha, hfa⟩ := f.coeff.support.exists_max_image (fun z => l (embed z)) hfS
    obtain ⟨b, hb, hgb⟩ := g.coeff.support.exists_max_image (fun z => l (embed z)) hgS
    refine ⟨a, ha, b, hb, hfa, hgb, ?_⟩
    let F : LaurentPolynomial := AddMonoidAlgebra.ofCoeff
      (f.coeff.filter (fun x => l (embed x) = l (embed a)))
    let G : LaurentPolynomial := AddMonoidAlgebra.ofCoeff
      (g.coeff.filter (fun y => l (embed y) = l (embed b)))
    have hF : F ≠ 0 := by
      intro h
      have hh := congrArg (fun p : LaurentPolynomial => p.coeff a) h
      exact (Finsupp.mem_support_iff.mp ha) (by simpa [F] using hh)
    have hG : G ≠ 0 := by
      intro h
      have hh := congrArg (fun p : LaurentPolynomial => p.coeff b) h
      exact (Finsupp.mem_support_iff.mp hb) (by simpa [G] using hh)
    have hFG : (F * G).coeff ≠ 0 := by
      intro h
      exact (mul_ne_zero hF hG) (AddMonoidAlgebra.coeff_injective h)
    obtain ⟨r, hr⟩ := Finsupp.support_nonempty_iff.mpr hFG
    have hrweight : l (embed r) = l (embed a) + l (embed b) := by
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp
        (AddMonoidAlgebra.support_coeff_mul_subset F G hr)
      have hx' : l (embed x) = l (embed a) := (Finset.mem_filter.mp hx).2
      have hy' : l (embed y) = l (embed b) := (Finset.mem_filter.mp hy).2
      rw [embed_add, map_add, hx', hy']
    have hpairs (x : Lattice) (hx : x ∈ f.coeff.support)
        (y : Lattice) (hy : y ∈ g.coeff.support) (hxy : x + y = r) :
        l (embed x) = l (embed a) ∧ l (embed y) = l (embed b) := by
      have heq : l (embed x) + l (embed y) = l (embed a) + l (embed b) := by
        rw [← map_add, ← embed_add, hxy, hrweight]
      have hxle := hfa x hx
      have hyle := hgb y hy
      constructor <;> linarith
    have hcoeff : (F * G).coeff r = (f * g).coeff r := by
      simp only [AddMonoidAlgebra.coeff_mul, F, G, Finsupp.support_filter, Finset.sum_filter, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxa : l (embed x) = l (embed a)
      · simp only [ite_eq_left hxa]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hyb : l (embed y) = l (embed b)
        · simp only [ite_eq_left hyb, Finsupp.filter_apply, ite_eq_left hxa]
        · have hxy : x + y ≠ r := fun hh => hyb (hpairs x hx y hy hh).2
          simp only [ite_eq_right hyb, ite_eq_right hxy]
      · simp only [ite_eq_right hxa]
        symm
        apply Finset.sum_eq_zero
        intro y hy
        have hxy : x + y ≠ r := fun hh => hxa (hpairs x hx y hy hh).1
        simp only [ite_eq_right hxy]
    exact ⟨r, Finsupp.mem_support_iff.mpr (hcoeff ▸ Finsupp.mem_support_iff.mp hr), hrweight⟩
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro z ⟨q, hq, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp
        (AddMonoidAlgebra.support_coeff_mul_subset f g hq)
      rw [embed_add]
      exact Set.add_mem_add (window_mem_hull _ ha) (window_mem_hull _ hb)
    · exact (windowHull_convex _).add (windowHull_convex _)
  · rintro z ⟨x, hx, y, hy, rfl⟩
    by_contra hn
    obtain ⟨l, c, hl, hc⟩ := geometric_hahn_banach_closed_point
      (windowHull_convex (f * g).coeff.support)
      (windowHull_compact (f * g).coeff.support).isClosed hn
    obtain ⟨a, ha, b, hb, hfa, hgb, r, hr, heq⟩ := hmax l
    have hxle : l x ≤ l (embed a) := by
      have hs : windowHull f.coeff.support ⊆ {w | l w ≤ l (embed a)} :=
        convexHull_min (by rintro w ⟨q, hq, rfl⟩; exact hfa q hq)
          ((convex_Iic (l (embed a))).linear_preimage l.toLinearMap)
      exact hs hx
    have hyle : l y ≤ l (embed b) := by
      have hs : windowHull g.coeff.support ⊆ {w | l w ≤ l (embed b)} :=
        convexHull_min (by rintro w ⟨q, hq, rfl⟩; exact hgb q hq)
          ((convex_Iic (l (embed b))).linear_preimage l.toLinearMap)
      exact hs hy
    have hlt := hl (embed r) (window_mem_hull _ hr)
    rw [map_add] at hc
    linarith



end
end ConvexNivat
