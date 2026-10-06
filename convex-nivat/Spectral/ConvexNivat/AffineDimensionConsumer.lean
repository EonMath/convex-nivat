import ConvexNivat.AffineRelationConsumer
import ConvexNivat.RationalKernel
import ConvexNivat.Geometry.Basic
import ConvexNivat.Geometry.ZonotopeBasic
import ConvexNivat.ExceptionalNewton

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section
set_option maxHeartbeats 1600000

theorem affine_observable_dimension_budget {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (hw : SpectrumPreservingEncoding star periods w)
    (S : Finset Lattice) (hS : LatticeConvex S) :
    S.card + 1 ≤ Module.finrank ℚ (affineObservableSpace star w S) +
      (erosion (spectralZonotope star periods).carrier S).ncard := by
  classical
  let I := {s : Lattice // s ∈ S}
  let n := S.card + 1
  let e : Fin n ≃ Option I := Fintype.equivOfCardEq (by simp [n, I])
  let obs : Fin n → OccurringPattern star S → ℚ := fun j γ =>
    match e j with
    | none => 1
    | some s => (w (γ.val s) : ℚ)
  let coeff : Lattice → Fin n → ℚ := fun u j =>
    obs j ⟨pattern star.configuration S u, ⟨u, rfl⟩⟩
  let L : (Fin n → ℚ) →ₗ[ℚ] (OccurringPattern star S → ℚ) :=
    Fintype.linearCombination ℚ obs
  have hrange : L.range = affineObservableSpace star w S := by
    rw [Fintype.range_linearCombination]
    unfold affineObservableSpace
    congr 1
    ext g
    constructor
    · rintro ⟨j, rfl⟩
      cases h : e j with
      | none => exact Or.inl (by simp [obs, h])
      | some s => exact Or.inr ⟨s, by simp [obs, h]⟩
    · rintro (h | ⟨s, rfl⟩)
      · simp only [Set.mem_singleton_iff] at h
        exact ⟨e.symm none, by simp [obs, h]⟩
      · exact ⟨e.symm (some s), by simp [obs]⟩
  have hker : L.ker = rationalSystemKernel coeff ℚ := by
    have heq (x : Fin n → ℚ) (u : Lattice) :
        rationalSystemEquation coeff ℚ u x =
          L x ⟨pattern star.configuration S u, ⟨u, rfl⟩⟩ := by
      simp only [rationalSystemEquation, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, Algebra.algebraMap_self, RingHom.id_apply,
        smul_eq_mul, L, Fintype.linearCombination_apply,
        Finset.sum_apply, Pi.smul_apply, coeff]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    ext x
    simp only [LinearMap.mem_ker, rationalSystemKernel, Submodule.mem_iInf]
    constructor
    · intro hx u
      have h := congrFun hx ⟨pattern star.configuration S u, ⟨u, rfl⟩⟩
      exact (heq x u).trans h
    · intro hx
      funext γ
      obtain ⟨u, hu⟩ := γ.property
      have hγ : γ = ⟨pattern star.configuration S u, ⟨u, rfl⟩⟩ := Subtype.ext hu.symm
      rw [hγ]
      exact (heq x u).symm.trans (hx u)
  have hnull := L.finrank_range_add_finrank_ker
  rw [hrange, hker, Module.finrank_fin_fun] at hnull
  have hfield := rational_system_kernel_dimension coeff
  let RC := rationalSystemKernel coeff ℂ
  let P : (Fin n → ℂ) →ₗ[ℂ] LaurentPolynomial :=
    { toFun := fun x => ∑ s : I, AddMonoidAlgebra.single s.val (x (e.symm (some s)))
      map_add' := by intro x y; simp [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Pi.smul_apply, Finset.smul_sum] }
  have hcoeff (x : Fin n → ℂ) (s : I) : (P x).coeff s.val = x (e.symm (some s)) := by
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    have htest (t : I) : (t.val = s.val) ↔ t = s := Subtype.ext_iff.symm
    simp_rw [htest]
    simpa only [Finset.mem_univ, ite_true] using
      Finset.sum_ite_eq' Finset.univ s (fun t : I => x (e.symm (some t)))
  have hsupport (x : Fin n → ℂ) : (P x).coeff.support ⊆ S := by
    intro z hz
    by_contra hzs
    have he : (P x).coeff z = 0 := by
      simp only [P, LinearMap.coe_mk, AddHom.coe_mk, AddMonoidAlgebra.coeff_sum,
        Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      apply Finset.sum_eq_zero
      intro s _
      have hne : z ≠ s.val := by intro h; exact hzs (h.symm ▸ s.property)
      simp [Ne.symm hne]
    exact (Finsupp.mem_support_iff.mp hz) he
  have hrow (x : RC) (u : Lattice) :
      x.val (e.symm none) + ∑ s : I, x.val (e.symm (some s)) *
        (w (star.configuration (u + s.val)) : ℂ) = 0 := by
    have h := x.property
    simp only [RC, rationalSystemKernel, Submodule.mem_iInf, LinearMap.mem_ker] at h
    have hh := h u
    simp only [rationalSystemEquation, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul] at hh
    rw [← e.symm.sum_comp] at hh
    simpa [coeff, obs, Fintype.sum_option, pattern, mul_comm] using hh
  have haction (x : Fin n → ℂ) :
      applyLaurent (P x) (encodedStar star w) = fun u =>
        ∑ s : I, x (e.symm (some s)) * (w (star.configuration (u + s.val)) : ℂ) := by
    let act : LaurentPolynomial →+ ScalarField :=
      { toFun := fun f => applyLaurent f (encodedStar star w)
        map_zero' := applyLaurent_zero _
        map_add' := fun f g => applyLaurent_add f g _ }
    change act (∑ s : I, _) = _
    rw [map_sum]
    funext u
    simp [act, applyLaurent_single, encodedStar]
  have hdiv (x : RC) : exceptionalPolynomial star periods ∣ P x.val := by
    by_cases hx : P x.val = 0
    · rw [hx]
      exact dvd_zero _
    · apply affine_relation_divisible star periods w hw _ hx
      refine ⟨-x.val (e.symm none), ?_⟩
      rw [haction]
      funext u
      have h := hrow x u
      exact eq_neg_of_add_eq_zero_right h
  let A := exceptionalPolynomial star periods
  have hA : A ≠ 0 := exceptional_polynomial_nonzero star periods
  let R := erosion (spectralZonotope star periods).carrier S
  have hR : R.Finite := erosion_finite hS (IntegralZonotope.zero_mem _)
  let Q : RC → LaurentPolynomial := fun x => Classical.choose (hdiv x)
  have hQ (x : RC) : P x.val = A * Q x := Classical.choose_spec (hdiv x)
  have hQsupport (x : RC) : ((Q x).coeff.support : Set Lattice) ⊆ R := by
    by_cases hq : Q x = 0
    · simp [hq]
    have hp : P x.val ≠ 0 := by rw [hQ]; exact mul_ne_zero hA hq
    have hnewt := laurent_newton_polygon_mul A (Q x) hA hq
    rw [← hQ] at hnewt
    change windowHull (P x.val).coeff.support = newtonPolygon A +
      windowHull (Q x).coeff.support at hnewt
    rw [show A = exceptionalPolynomial star periods from rfl,
      exceptional_polynomial_newton] at hnewt
    have hsub : windowHull (P x.val).coeff.support ⊆ windowHull S :=
      convexHull_mono (Set.image_mono (by exact hsupport x.val))
    intro r hr y hy
    apply hsub
    rw [hnewt, add_comm (embed r)]
    exact Set.add_mem_add hy (window_mem_hull _ hr)
  let D : RC →ₗ[ℂ] (R → ℂ) :=
    { toFun := fun x r => (Q x).coeff r.val
      map_add' := by
        intro x y
        have hq : Q (x + y) = Q x + Q y := by
          apply mul_left_cancel₀ hA
          rw [← hQ, mul_add, ← hQ, ← hQ]
          exact P.map_add _ _
        funext r
        simp [hq]
      map_smul' := by
        intro c x
        have hq : Q (c • x) = c • Q x := by
          apply mul_left_cancel₀ hA
          rw [← hQ, mul_smul_comm, ← hQ]
          exact P.map_smul c x.val
        funext r
        simp [hq] }
  have hD : Function.Injective D := by
    intro x y hxy
    have hqeq : Q x = Q y := by
      apply AddMonoidAlgebra.coeff_injective
      ext r
      by_cases hr : r ∈ R
      · exact congrFun hxy ⟨r, hr⟩
      · have hxr : r ∉ (Q x).coeff.support := fun h => hr (hQsupport x h)
        have hyr : r ∉ (Q y).coeff.support := fun h => hr (hQsupport y h)
        simp [Finsupp.notMem_support_iff.mp hxr, Finsupp.notMem_support_iff.mp hyr]
    have hpeq : P x.val = P y.val := by rw [hQ, hQ, hqeq]
    have hs (s : I) : x.val (e.symm (some s)) = y.val (e.symm (some s)) := by
      rw [← hcoeff x.val s, ← hcoeff y.val s, hpeq]
    have hn : x.val (e.symm none) = y.val (e.symm none) := by
      have hx := hrow x 0
      have hy := hrow y 0
      have hsum : (∑ s : I, x.val (e.symm (some s)) *
          (w (star.configuration (0 + s.val)) : ℂ)) =
        ∑ s : I, y.val (e.symm (some s)) * (w (star.configuration (0 + s.val)) : ℂ) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [hs s]
      rw [hsum] at hx
      exact add_right_cancel (hx.trans hy.symm)
    apply Subtype.ext
    funext j
    have hj : j = e.symm (e j) := (e.symm_apply_apply j).symm
    rw [hj]
    cases e j with
    | none => exact hn
    | some s => exact hs s
  let : Fintype R := hR.fintype
  have hbound := D.finrank_le_finrank_of_injective hD
  simp only [Module.finrank_pi] at hbound
  rw [Set.fintypeCard_eq_ncard] at hbound
  change Module.finrank ℂ (rationalSystemKernel coeff ℂ) ≤ R.ncard at hbound
  rw [hfield] at hbound
  change Module.finrank ℚ (affineObservableSpace star w S) +
    Module.finrank ℚ (rationalSystemKernel coeff ℚ) = S.card + 1 at hnull
  exact hnull.symm.trans_le (Nat.add_le_add_left hbound _)

end
end ConvexNivat
