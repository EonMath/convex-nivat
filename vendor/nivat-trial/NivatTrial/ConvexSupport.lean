import NivatTrial.Divisibility
import NivatTrial.LatticePolygon

/-! Convex support control for products of nondegenerate Laurent binomials.
The two extremes on each lattice line survive multiplication. Consequently
division by a binomial erodes every convex support bound by its segment. -/

namespace NivatTrial.ConvexSupport

open NivatTrial.Algebra NivatTrial.Divisibility
open scoped Classical

noncomputable section

theorem lattice_line_injective (z v : G) (hv : v ≠ 0) :
    Function.Injective (fun n : ℤ => z + n • v) := by
  intro n m h
  exact smul_left_injective ℤ hv (add_left_cancel h)

theorem coeff_binomial_mul (v : G) (lam : ℂ) (g : Laurent) (z : G) :
    (binomial v lam * g).coeff z = g.coeff (-v + z) - lam * g.coeff z := by
  simp [binomial, monomial, sub_mul, AddMonoidAlgebra.coeff_single_mul_apply]

/-- The first and last nonzero coefficients on the line give two nonzero
coefficients of the product enclosing both `z` and `z+v`. -/
theorem binomial_support_line_extremes (v : G) (hv : v ≠ 0) (lam : ℂ)
    (hlam : lam ≠ 0) (g : Laurent) (z : G) (hz : g.coeff z ≠ 0) :
    ∃ a b : ℤ, a ≤ 0 ∧ 1 ≤ b ∧
      (binomial v lam * g).coeff (z + a • v) ≠ 0 ∧
      (binomial v lam * g).coeff (z + b • v) ≠ 0 := by
  let I : Set ℤ := {n | g.coeff (z + n • v) ≠ 0}
  have hfinite : I.Finite := by
    have h := g.coeff.support.finite_toSet.preimage (lattice_line_injective z v hv).injOn
    have heq : I = (fun n : ℤ => z + n • v) ⁻¹' (g.coeff.support : Set G) := by
      ext n
      simp [I]
    rw [heq]
    exact h
  have hzero : (0 : ℤ) ∈ I := by simpa [I] using hz
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image I id hfinite ⟨0, hzero⟩
  obtain ⟨b, hb, hmax⟩ := Set.exists_max_image I id hfinite ⟨0, hzero⟩
  have ha0 : a ≤ 0 := hmin 0 hzero
  have hb0 : 0 ≤ b := hmax 0 hzero
  have hprev : g.coeff (z + (a - 1) • v) = 0 := by
    by_contra hn
    have h := hmin (a - 1) hn
    dsimp at h
    omega
  have hnext : g.coeff (z + (b + 1) • v) = 0 := by
    by_contra hn
    have h := hmax (b + 1) hn
    dsimp at h
    omega
  refine ⟨a, b + 1, ha0, by omega, ?_, ?_⟩
  · rw [coeff_binomial_mul]
    have heq : -v + (z + a • v) = z + (a - 1) • v := by
      rw [sub_smul, one_smul]
      abel
    rw [heq, hprev, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hlam ha)
  · rw [coeff_binomial_mul]
    have heq : -v + (z + (b + 1) • v) = z + b • v := by
      rw [add_smul, one_smul]
      abel
    rw [heq, hnext, mul_zero, sub_zero]
    exact hb

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem lineMap_cast (φ : G →+ E) (z v : G) (n : ℤ) :
    AffineMap.lineMap (φ z) (φ (z + v)) (n : ℝ) = φ (z + n • v) := by
  simp only [AffineMap.lineMap_apply, map_add, vsub_eq_sub, vadd_eq_add,
    add_sub_cancel_left, Int.cast_smul_eq_zsmul, map_zsmul, add_comm]

theorem convex_binomial_support (φ : G →+ E) (C : Set E) (hC : Convex ℝ C)
    (v : G) (hv : v ≠ 0) (lam : ℂ) (hlam : lam ≠ 0) (g : Laurent)
    (hbound : ∀ z, (binomial v lam * g).coeff z ≠ 0 → φ z ∈ C)
    (z : G) (hz : g.coeff z ≠ 0) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    φ z + t • φ v ∈ C := by
  obtain ⟨a, b, ha, hb, hleft, hright⟩ :=
    binomial_support_line_extremes v hv lam hlam g z hz
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (φ z) (φ (z + v))
  have hcv : Convex ℝ (L ⁻¹' C) := hC.affine_preimage L
  have hla : (a : ℝ) ∈ L ⁻¹' C := by
    change L (a : ℝ) ∈ C
    rw [show L (a : ℝ) = φ (z + a • v) from lineMap_cast φ z v a]
    exact hbound _ hleft
  have hlb : (b : ℝ) ∈ L ⁻¹' C := by
    change L (b : ℝ) ∈ C
    rw [show L (b : ℝ) = φ (z + b • v) from lineMap_cast φ z v b]
    exact hbound _ hright
  have hat : (a : ℝ) ≤ t := (by exact_mod_cast ha : (a : ℝ) ≤ 0).trans ht.1
  have htb : t ≤ (b : ℝ) := ht.2.trans (by exact_mod_cast hb : (1 : ℝ) ≤ b)
  have hmem := hcv.ordConnected.out hla hlb ⟨hat, htb⟩
  change L t ∈ C at hmem
  simpa [L, AffineMap.lineMap_apply, map_add, add_comm] using hmem

/-- Convex erosion is the correct induction invariant for a product of factors. -/
def erosion (C P : Set E) : Set E := {x | ∀ p ∈ P, x + p ∈ C}

theorem convex_erosion (C P : Set E) (hC : Convex ℝ C) : Convex ℝ (erosion C P) := by
  intro x hx y hy a b ha hb hab p hp
  have h := hC (hx p hp) (hy p hp) ha hb hab
  have heq : a • (x + p) + b • (y + p) = (a • x + b • y) + p := by
    rw [smul_add, smul_add]
    have hp' : a • p + b • p = p := by rw [← add_smul, hab, one_smul]
    calc
      a • x + a • p + (b • y + b • p) = (a • x + b • y) + (a • p + b • p) := by abel
      _ = (a • x + b • y) + p := by rw [hp']
  rwa [heq] at h

/-- Every choice of points in the factor segments can be added to each exponent
of the quotient without leaving the convex support bound of the product. -/
theorem convex_product_support {ι : Type*} (φ : G →+ E) (s : Finset ι)
    (v : ι → G) (lam : ι → ℂ) (g : Laurent) (C : Set E) (hC : Convex ℝ C)
    (hv : ∀ i ∈ s, v i ≠ 0) (hlam : ∀ i ∈ s, lam i ≠ 0)
    (hbound : ∀ z, ((∏ i ∈ s, binomial (v i) (lam i)) * g).coeff z ≠ 0 → φ z ∈ C)
    (z : G) (hz : g.coeff z ≠ 0) (t : ι → ℝ) (ht : ∀ i ∈ s, t i ∈ Set.Icc 0 1) :
    φ z + ∑ i ∈ s, t i • φ (v i) ∈ C := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simpa using hbound z (by simpa using hz)
  | @insert i s hi ih =>
    let P : Set E := (fun u : ℝ => u • φ (v i)) '' Set.Icc 0 1
    have hbound' : ∀ r, (binomial (v i) (lam i) *
        ((∏ j ∈ s, binomial (v j) (lam j)) * g)).coeff r ≠ 0 → φ r ∈ C := by
      intro r hr
      apply hbound r
      simpa only [Finset.prod_insert hi, mul_assoc] using hr
    have heroded : ∀ r, ((∏ j ∈ s, binomial (v j) (lam j)) * g).coeff r ≠ 0 →
        φ r ∈ erosion C P := by
      intro r hr p hp
      obtain ⟨u, hu, rfl⟩ := hp
      exact convex_binomial_support φ C hC (v i) (hv i (Finset.mem_insert_self i s))
        (lam i) (hlam i (Finset.mem_insert_self i s)) _ hbound' r hr u hu
    have h := ih (erosion C P) (convex_erosion C P hC)
      (fun j hj => hv j (Finset.mem_insert_of_mem hj))
      (fun j hj => hlam j (Finset.mem_insert_of_mem hj)) heroded
      (fun j hj => ht j (Finset.mem_insert_of_mem hj))
    have hp : t i • φ (v i) ∈ P := ⟨t i, ht i (Finset.mem_insert_self i s), rfl⟩
    have hresult := h _ hp
    simpa only [Finset.sum_insert hi, add_assoc, add_comm, add_left_comm] using hresult

theorem grouped_product_support {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (v : ι → G) (lam : (i : ι) → β i → ℂ)
    (hv : ∀ i, v i ≠ 0) (hlam : ∀ i k, lam i k ≠ 0)
    (g : Laurent) (S : Finset G)
    (hbound : ∀ z, ((∏ q : Sigma β, binomial (v q.1) (lam q.1 q.2)) * g).coeff z ≠ 0 → z ∈ S)
    (z : G) (hz : g.coeff z ≠ 0) :
    z ∈ LatticePolygon.placementSet
      (Zonotope.zonotope (fun i => Fintype.card (β i) • v i)) S := by
  intro x hx
  obtain ⟨t, ht, hsum⟩ := hx
  have h := convex_product_support Zonotope.embedHom (Finset.univ : Finset (Sigma β))
    (fun q => v q.1) (fun q => lam q.1 q.2) g (LatticePolygon.windowHull S)
    (LatticePolygon.windowHull_convex S) (fun q _ => hv q.1)
    (fun q _ => hlam q.1 q.2)
    (fun r hr => LatticePolygon.mem_windowHull_of_mem S (hbound r hr)) z hz
    (fun q => t q.1) (fun q _ => ht q.1)
  have heq : (∑ q : Sigma β, t q.1 • Zonotope.embed (v q.1)) = x := by
    rw [← hsum]
    unfold Zonotope.coeffPoint
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_const, Finset.card_univ, Zonotope.embed_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_comm]
  change Zonotope.embed z + ∑ q : Sigma β, t q.1 • Zonotope.embed (v q.1) ∈ _ at h
  rwa [heq] at h

end

end NivatTrial.ConvexSupport
