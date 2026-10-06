import NivatTrial.QuotientIdeals
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Passing the finite two-direction exponent blocks to the global quotient. -/

namespace NivatTrial.QuotientLinear

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.CoefficientField
open NivatTrial.QuotientFactors NivatTrial.QuotientIdeals
open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem aCofactor_mul (v : ι → G) (S : ι → Finset ℂˣ) (i : ι) :
    aCofactor v S i * aFactor (v i) (S i) = aProduct v S := by
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem cCofactor_mul (v : ι → G) (S : ι → Finset ℂˣ) (j : ι) :
    cCofactor v S j * cFactor (v j) (S j) = cProduct v S := by
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ j)

@[simp] theorem projection_aProduct (v : ι → G) (S : ι → Finset ℂˣ) :
    projection v S (aProduct v S) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_insert _ _)

@[simp] theorem projection_cProduct (v : ι → G) (S : ι → Finset ℂˣ) :
    projection v S (cProduct v S) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem projector_aFactor_zero (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) :
    projection v S (projector v S i j * aFactor (v i) (S i)) = 0 := by
  have heq : projector v S i j * aFactor (v i) (S i) =
      cCofactor v S j * aProduct v S := by
    rw [← aCofactor_mul v S i, projector]
    ring
  simp only [heq, map_mul, projection_aProduct]
  exact mul_zero (projection v S (cCofactor v S j))

theorem projector_cFactor_zero (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) :
    projection v S (projector v S i j * cFactor (v j) (S j)) = 0 := by
  have heq : projector v S i j * cFactor (v j) (S j) =
      aCofactor v S i * cProduct v S := by
    rw [← cCofactor_mul v S j, projector]
    ring
  simp only [heq, map_mul, projection_cProduct]
  exact mul_zero (projection v S (aCofactor v S i))

theorem cFactor_scaled (v : G) (S : Finset ℂˣ) :
    cFactor v S = Polynomial.aeval (AddMonoidAlgebra.single (-v) 1)
      (scaledRelation (rootPolynomial S) (xUnit v : K)) := by
  rw [scaledRelation_aeval, cFactor]
  congr 1

def pairIdeal (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) : Ideal R :=
  twoRelationIdeal (v i) (-v j) (rootPolynomial (S i))
    (scaledRelation (rootPolynomial (S j)) (xUnit (v j) : K))

abbrev pairQuotient (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) := R ⧸ pairIdeal v S i j

theorem pairIdeal_eq (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) :
    pairIdeal v S i j = Ideal.span {aFactor (v i) (S i), cFactor (v j) (S j)} := by
  simp only [pairIdeal, twoRelationIdeal, ← cFactor_scaled]
  rfl

def projectorMap (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) :
    R →ₗ[K] relationQuotient v S where
  toFun r := projection v S (projector v S i j * r)
  map_add' r s := by simp [mul_add]
  map_smul' a r := by
    simpa only [mul_smul_comm, AlgHom.toLinearMap_apply, RingHom.id_apply] using
      (projection v S).toLinearMap.map_smul a (projector v S i j * r)

@[simp] theorem projectorMap_apply (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) (r : R) :
    projectorMap v S i j r = projection v S (projector v S i j * r) := rfl

theorem pairIdeal_le_projector_kernel (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) :
    (pairIdeal v S i j).restrictScalars K ≤ LinearMap.ker (projectorMap v S i j) := by
  intro x hx
  change x ∈ pairIdeal v S i j at hx
  rw [pairIdeal_eq] at hx
  have h : ∀ r : R, projection v S (projector v S i j * (r * x)) = 0 := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · intro r
        rw [show projector v S i j * (r * aFactor (v i) (S i)) =
          r * (projector v S i j * aFactor (v i) (S i)) by ring,
          map_mul, projector_aFactor_zero]
        exact mul_zero (projection v S r)
      · obtain rfl := Set.mem_singleton_iff.mp hy
        intro r
        rw [show projector v S i j * (r * cFactor (v j) (S j)) =
          r * (projector v S i j * cFactor (v j) (S j)) by ring,
          map_mul, projector_cFactor_zero]
        exact mul_zero (projection v S r)
    | zero => intro r; simp
    | add x y _ _ hx hy => intro r; simp [mul_add, hx r, hy r]
    | smul a y _ hy =>
      intro r
      simpa only [smul_eq_mul, mul_assoc] using hy (r * a)
  change projection v S (projector v S i j * x) = 0
  simpa only [one_mul] using h 1

def localProjector (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) :
    pairQuotient v S i j →ₗ[K] relationQuotient v S :=
  ((pairIdeal v S i j).restrictScalars K).liftQ
    (projectorMap v S i j) (pairIdeal_le_projector_kernel v S i j) |>.comp
    (Submodule.Quotient.restrictScalarsEquiv K (pairIdeal v S i j)).symm.toLinearMap

@[simp] theorem localProjector_projection (v : ι → G) (S : ι → Finset ℂˣ)
    (i j : ι) (r : R) :
    localProjector v S i j (Ideal.Quotient.mkₐ K (pairIdeal v S i j) r) =
      projection v S (projector v S i j * r) := rfl

theorem pairQuotient_span (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι)
    (hdet : det (v i) (-v j) ≠ 0) :
    Submodule.span K ((fun e : G => Ideal.Quotient.mkₐ K (pairIdeal v S i j)
      (AddMonoidAlgebra.single e 1)) '' exponentBlock (v i) (-v j) (S i).card (S j).card) = ⊤ := by
  have hspan := exponentBlock_monomials_span (v i) (-v j) hdet
    (rootPolynomial (S i)) (scaledRelation (rootPolynomial (S j)) (xUnit (v j) : K))
    (rootPolynomial_constant_ne_zero (S i))
    (scaledRelation_constant_ne_zero (rootPolynomial_constant_ne_zero (S j)) _)
  change Submodule.span K ((fun e : G => Ideal.Quotient.mkₐ K (pairIdeal v S i j)
      (AddMonoidAlgebra.single e 1)) '' exponentBlock (v i) (-v j)
      (rootPolynomial (S i)).natDegree
      (scaledRelation (rootPolynomial (S j)) (xUnit (v j) : K)).natDegree) = ⊤ at hspan
  simpa only [rootPolynomial_natDegree,
    scaledRelation_natDegree (rootPolynomial (S j)) (Units.ne_zero (xUnit (v j)))] using hspan

theorem projector_mul_mem (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι)
    (hdet : det (v i) (-v j) ≠ 0) (N : Submodule K (relationQuotient v S))
    (hblock : ∀ e ∈ exponentBlock (v i) (-v j) (S i).card (S j).card,
      projection v S (projector v S i j * AddMonoidAlgebra.single e 1) ∈ N)
    (r : R) : projection v S (projector v S i j * r) ∈ N := by
  have hle : Submodule.span K ((fun e : G => Ideal.Quotient.mkₐ K (pairIdeal v S i j)
      (AddMonoidAlgebra.single e 1)) '' exponentBlock (v i) (-v j) (S i).card (S j).card) ≤
      N.comap (localProjector v S i j) := by
    apply Submodule.span_le.mpr
    rintro x ⟨e, he, rfl⟩
    exact hblock e he
  rw [pairQuotient_span v S i j hdet] at hle
  exact hle (Submodule.mem_top : Ideal.Quotient.mkₐ K (pairIdeal v S i j) r ∈ ⊤)

/-- Once the finite projector blocks belong to a subspace, the proved unit
ideal generation forces every element of the global quotient into it. -/
theorem global_span_of_projector_blocks (v : ι → G) (S : ι → Finset ℂˣ)
    (hv : ∀ i, v i ≠ 0) (hdet : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (N : Submodule K (relationQuotient v S))
    (hblock : ∀ i j, i ≠ j → ∀ e ∈ exponentBlock (v i) (-v j) (S i).card (S j).card,
      projection v S (projector v S i j * AddMonoidAlgebra.single e 1) ∈ N) : N = ⊤ := by
  have hneg i j (hij : i ≠ j) : det (v i) (-v j) ≠ 0 := by
    have heq : det (v i) (-v j) = -det (v i) (v j) := by simp [det]; ring
    rw [heq]
    exact neg_ne_zero.mpr (hdet i j hij)
  have hone : (1 : R) ∈ Ideal.span (globalGenerators v S) := by
    rw [globalGenerators_span_top v S hv hdet]
    exact Submodule.mem_top
  have hall (x : R) (hx : x ∈ Ideal.span (globalGenerators v S)) :
      ∀ r : R, projection v S (r * x) ∈ N := by
    induction hx using Submodule.span_induction with
    | mem g hg =>
      rcases hg with hg | ⟨ij, rfl⟩
      · rcases Set.mem_insert_iff.mp hg with rfl | hg
        · intro r
          have hzero : projection v S (r * aProduct v S) = 0 := by
            rw [map_mul, projection_aProduct]
            exact mul_zero (projection v S r)
          rw [hzero]
          exact N.zero_mem
        · obtain rfl := Set.mem_singleton_iff.mp hg
          intro r
          have hzero : projection v S (r * cProduct v S) = 0 := by
            rw [map_mul, projection_cProduct]
            exact mul_zero (projection v S r)
          rw [hzero]
          exact N.zero_mem
      · intro r
        rw [mul_comm]
        exact projector_mul_mem v S ij.val.1 ij.val.2 (hneg _ _ ij.property) N
          (hblock _ _ ij.property) r
    | zero => intro r; simpa using N.zero_mem
    | add x y _ _ hx hy => intro r; simpa only [mul_add, map_add] using N.add_mem (hx r) (hy r)
    | smul a x _ hx => intro r; simpa only [smul_eq_mul, mul_assoc] using hx (r * a)
  apply top_unique
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (relationIdeal v S) x
  change projection v S r ∈ N
  simpa only [mul_one] using hall 1 hone r

end

end NivatTrial.QuotientLinear
