import ConvexNivat.StarIsolated
import ConvexNivat.StarFiniteSupport

namespace ConvexNivat
open scoped BigOperators Pointwise
noncomputable section
set_option maxHeartbeats 1000000

private theorem applyLaurent_finset_sum {ι : Type*} (D : LaurentPolynomial)
    (s : Finset ι) (f : ι → ScalarField) :
    applyLaurent D (∑ i ∈ s, f i) = ∑ i ∈ s, applyLaurent D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext z; simp [applyLaurent]
  | @insert i s hi ih => rw [Finset.sum_insert hi, applyLaurent_add_field, ih, Finset.sum_insert hi]

/-- Vanishing of every two-point witness annihilates products of arbitrary
finite operator combinations of translates of the same scalar field. -/
private theorem all_quadratic_zero_product {D : LaurentPolynomial} {η : ScalarField}
    (hJ : ∀ δ, quadraticWitness D η δ = 0)
    (q r : LaurentPolynomial) (δ : Lattice) :
    applyLaurent D (fun z => applyLaurent q η z * applyLaurent r η (z+δ)) = 0 := by
  classical
  have hpair (u v : Lattice) :
      applyLaurent D (fun z => η (z+u) * η (z+δ+v)) = 0 := by
    have heq : (fun z => η (z+u) * η (z+δ+v)) =
        (fun z => (fun t => η t * η (t+(δ+v-u))) (z+u)) := by
      ext z
      congr 2
      abel
    rw [heq]
    have h := hJ (δ+v-u)
    exact (applyLaurent_translate D (fun t => η t * η (t+(δ+v-u))) u).trans
      (congrArg (fun f : ScalarField => fun z => f (z+u)) h)
  have hexpand : (fun z => applyLaurent q η z * applyLaurent r η (z+δ)) =
      ∑ u ∈ q.coeff.support, ∑ v ∈ r.coeff.support,
        (q.coeff u * r.coeff v) • (fun z => η (z+u) * η (z+δ+v)) := by
    ext z
    simp only [applyLaurent, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [hexpand, applyLaurent_finset_sum]
  apply Finset.sum_eq_zero
  intro u hu
  rw [applyLaurent_finset_sum]
  apply Finset.sum_eq_zero
  intro v hv
  rw [applyLaurent_smul_field, hpair]
  simp


 theorem quadraticWitness_finite_support {p : ℕ} (d : StarData p)
    (P : StarPeriodData d) (w : ZMod p → ℤ) (δ : Lattice) :
    ScalarHasFiniteSupport
      (quadraticWitness (starDifference P) (integerScalarEncoding d w) δ) := by
  classical
  let W : Finset Lattice := {0, δ}
  let φ : Pattern (ZMod p) W → ℂ := fun γ =>
    (w (γ ⟨0, by simp [W]⟩) : ℂ) * (w (γ ⟨δ, by simp [W]⟩) : ℂ)
  have heq : (fun z => integerScalarEncoding d w z * integerScalarEncoding d w (z+δ)) =
      starLocalFunction d W φ := by
    ext z
    simp [starLocalFunction, φ, pattern, integerScalarEncoding, scalarEncoding]
  unfold quadraticWitness
  rw [heq]
  exact lemma_1_1 d P W φ

 theorem lemma_4_2 {p : ℕ} (d : StarData p) (P : StarPeriodData d)
    (w : ZMod p → ℤ) (hw : Function.Injective w)
    (hD : ∀ a : ZMod p,
      applyLaurent (starDifference P) (scalarColourIndicator d.configuration a) = 0) :
    (∀ δ : Lattice, ScalarHasFiniteSupport
      (quadraticWitness (starDifference P) (integerScalarEncoding d w) δ)) ∧
      ∃ δ : Lattice, quadraticWitness (starDifference P) (integerScalarEncoding d w) δ ≠ 0 := by
  classical
  refine ⟨quadraticWitness_finite_support d P w, ?_⟩
  let i : Fin d.m := ⟨0, by have := d.two_le; omega⟩
  let j : Fin d.m := ⟨1, by have := d.two_le; omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  obtain ⟨⟨li, ri, hi⟩, hine⟩ := lemma_4_1 d P w hw hD i
  obtain ⟨⟨lj, rj, hj⟩, hjne⟩ := lemma_4_1 d P w hw hD j
  obtain ⟨xi, hxi⟩ := Function.ne_iff.mp hine
  obtain ⟨xj, hxj⟩ := Function.ne_iff.mp hjne
  let δ := xj-xi
  let C : ScalarField := fun z => isolatedScalarField P (integerScalarEncoding d w) i z *
    isolatedScalarField P (integerScalarEncoding d w) j (z+δ)
  have hCne : C ≠ 0 := by
    intro hzero
    have hxiδ : xi+δ = xj := by dsimp [δ]; abel
    have hz := congrFun hzero xi
    change isolatedScalarField P (integerScalarEncoding d w) i xi *
      isolatedScalarField P (integerScalarEncoding d w) j (xi+δ) = 0 at hz
    rw [hxiδ] at hz
    exact mul_ne_zero hxi hxj hz
  have hCfin : ScalarHasFiniteSupport C := by
    apply (nonparallel_strip_intersection_finite
      (d.component i).direction (d.component j).direction
      (d.pairwise_nonparallel i j hij) li ri
      (lj-height (d.component j).direction δ)
      (rj-height (d.component j).direction δ)).subset
    intro z hz
    have hmul : isolatedScalarField P (integerScalarEncoding d w) i z *
      isolatedScalarField P (integerScalarEncoding d w) j (z+δ) ≠ 0 := hz
    have hzi := hi z (mul_ne_zero_iff.mp hmul).1
    have hzj := hj (z+δ) (mul_ne_zero_iff.mp hmul).2
    rw [height_add] at hzj
    exact ⟨hzi, by constructor <;> omega⟩
  have hDCne := lemma_1_2 C hCfin hCne (starDifference P) (starDifference_ne_zero d P)
  by_contra hzero
  push Not at hzero
  apply hDCne
  exact all_quadratic_zero_product hzero (starOtherDifference P i) (starOtherDifference P j) δ

end
end ConvexNivat
