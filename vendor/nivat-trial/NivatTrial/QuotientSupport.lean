import NivatTrial.QuotientIdeals
import NivatTrial.Zonotope
import Mathlib.Algebra.MonoidAlgebra.Support

/-! Support estimates for the projectors in the Laurent quotient argument. -/

namespace NivatTrial.QuotientSupport

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.CoefficientField
open NivatTrial.QuotientFactors NivatTrial.QuotientIdeals NivatTrial.Zonotope
open scoped BigOperators Pointwise
open scoped Classical

noncomputable section

theorem aeval_single_eq_sum (p : Polynomial K) (v : G) (a : K) :
    Polynomial.aeval (AddMonoidAlgebra.single v a) p =
      ∑ n ∈ p.support, AddMonoidAlgebra.single (n • v) (p.coeff n * a ^ n) := by
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum,
    AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]

theorem aeval_single_support (p : Polynomial K) (v : G) (a : K) {z : G}
    (hz : z ∈ (Polynomial.aeval (AddMonoidAlgebra.single v a) p).coeff.support) :
    ∃ n : ℕ, n ≤ p.natDegree ∧ z = n • v := by
  classical
  rw [aeval_single_eq_sum] at hz
  have hz' : (∑ n ∈ p.support,
      (AddMonoidAlgebra.single (n • v) (p.coeff n * a ^ n) : R).coeff z) ≠ 0 := by
    simpa using Finsupp.mem_support_iff.mp hz
  obtain ⟨n, hn, hnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz'
  refine ⟨n, Polynomial.le_natDegree_of_mem_supp n hn, ?_⟩
  by_contra hne
  apply hnonzero
  exact Finsupp.single_eq_of_ne hne

theorem wCharacter_val (v : G) :
    (wCharacter (.ofAdd v) : R) = AddMonoidAlgebra.single (-v) (xUnit v : K) := by
  change algebraMap K R (xUnit v : K) * (↑((yUnit v)⁻¹) : R) = _
  have hy : (↑((yUnit v)⁻¹) : R) = AddMonoidAlgebra.single (-v) 1 := rfl
  rw [hy]
  simp [AddMonoidAlgebra.single_mul_single]

theorem aFactor_support (v : G) (S : Finset ℂˣ) {z : G}
    (hz : z ∈ (aFactor v S).coeff.support) :
    ∃ n : ℕ, n ≤ S.card ∧ z = n • v := by
  simpa only [rootPolynomial_natDegree] using
    aeval_single_support (rootPolynomial S) v 1 hz

theorem cFactor_support (v : G) (S : Finset ℂˣ) {z : G}
    (hz : z ∈ (cFactor v S).coeff.support) :
    ∃ n : ℕ, n ≤ S.card ∧ z = n • (-v) := by
  rw [cFactor, wCharacter_val] at hz
  simpa only [rootPolynomial_natDegree] using
    aeval_single_support (rootPolynomial S) (-v) (xUnit v : K) hz

variable {ι : Type*} [Fintype ι]

/-- A coefficient box records the individual directional bounds before taking
the linear image in the real plane. -/
def coefficientBox (v : ι → G) (l u : ι → ℝ) : Set G :=
  {z | ∃ t : ι → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ u i) ∧
    coeffPoint v t = embed z}

theorem coefficientBox_add (v : ι → G) (l u l' u' : ι → ℝ)
    {x y : G} (hx : x ∈ coefficientBox v l u) (hy : y ∈ coefficientBox v l' u') :
    x + y ∈ coefficientBox v (fun i => l i + l' i) (fun i => u i + u' i) := by
  obtain ⟨t, ht, htx⟩ := hx
  obtain ⟨s, hs, hsy⟩ := hy
  refine ⟨fun i => t i + s i, fun i =>
    ⟨add_le_add (ht i).1 (hs i).1, add_le_add (ht i).2 (hs i).2⟩, ?_⟩
  rw [coeffPoint_add, htx, hsy, embed_add]

theorem support_mul_box (v : ι → G) (f g : R) (l u l' u' : ι → ℝ)
    (hf : ∀ z ∈ f.coeff.support, z ∈ coefficientBox v l u)
    (hg : ∀ z ∈ g.coeff.support, z ∈ coefficientBox v l' u') :
    ∀ z ∈ (f * g).coeff.support,
      z ∈ coefficientBox v (fun i => l i + l' i) (fun i => u i + u' i) := by
  classical
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset f g hz)
  exact coefficientBox_add v l u l' u' (hf x hx) (hg y hy)

theorem support_prod_directional (v : ι → G) (f : ι → R) (d : ι → ℕ)
    (hf : ∀ i z, z ∈ (f i).coeff.support → ∃ n : ℕ, n ≤ d i ∧ z = n • v i)
    (s : Finset ι) :
    ∀ z ∈ (∏ i ∈ s, f i).coeff.support,
      z ∈ coefficientBox v (fun _ => 0) (fun i => if i ∈ s then (d i : ℝ) else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    exact ⟨fun _ => 0, fun _ => ⟨le_rfl, le_rfl⟩, by simp [coeffPoint]⟩
  | @insert k s hks ih =>
    intro z hz
    rw [Finset.prod_insert hks] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset (f k) (∏ i ∈ s, f i) hz)
    obtain ⟨n, hn, rfl⟩ := hf k x hx
    obtain ⟨t, ht, hty⟩ := ih y hy
    refine ⟨fun i => (if i = k then (n : ℝ) else 0) + t i, ?_, ?_⟩
    · intro i
      by_cases hik : i = k
      · subst i
        have htk : t k = 0 := le_antisymm (by simpa [hks] using (ht k).2) (ht k).1
        simp only [ite_true, htk, add_zero, Finset.mem_insert_self]
        exact ⟨Nat.cast_nonneg _, by exact_mod_cast hn⟩
      · simpa [hik, Finset.mem_insert, hik] using ht i
    · rw [coeffPoint_add, hty, embed_add, embed_nsmul]
      congr 1
      simp [coeffPoint]

end

end NivatTrial.QuotientSupport
