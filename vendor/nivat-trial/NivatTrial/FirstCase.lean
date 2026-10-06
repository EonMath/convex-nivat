import NivatTrial.Algebra
import NivatTrial.Patterns

/-! The first-case complexity argument of Proposition 1.3.

The finite-support conclusion of Lemma 1.1 is an explicit hypothesis here.
The remaining dimension and integral-domain arguments are proved in full.
-/

namespace NivatTrial

open NivatTrial.Algebra

noncomputable section

/-- Package coefficients on a window into a Laurent polynomial. -/
def windowPolynomial (S : Finset Lattice) (c : S → ℂ) : Laurent :=
  ∑ s : S, AddMonoidAlgebra.single (s : Lattice) (c s)

@[simp] theorem windowPolynomial_coeff (S : Finset Lattice) (c : S → ℂ) (s : S) :
    (windowPolynomial S c).coeff (s : Lattice) = c s := by
  classical
  simp [windowPolynomial, Finsupp.single_apply]

theorem windowPolynomial_ne_zero (S : Finset Lattice) {c : S → ℂ} (hc : c ≠ 0) :
    windowPolynomial S c ≠ 0 := by
  intro h
  apply hc
  funext s
  have hs := congrArg (fun f : Laurent => f.coeff (s : Lattice)) h
  simpa using hs

theorem act_windowPolynomial (S : Finset Lattice) (c : S → ℂ)
    (J : Lattice → ℂ) (z : Lattice) :
    act (windowPolynomial S c) J z = ∑ s : S, c s * J (z + s) := by
  classical
  simp [windowPolynomial, act_sum, act_single]

/-- A local observation with a nonzero, finitely supported difference forces
more patterns than sites in every finite window. -/
theorem complexity_lower_bound_of_finite_difference {A : Type*} [Fintype A]
    (θ : Lattice → A) (w : A → ℂ) (D : Laurent)
    (hconstant : ∀ b : ℂ, act D (fun _ => b) = 0)
    (hfinite : (Function.support (act D (fun z => w (θ z)))).Finite)
    (hnonzero : act D (fun z => w (θ z)) ≠ 0) (S : Finset Lattice) :
    S.card + 1 ≤ patternComplexity θ S := by
  classical
  by_contra h
  have hlow : patternComplexity θ S ≤ S.card := by omega
  obtain ⟨c, hc, b, hrelation⟩ := exists_affine_pattern_relation θ S w hlow
  let q := windowPolynomial S c
  have hq : q ≠ 0 := windowPolynomial_ne_zero S hc
  have hrel : act q (fun z => w (θ z)) = fun _ => b := by
    funext z
    simpa [q, act_windowPolynomial] using hrelation z
  have hzero : act q (act D (fun z => w (θ z))) = 0 := by
    rw [act_comm, hrel, hconstant]
  exact lemma1_2 hq hnonzero hfinite hzero

/-- The indicator version used in Proposition 1.3. The finite-support premise
is the output of Lemma 1.1, not a formalization of that lemma. -/
theorem indicator_complexity_lower_bound {A : Type*} [Fintype A] [DecidableEq A]
    (θ : Lattice → A) (a : A) (D : Laurent)
    (hconstant : ∀ b : ℂ, act D (fun _ => b) = 0)
    (hfinite : (Function.support
      (act D (fun z => if θ z = a then (1 : ℂ) else 0))).Finite)
    (hnonzero : act D (fun z => if θ z = a then (1 : ℂ) else 0) ≠ 0)
    (S : Finset Lattice) : S.card + 1 ≤ patternComplexity θ S := by
  exact complexity_lower_bound_of_finite_difference θ
    (fun x => if x = a then 1 else 0) D hconstant hfinite hnonzero S

end

end NivatTrial
