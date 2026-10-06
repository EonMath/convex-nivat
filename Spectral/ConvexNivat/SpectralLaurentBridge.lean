import ConvexNivat.OperatorAction
import ConvexNivat.CoreLattice
import ConvexNivat.SpectralFourier
import ConvexNivat.OneSidedRecurrence

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

/-- The Laurent polynomial whose action is the projection Pζ in Lemma 2.0. -/
def spectralProjectionPolynomial (v : Lattice) (κ : ℕ) (ζ : ℂ) :
    LaurentPolynomial :=
  ∑ k ∈ Finset.range κ, AddMonoidAlgebra.single ((k : ℤ) • v)
    ((κ : ℂ)⁻¹ * ζ ^ (-(k : ℤ)))

/-- Lemma 2.0(3): the defined projection is an actual Laurent-polynomial action. -/
theorem spectral_projection_polynomial_action (v : Lattice) (κ : ℕ) (ζ : ℂ)
    (d : ScalarField) :
    applyLaurent (spectralProjectionPolynomial v κ ζ) d =
      spectralProjection v κ ζ d := by
  classical
  let A : LaurentPolynomial →+ ScalarField :=
    { toFun := fun p => applyLaurent p d
      map_zero' := applyLaurent_zero d
      map_add' := fun p q => applyLaurent_add p q d }
  change A (∑ k ∈ Finset.range κ, _) = _
  rw [map_sum]
  funext z
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range κ, applyLaurent
    (AddMonoidAlgebra.single ((k : ℤ) • v) ((κ : ℂ)⁻¹ * ζ ^ (-(k : ℤ)))) d z) = _
  simp only [applyLaurent_single, spectralProjection, mul_assoc, Finset.mul_sum]

/-- Lemma 2.0(3): commutation with every Laurent action. -/
theorem spectral_projection_commutes_laurent (v : Lattice) (κ : ℕ) (ζ : ℂ)
    (d : ScalarField) (f : LaurentPolynomial) :
    spectralProjection v κ ζ (applyLaurent f d) =
      applyLaurent f (spectralProjection v κ ζ d) := by
  rw [← spectral_projection_polynomial_action, ← spectral_projection_polynomial_action]
  exact applyLaurent_commute _ _ _

/-- Lemma 2.0(4), with the integral basis coefficients read directly from f. -/
theorem spectral_laurent_row_formula (v u : Lattice) (hbasis : det v u = 1)
    (κ : ℕ) (hκ : 0 < κ) (ζ : ℂ) (hζ : ζ ^ κ = 1)
    (d : ScalarField) (hd : HasPeriod d ((κ : ℤ) • v))
    (f : LaurentPolynomial) (s t : ℤ) :
    applyLaurent f (spectralProjection v κ ζ d) (s • v + t • u) =
      ζ ^ s * ∑ q ∈ f.coeff.support,
        f.coeff q * ζ ^ (det q u) *
          spectralRowCoefficient v u κ ζ d (t + det v q) := by
  classical
  have hζ0 : ζ ≠ 0 := by
    intro hz
    simp [hz, Nat.ne_of_gt hκ] at hζ
  have hb (q : Lattice) : q = (det q u) • v + (det v q) • u := by
    ext <;> simp [det] at hbasis ⊢
    · linear_combination -q.1 * hbasis
    · linear_combination -q.2 * hbasis
  change (∑ q ∈ f.coeff.support, f.coeff q *
    spectralProjection v κ ζ d (s • v + t • u + q)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : s • v + t • u + q =
      (s + det q u) • v + (t + det v q) • u := by
    conv_lhs => rhs; rw [hb q]
    simp only [add_smul]
    abel
  rw [hq', spectral_projection_row_formula v u κ hκ ζ hζ d hd,
    zpow_add₀ hζ0]
  ring


end
end ConvexNivat
