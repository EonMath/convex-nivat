import ConvexNivat.ExceptionalPolynomialDefinitions
import ConvexNivat.OperatorAction

open scoped BigOperators
namespace ConvexNivat
noncomputable section

private lemma action_zero_field (f : LaurentPolynomial) : applyLaurent f 0 = 0 := by
  funext z
  simp [applyLaurent]

private lemma action_sum_field {ι : Type*} (s : Finset ι)
    (f : LaurentPolynomial) (d : ι → ScalarField) :
    applyLaurent f (∑ i ∈ s, d i) = ∑ i ∈ s, applyLaurent f (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [action_zero_field]
  | @insert i s hi h => simp [hi, applyLaurent_add_field, h]

lemma exceptional_product_annihilates (v : Lattice) (κ : ℕ) (hκ : 0 < κ)
    (d : ScalarField) (hd : HasPeriod d ((κ : ℤ) • v)) (s : Finset ℂ)
    (hs : ∀ ζ ∈ rootSpectrum κ, spectralOccurs v κ ζ d → ζ ∈ s) :
    applyLaurent (∏ ζ ∈ s, (translationMonomial v - AddMonoidAlgebra.single 0 ζ)) d = 0 := by
  classical
  rw [← spectral_projection_complete v κ hκ d hd, action_sum_field]
  apply Finset.sum_eq_zero
  intro ζ hζ
  by_cases hocc : spectralOccurs v κ ζ d
  · have hm := hs ζ hζ hocc
    have hroot : ζ ^ κ = 1 := (Polynomial.mem_nthRootsFinset hκ 1).mp hζ
    have hkill : applyLaurent (translationMonomial v - AddMonoidAlgebra.single 0 ζ)
        (spectralProjection v κ ζ d) = 0 := by
      rw [applyLaurent_sub]
      funext z
      have he := congrFun (spectral_projection_eigen v κ hκ ζ hroot d hd) z
      simp only [translationMonomial, Pi.sub_apply, applyLaurent_single,
        one_mul, add_zero]
      exact sub_eq_zero.mpr he
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem
      (fun μ => translationMonomial v - AddMonoidAlgebra.single 0 μ) hm
    rw [hq, mul_comm, applyLaurent_mul, hkill, action_zero_field]
  · have hz : spectralProjection v κ ζ d = 0 := not_ne_iff.mp hocc
    rw [hz, action_zero_field]

end
end ConvexNivat
