import ConvexNivat.SpectralLaurentBridge

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

/-- Different directions give nonassociate factors, by their two-point supports. -/
theorem nonparallel_translation_binomials_not_associated (v v' : Lattice)
    (hvv' : Nonparallel v v') (ζ μ : ℂ) (hζ : ζ ≠ 0) (hμ : μ ≠ 0) :
    ¬ Associated (translationMonomial v - AddMonoidAlgebra.single 0 ζ)
      (translationMonomial v' - AddMonoidAlgebra.single 0 μ) := by
  classical
  have hD : (det v v' : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hvv'
  have hμ' : -μ ≠ 0 := neg_ne_zero.mpr hμ
  let a : Lattice → ℂ := fun z =>
    (det z v' : ℂ) / (det v v' : ℂ) * Complex.log ζ +
      (det v z : ℂ) / (det v v' : ℂ) * Complex.log (-μ)
  have ha (z w : Lattice) : a (z + w) = a z + a w := by
    simp only [a, det, Prod.fst_add, Prod.snd_add]
    push_cast
    ring
  have hself (z : Lattice) : det z z = 0 := by simp [det, mul_comm]
  have hav : a v = Complex.log ζ := by simp [a, hself, div_self hD]
  have hav' : a v' = Complex.log (-μ) := by simp [a, hself, div_self hD]
  have ha0 : a 0 = 0 := by simp [a, det]
  let d : ScalarField := fun z => Complex.exp (a z)
  have hd0 : d 0 = 1 := by simp [d, ha0]
  have hdv : d v = ζ := by simp [d, hav, Complex.exp_log hζ]
  have hdv' : d v' = -μ := by simp [d, hav', Complex.exp_log hμ']
  have heigen (z : Lattice) : d (z + v) = ζ * d z := by
    simp [d, ha, hav, Complex.exp_add, Complex.exp_log hζ, mul_comm]
  have hkill : applyLaurent
      (translationMonomial v - AddMonoidAlgebra.single 0 ζ) d = 0 := by
    funext z
    simp [applyLaurent_sub, translationMonomial, applyLaurent_single, heigen]
  intro h
  obtain ⟨g, hg⟩ := h.dvd
  have heq : applyLaurent
      (translationMonomial v' - AddMonoidAlgebra.single 0 μ) d = 0 := by
    rw [hg, mul_comm, applyLaurent_mul, hkill]
    funext z
    simp [applyLaurent]
  have hz := congrFun heq 0
  have hdiff : -μ - μ = 0 := by
    simpa [applyLaurent_sub, translationMonomial, applyLaurent_single, hd0, hdv'] using hz
  apply hμ
  linear_combination - (1 / 2 : ℂ) * hdiff

/-- Distinct roots in one primitive direction also give nonassociate factors. -/
theorem distinct_root_translation_binomials_not_associated (v : Lattice)
    (hv : Primitive v) (ζ μ : ℂ) (hζ : ζ ≠ 0) (hμ : μ ≠ 0) (hne : ζ ≠ μ) :
    ¬ Associated (translationMonomial v - AddMonoidAlgebra.single 0 ζ)
      (translationMonomial v - AddMonoidAlgebra.single 0 μ) := by
  have _ := hμ
  obtain ⟨u, hu⟩ := primitive_height_surjective v hv 1
  have hu' : det v u = 1 := hu
  let d : ScalarField := fun z => ζ ^ (det z u)
  have heigen (z : Lattice) : d (z + v) = ζ * d z := by
    dsimp [d]
    have hdet : det (z + v) u = det z u + 1 := by
      simp only [det, Prod.fst_add, Prod.snd_add] at hu' ⊢
      linear_combination hu'
    rw [hdet, zpow_add₀ hζ, zpow_one, mul_comm]
  have hkill : applyLaurent
      (translationMonomial v - AddMonoidAlgebra.single 0 ζ) d = 0 := by
    funext z
    simp [applyLaurent_sub, translationMonomial, applyLaurent_single, heigen]
  intro h
  obtain ⟨g, hg⟩ := h.dvd
  have heq : applyLaurent
      (translationMonomial v - AddMonoidAlgebra.single 0 μ) d = 0 := by
    rw [hg, mul_comm, applyLaurent_mul, hkill]
    funext z
    simp [applyLaurent]
  have hz := congrFun heq 0
  have hdiff : ζ - μ = 0 := by
    simpa [applyLaurent_sub, translationMonomial, applyLaurent_single,
      d, hu', show det (0 : Lattice) u = 0 by simp [det]] using hz
  exact hne (sub_eq_zero.mp hdiff)


end
end ConvexNivat
