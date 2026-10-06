import NivatTrial.WitnessTransform
import NivatTrial.Zonotope

/-! The witness-confinement step of Proposition 5.3.
The quotient-algebra spanning theorem is used through its actual projection.
The bridge proves that the entire relation ideal is annihilated and that a
functional vanishing on the projected spanning family vanishes everywhere.
-/

namespace NivatTrial.Confinement

open NivatTrial.Algebra NivatTrial.CoefficientField
open NivatTrial.WitnessTransform NivatTrial.BiRecursion NivatTrial.Quadratic
open scoped Classical Pointwise

noncomputable section

def monomialsIn (E : Set G) : Set R :=
  {f | ∃ d ∈ E, f = AddMonoidAlgebra.single d 1}

def projectedMonomials {Q : Type*} [AddCommGroup Q] [Module K Q]
    (q : R →ₗ[K] Q) (E : Set G) : Set Q :=
  {r | ∃ d ∈ E, r = q (AddMonoidAlgebra.single d 1)}

theorem image_monomials {Q : Type*} [AddCommGroup Q] [Module K Q]
    (q : R →ₗ[K] Q) (E : Set G) : q '' monomialsIn E = projectedMonomials q E := by
  ext r
  constructor
  · rintro ⟨f, ⟨d, hd, rfl⟩, hr⟩
    exact ⟨d, hd, hr.symm⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨AddMonoidAlgebra.single d 1, ⟨d, hd, rfl⟩, rfl⟩

theorem projectedMonomials_eq_image {Q : Type*} [AddCommGroup Q] [Module K Q]
    (q : R →ₗ[K] Q) (E : Set G) :
    projectedMonomials q E = (fun d : G => q (AddMonoidAlgebra.single d 1)) '' E := by
  ext r
  constructor
  · rintro ⟨d, hd, hr⟩
    exact ⟨d, hd, hr.symm⟩
  · rintro ⟨d, hd, hr⟩
    exact ⟨d, hd, hr.symm⟩

/-- The map-span argument performs the descent to the quotient without
postulating a quotient functional. -/
theorem functional_zero_of_projected_span
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (J : G → G →₀ ℂ) (P : Laurent) (q : R →ₗ[K] Q) (E : Set G)
    (hdisp : ∀ d z, displacementAction P (fun d z => J d z) d z = 0)
    (hdiag : ∀ d z, diagonalAction P (fun d z => J d z) d z = 0)
    (hker : ∀ f : R, q f = 0 → f ∈ Ideal.span {includeCoefficients P, diagonalCoefficients P})
    (hspan : Submodule.span K (projectedMonomials q E) = ⊤)
    (hvanish : ∀ d ∈ E, J d = 0) : functional J = 0 := by
  let U := Submodule.span K (monomialsIn E)
  have hU : U ≤ (functional J).ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨d, hd, rfl⟩
    change functional J (AddMonoidAlgebra.single d 1) = 0
    rw [functional_single, one_mul, hvanish d hd]
    exact map_zero transform
  have hkerL : q.ker ≤ (functional J).ker := by
    intro f hf
    exact functional_ideal_zero J P hdisp hdiag f (hker f hf)
  have hmap : Submodule.map q U = ⊤ := by
    change Submodule.map q (Submodule.span K (monomialsIn E)) = ⊤
    rw [Submodule.map_span, image_monomials, hspan]
  have htop : (⊤ : Submodule K R) ≤ (functional J).ker := by
    have hsup := sup_le hU hkerL
    rw [← Submodule.comap_map_eq, hmap, Submodule.comap_top] at hsup
    exact hsup
  ext f
  exact htop (Submodule.mem_top)

theorem finsupp_witness_confined
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (J : G → G →₀ ℂ) (P : Laurent) (q : R →ₗ[K] Q) (E : Set G)
    (hdisp : ∀ d z, displacementAction P (fun d z => J d z) d z = 0)
    (hdiag : ∀ d z, diagonalAction P (fun d z => J d z) d z = 0)
    (hker : ∀ f : R, q f = 0 → f ∈ Ideal.span {includeCoefficients P, diagonalCoefficients P})
    (hspan : Submodule.span K (projectedMonomials q E) = ⊤)
    (hsome : ∃ d, J d ≠ 0) : ∃ d ∈ E, J d ≠ 0 := by
  by_contra h
  have hvanish : ∀ d ∈ E, J d = 0 := by
    simpa only [not_exists, not_and, not_not] using h
  have hzero := functional_zero_of_projected_span J P q E hdisp hdiag hker hspan hvanish
  obtain ⟨d, hd⟩ := hsome
  have hz := LinearMap.congr_fun hzero (AddMonoidAlgebra.single d 1)
  simp only [functional_single, one_mul, LinearMap.zero_apply] at hz
  exact transform_ne_zero hd hz

def finiteFamily (J : G → G → ℂ) (hfinite : ∀ d, (Function.support (J d)).Finite) :
    G → G →₀ ℂ := fun d => Finsupp.ofSupportFinite (J d) (hfinite d)

@[simp] theorem finiteFamily_apply (J : G → G → ℂ)
    (hfinite : ∀ d, (Function.support (J d)).Finite) (d z : G) :
    finiteFamily J hfinite d z = J d z := rfl

theorem finiteFamily_ne_zero (J : G → G → ℂ)
    (hfinite : ∀ d, (Function.support (J d)).Finite) {d : G} (hd : J d ≠ 0) :
    finiteFamily J hfinite d ≠ 0 := by
  intro h
  apply hd
  funext z
  have hz := congrArg (fun f : G →₀ ℂ => f z) h
  simpa using hz

/-- Proposition 5.3 for actual functions with finite support in the observation
variable. The supports are allowed to vary with the displacement. -/
theorem witness_confined
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (J : G → G → ℂ) (P : Laurent) (q : R →ₗ[K] Q) (E : Set G)
    (hfinite : ∀ d, (Function.support (J d)).Finite)
    (hdisp : ∀ d z, displacementAction P J d z = 0)
    (hdiag : ∀ d z, diagonalAction P J d z = 0)
    (hker : ∀ f : R, q f = 0 → f ∈ Ideal.span {includeCoefficients P, diagonalCoefficients P})
    (hspan : Submodule.span K (projectedMonomials q E) = ⊤)
    (hsome : ∃ d, J d ≠ 0) : ∃ d ∈ E, J d ≠ 0 := by
  have hsome' : ∃ d, finiteFamily J hfinite d ≠ 0 := by
    obtain ⟨d, hd⟩ := hsome
    exact ⟨d, finiteFamily_ne_zero J hfinite hd⟩
  obtain ⟨d, hd, hJ⟩ := finsupp_witness_confined (finiteFamily J hfinite) P q E
    (by simpa only [finiteFamily_apply] using hdisp)
    (by simpa only [finiteFamily_apply] using hdiag) hker hspan hsome'
  refine ⟨d, hd, ?_⟩
  intro hzero
  apply hJ
  ext z
  simp [hzero]

theorem nonzero_witness_confined
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (J : G → G → ℂ) (P : Laurent) (q : R →ₗ[K] Q) (E : Set G)
    (hfinite : ∀ d, (Function.support (J d)).Finite)
    (hdisp : ∀ d z, displacementAction P J d z = 0)
    (hdiag : ∀ d z, diagonalAction P J d z = 0)
    (hker : ∀ f : R, q f = 0 → f ∈ Ideal.span {includeCoefficients P, diagonalCoefficients P})
    (hspan : Submodule.span K (projectedMonomials q E) = ⊤)
    (hsome : ∃ d, J d ≠ 0) (hzero : J 0 = 0) : ∃ d ∈ E, d ≠ 0 ∧ J d ≠ 0 := by
  obtain ⟨d, hd, hJ⟩ := witness_confined J P q E hfinite hdisp hdiag hker hspan hsome
  refine ⟨d, hd, ?_, hJ⟩
  intro heq
  exact hJ (heq ▸ hzero)

/-- The actual quadratic witness from §5.1; neither recurrence is assumed to
hold for an unrelated family. -/
theorem biRecursion_witness_confined
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (P D : Laurent) (η : G → ℂ) (q : R →ₗ[K] Q) (E : Set G)
    (hfinite : ∀ d, (Function.support (witness D η d)).Finite)
    (hrec : (∀ d z, displacementAction P (witness D η) d z = 0) ∧
      (∀ d z, diagonalAction P (witness D η) d z = 0))
    (hker : ∀ f : R, q f = 0 → f ∈ Ideal.span {includeCoefficients P, diagonalCoefficients P})
    (hspan : Submodule.span K (projectedMonomials q E) = ⊤)
    (hsome : ∃ d, act D (twoPoint η 0 d) ≠ 0) :
    ∃ d ∈ E, act D (twoPoint η 0 d) ≠ 0 :=
  witness_confined (witness D η) P q E hfinite hrec.1 hrec.2 hker hspan hsome

theorem biRecursion_nonzero_witness_confined
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (P D : Laurent) (η : G → ℂ) (q : R →ₗ[K] Q) (E : Set G)
    (hfinite : ∀ d, (Function.support (witness D η d)).Finite)
    (hrec : (∀ d z, displacementAction P (witness D η) d z = 0) ∧
      (∀ d z, diagonalAction P (witness D η) d z = 0))
    (hker : ∀ f : R, q f = 0 → f ∈ Ideal.span {includeCoefficients P, diagonalCoefficients P})
    (hspan : Submodule.span K (projectedMonomials q E) = ⊤)
    (hsome : ∃ d, act D (twoPoint η 0 d) ≠ 0)
    (hsquare : act D (fun z => η z * η z) = 0) :
    ∃ d ∈ E, d ≠ 0 ∧ act D (twoPoint η 0 d) ≠ 0 := by
  apply nonzero_witness_confined (witness D η) P q E hfinite hrec.1 hrec.2 hker hspan hsome
  funext z
  change act D (twoPoint η 0 0) z = 0
  have hpair : twoPoint η 0 0 = fun x => η x * η x := by
    funext x
    simp [twoPoint]
  rw [hpair]
  exact congrFun hsquare z

end

end NivatTrial.Confinement
