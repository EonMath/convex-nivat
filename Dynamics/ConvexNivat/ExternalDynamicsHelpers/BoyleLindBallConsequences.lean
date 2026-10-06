import ConvexNivat.ExternalDynamicsHelpers.BoyleLindDefinitions

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

theorem large_ball_growth_iterates (ξ : Configuration ℤ) (R₀ : ℝ)
    (hcode : ∀ R : ℝ, R₀ ≤ R → RealCodes ξ (realBall R) (realBall (R + 1 / 2))) :
    ∀ j : ℕ, RealCodes ξ (realBall R₀) (realBall (R₀ + (j : ℝ) / 2)) := by
  intro j
  induction j with
  | zero => simpa using (show RealCodes ξ (realBall R₀) (realBall R₀) from
      fun _ _ _ _ _ h => h)
  | succ j ih =>
    have hj : R₀ ≤ R₀ + (j : ℝ) / 2 := le_add_of_nonneg_right (by positivity)
    intro a x hx y hy hag
    have hp := hcode (R₀ + (j : ℝ) / 2) hj a x hx y hy (ih a x hx y hy hag)
    have he : R₀ + ((j + 1 : ℕ) : ℝ) / 2 = (R₀ + (j : ℝ) / 2) + 1 / 2 := by
      push_cast
      ring
    rw [he]
    exact hp

/-- The final iteration step of Theorem 3.6. -/
theorem large_ball_codes_entire_plane (ξ : Configuration ℤ) (R₀ : ℝ)
    (hcode : ∀ R : ℝ, R₀ ≤ R → RealCodes ξ (realBall R) (realBall (R + 1 / 2))) :
    RealCodes ξ (realBall R₀) Set.univ := by
  intro a x hx y hy hag z hz
  obtain ⟨j,hj⟩ := exists_nat_gt (2 * (planeNorm (embed z - a) - R₀))
  apply large_ball_growth_iterates ξ R₀ hcode j a x hx y hy hag z
  change planeNorm (embed z - a) ≤ R₀ + (j : ℝ) / 2
  linarith

private theorem construction_planeNorm_sq (x : RealPlane) :
    planeNorm x ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  simp [planeNorm, euclideanCoordinates, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem lattice_in_real_ball_finite (R : ℝ) : (embed ⁻¹' realBall R).Finite := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt R
  apply ((Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N)).finite_toSet.subset
  intro z hz
  have hp : planeNorm (embed z) ≤ R := hz
  have hn : 0 ≤ planeNorm (embed z) := norm_nonneg _
  have hs := construction_planeNorm_sq (embed z)
  change planeNorm (embed z) ^ 2 = (z.1 : ℝ)^2 + (z.2 : ℝ)^2 at hs
  have h1 : -(N : ℝ) ≤ z.1 ∧ (z.1 : ℝ) ≤ N := by
    constructor <;> nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  have h2 : -(N : ℝ) ≤ z.2 ∧ (z.2 : ℝ) ≤ N := by
    constructor <;> nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    exact_mod_cast h1
  · apply Finset.mem_Icc.mpr
    exact_mod_cast h2

/-- A finite ball coding everything makes the actual finite-alphabet subshift finite. -/
theorem finite_ball_code_orbit_finite (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (R : ℝ)
    (hcode : RealCodes ξ (realBall R) Set.univ) :
    (OrbitClosure ξ).Finite := by
  classical
  let B := (lattice_in_real_ball_finite R).toFinset
  let f : OrbitClosure ξ → (B → A) :=
    fun x z => ⟨x.val z.val, orbitClosure_alphabet ξ x.val A hA x.property z.val⟩
  have hf : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    funext z
    apply hcode 0 x.val x.property y.val y.property ?_ z (by trivial)
    intro w hw
    have hw' : w ∈ B := by
      simpa [B, realTranslate] using hw
    exact congrArg Subtype.val (congrFun heq ⟨w, hw'⟩)
  let := Finite.of_injective f hf
  exact Set.toFinite _

end
end ConvexNivat.ExternalDynamicsHelpers
