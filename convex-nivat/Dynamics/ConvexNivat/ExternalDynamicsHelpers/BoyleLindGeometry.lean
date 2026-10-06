import ConvexNivat.ExternalDynamicsHelpers.BoyleLindDefinitions

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

theorem planeNorm_sq (x : RealPlane) : planeNorm x ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  simpa [planeNorm, euclideanCoordinates, Fin.sum_univ_two] using
    EuclideanSpace.real_norm_sq_eq (euclideanCoordinates x)

theorem unitNormals_compact : IsCompact unitNormals := by
  have heq : unitNormals = {n : RealPlane | n.1 ^ 2 + n.2 ^ 2 = 1} := by
    ext n
    change planeNorm n = 1 ↔ n.1 ^ 2 + n.2 ^ 2 = 1
    have hnonneg : 0 ≤ planeNorm n := norm_nonneg _
    have hs := planeNorm_sq n
    constructor <;> intro h <;> nlinarith
  rw [heq]
  apply (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).prod
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)) |>.of_isClosed_subset
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro n hn
    have h1 := sq_nonneg n.1
    have h2 := sq_nonneg n.2
    change n.1 ^ 2 + n.2 ^ 2 = 1 at hn
    change (-1 ≤ n.1 ∧ n.1 ≤ 1) ∧ (-1 ≤ n.2 ∧ n.2 ≤ 1)
    constructor <;> constructor <;> nlinarith

theorem unit_normal_ne_zero (n : RealPlane) (hn : n ∈ unitNormals) : n ≠ 0 := by
  intro hzero
  subst n
  change planeNorm (0 : RealPlane) = 1 at hn
  have hs := planeNorm_sq (0 : RealPlane)
  simp only [Prod.fst_zero, Prod.snd_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hs
  nlinarith

/-- The nearest lattice point used for the real translations in Lemma 3.2. -/
theorem real_center_near_lattice (a : RealPlane) :
    ∃ z : Lattice, planeNorm (a - embed z) < 2 := by
  refine ⟨(⌊a.1⌋, ⌊a.2⌋), ?_⟩
  have hx0 := Int.floor_le a.1
  have hx1 := Int.lt_floor_add_one a.1
  have hy0 := Int.floor_le a.2
  have hy1 := Int.lt_floor_add_one a.2
  have hx : 0 ≤ a.1 - (⌊a.1⌋ : ℝ) := by linarith
  have hxl : a.1 - (⌊a.1⌋ : ℝ) < 1 := by linarith
  have hy : 0 ≤ a.2 - (⌊a.2⌋ : ℝ) := by linarith
  have hyl : a.2 - (⌊a.2⌋ : ℝ) < 1 := by linarith
  have hxs : (a.1 - (⌊a.1⌋ : ℝ)) ^ 2 < 1 := by nlinarith
  have hys : (a.2 - (⌊a.2⌋ : ℝ)) ^ 2 < 1 := by nlinarith
  have hs := planeNorm_sq (a - embed (⌊a.1⌋, ⌊a.2⌋))
  change planeNorm (a - embed (⌊a.1⌋, ⌊a.2⌋)) ^ 2 =
    (a.1 - (⌊a.1⌋ : ℝ)) ^ 2 + (a.2 - (⌊a.2⌋ : ℝ)) ^ 2 at hs
  have hp : 0 ≤ planeNorm (a - embed (⌊a.1⌋, ⌊a.2⌋)) := norm_nonneg _
  nlinarith

end
end ConvexNivat.ExternalDynamicsHelpers
