import ConvexNivat.ExternalDynamicsHelpers.BoyleLindCompact
import ConvexNivat.ExternalDynamicsHelpers.BoyleLindBallConsequences
import ConvexNivat.ExternalDynamicsHelpers.BoyleLindCoding
import ConvexNivat.ExternalDynamicsHelpers.BoyleLindGeometry

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

private theorem lemma32_dot_sub (x y n : RealPlane) :
    realDot (x-y) n=realDot x n-realDot y n := by dsimp [realDot]; ring

private theorem lemma32_norm_add (x y : RealPlane) : planeNorm (x+y) ≤ planeNorm x+planeNorm y := by
  have he : euclideanCoordinates (x+y)=euclideanCoordinates x+euclideanCoordinates y := by
    ext i
    fin_cases i <;> rfl
  unfold planeNorm
  rw [he]
  exact norm_add_le _ _

private theorem lemma32_orthogonal_sq (n x : RealPlane) (hn : n ∈ unitNormals) :
    planeNorm x^2=(realDot x n)^2+(realDot x (realQuarterTurn n))^2 := by
  have hn2 : n.1^2+n.2^2=1 := by
    have hs := planeNorm_sq n
    change planeNorm n=1 at hn
    nlinarith
  rw [planeNorm_sq]
  dsimp [realDot,realQuarterTurn]
  nlinarith [congrArg (fun v : ℝ => (x.1^2+x.2^2)*v) hn2]

private theorem lemma32_dot_bounds (n x : RealPlane) (hn : n ∈ unitNormals) :
    |realDot x n| ≤ planeNorm x ∧ |realDot x (realQuarterTurn n)| ≤ planeNorm x := by
  have hs := lemma32_orthogonal_sq n x hn
  have hp : 0 ≤ planeNorm x := norm_nonneg _
  constructor <;> rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg (realDot x n),sq_nonneg (realDot x (realQuarterTurn n))]

/-- Published Lemma 3.2, including all real translation centres. -/
theorem boyleLind_lemma3_2 (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (n : RealPlane) (hn : n ∈ unitNormals) (hexp : ¬ NonexpansiveLine ξ n) :
    ∃ t : ℝ, 0 < t ∧ ∀ s : ℝ, 0 < s → ∃ r : ℝ,
      0 < r ∧ RealCodes ξ (lineBox n r t) (lineBox n 0 s) := by
  classical
  obtain ⟨u,hu,hdet⟩ := expansive_line_determining_band ξ n (unit_normal_ne_zero n hn) hexp
  refine ⟨u+2,by positivity,?_⟩
  intro s hs
  let D := (lattice_in_real_ball_finite (s+2)).toFinset
  obtain ⟨B,hB,hcode⟩ := band_finite_window_code ξ A hA n hn u hu hdet D
  let r := (∑ z ∈ B, |realDot (embed z) (realQuarterTurn n)|)+3
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r,hr,?_⟩
  intro a x hx y hy hag z hz
  obtain ⟨k,hk⟩ := real_center_near_lattice a
  have hdelta := lemma32_dot_bounds n (a-embed k) hn
  have hkn : |realDot (a-embed k) n| < 2 := hdelta.1.trans_lt hk
  have hkt : |realDot (a-embed k) (realQuarterTurn n)| < 2 := hdelta.2.trans_lt hk
  have htranslate : AgreesOn (translate k x) (translate k y) (B : Set Lattice) := by
    intro w hw
    change x (w+k)=y (w+k)
    apply hag (w+k)
    have he : embed (w+k)-a=embed w-(a-embed k) := by
      ext <;> simp [embed] <;> ring
    change |realDot (embed (w+k)-a) (realQuarterTurn n)| ≤ r ∧
      |realDot (embed (w+k)-a) n| ≤ u+2
    rw [he]
    constructor
    · rw [lemma32_dot_sub]
      have hb : |realDot (embed w) (realQuarterTurn n)| ≤
          ∑ z ∈ B, |realDot (embed z) (realQuarterTurn n)| :=
        Finset.single_le_sum (fun z _ => abs_nonneg (realDot (embed z) (realQuarterTurn n))) hw
      have htri := abs_sub (realDot (embed w) (realQuarterTurn n))
        (realDot (a-embed k) (realQuarterTurn n))
      dsimp [r]
      linarith
    · rw [lemma32_dot_sub]
      have hb : |realDot (embed w) n| ≤ u := hB hw
      exact (abs_sub _ _).trans (add_le_add hb hkn.le)
  have hc := hcode (translate k x) (orbitClosure_translate_member ξ x hx k)
    (translate k y) (orbitClosure_translate_member ξ y hy k) htranslate
  have hzD : z-k ∈ D := by
    change |realDot (embed z-a) (realQuarterTurn n)| ≤ 0 ∧
      |realDot (embed z-a) n| ≤ s at hz
    have hzt := abs_nonpos_iff.mp hz.1
    have hzs : planeNorm (embed z-a) ≤ s := by
      have he := lemma32_orthogonal_sq n (embed z-a) hn
      rw [hzt] at he
      have hsq := (sq_le_sq₀ (abs_nonneg _) hs.le).mpr hz.2
      rw [sq_abs] at hsq
      nlinarith [norm_nonneg (euclideanCoordinates (embed z-a))]
    have he : embed (z-k)=(embed z-a)+(a-embed k) := by
      ext <;> simp [embed] <;> ring
    have hb : planeNorm (embed (z-k)) ≤ s+2 := by
      rw [he]
      exact (lemma32_norm_add _ _).trans (add_le_add hzs hk.le)
    simpa [D,realBall] using hb
  have he := hc (z-k) hzD
  simpa [translate] using he

end
end ConvexNivat.ExternalDynamicsHelpers
