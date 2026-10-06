import ConvexNivat.ExternalDynamicsHelpers.BoyleLindDefinitions

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

private theorem rotation_unit_sq (n : RealPlane) (hn : n ∈ unitNormals) :
    n.1^2+n.2^2=1 := by
  have hs : planeNorm n^2=n.1^2+n.2^2 := by
    simpa [planeNorm,euclideanCoordinates,Fin.sum_univ_two] using
      EuclideanSpace.real_norm_sq_eq (euclideanCoordinates n)
  change planeNorm n=1 at hn
  nlinarith

private theorem rotation_dot_formula (n x w : RealPlane) (hn : n ∈ unitNormals) :
    realDot x w = realDot x n * realDot n w +
      realDot x (realQuarterTurn n) * realDot (realQuarterTurn n) w := by
  have hs := rotation_unit_sq n hn
  dsimp [realDot,realQuarterTurn]
  nlinarith [congrArg (fun v : ℝ => (x.1*w.1+x.2*w.2)*v) hs]

private theorem rotation_tan_formula (n x w : RealPlane) (hn : n ∈ unitNormals) :
    realDot x (realQuarterTurn w) = realDot x (realQuarterTurn n) * realDot n w -
      realDot x n * realDot (realQuarterTurn n) w := by
  have hs := rotation_unit_sq n hn
  dsimp [realDot,realQuarterTurn]
  nlinarith [congrArg (fun v : ℝ => (-x.1*w.2+x.2*w.1)*v) hs]

private theorem rotation_dot_le_one (n w : RealPlane)
    (hn : n ∈ unitNormals) (hw : w ∈ unitNormals) : |realDot n w| ≤ 1 := by
  have hn2 := rotation_unit_sq n hn
  have hw2 := rotation_unit_sq w hw
  have hid : (realDot n w)^2 + (realDot (realQuarterTurn n) w)^2 = 1 := by
    dsimp [realDot,realQuarterTurn]
    nlinarith [congrArg (fun v : ℝ => (n.1^2+n.2^2)*v) hw2]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (realDot (realQuarterTurn n) w)]

/-- The two inclusions used to make the finite code persist under rotation. -/
theorem near_normal_box_inclusions (n : RealPlane) (hn : n ∈ unitNormals)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    ∃ U : Set RealPlane, IsOpen U ∧ n ∈ U ∧
      ∀ w ∈ U, w ∈ unitNormals →
        lineBox n s u ⊆ lineBox w (s + 1) (u + 1) ∧
        lineBox w 0 (u + 2) ⊆ lineBox n 1 (u + 3) := by
  let δ := 1/(s+u+3)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ*(s+u+3)=1 := by dsimp [δ]; field_simp
  refine ⟨{w | |realDot (realQuarterTurn n) w| < δ}, ?_, ?_, ?_⟩
  · apply isOpen_lt _ continuous_const
    dsimp [realDot,realQuarterTurn]
    fun_prop
  · change |realDot (realQuarterTurn n) n| < δ
    have he : realDot (realQuarterTurn n) n=0 := by
      dsimp [realDot,realQuarterTurn]
      ring
    simpa [he] using hd
  · intro w hw hunit
    change |realDot (realQuarterTurn n) w| < δ at hw
    have ha := rotation_dot_le_one n w hn hunit
    have hb0 := abs_nonneg (realDot (realQuarterTurn n) w)
    have hbS : s*|realDot (realQuarterTurn n) w| ≤ 1 := by nlinarith
    have hbU : u*|realDot (realQuarterTurn n) w| ≤ 1 := by nlinarith
    have hbU2 : (u+2)*|realDot (realQuarterTurn n) w| ≤ 1 := by nlinarith
    constructor
    · intro x hx
      change |realDot x (realQuarterTurn n)| ≤ s ∧ |realDot x n| ≤ u at hx
      change |realDot x (realQuarterTurn w)| ≤ s+1 ∧ |realDot x w| ≤ u+1
      rw [rotation_tan_formula n x w hn,rotation_dot_formula n x w hn]
      constructor
      · calc
          _ ≤ |realDot x (realQuarterTurn n) * realDot n w| +
              |realDot x n * realDot (realQuarterTurn n) w| := abs_sub _ _
          _ = |realDot x (realQuarterTurn n)| * |realDot n w| +
              |realDot x n| * |realDot (realQuarterTurn n) w| := by rw [abs_mul,abs_mul]
          _ ≤ s*1 + u*|realDot (realQuarterTurn n) w| :=
            add_le_add (mul_le_mul hx.1 ha (abs_nonneg _) hs.le)
              (mul_le_mul_of_nonneg_right hx.2 hb0)
          _ ≤ s+1 := by linarith
      · calc
          _ ≤ |realDot x n * realDot n w| +
              |realDot x (realQuarterTurn n) * realDot (realQuarterTurn n) w| := abs_add_le _ _
          _ = |realDot x n| * |realDot n w| +
              |realDot x (realQuarterTurn n)| * |realDot (realQuarterTurn n) w| := by rw [abs_mul,abs_mul]
          _ ≤ u*1 + s*|realDot (realQuarterTurn n) w| :=
            add_le_add (mul_le_mul hx.2 ha (abs_nonneg _) hu.le)
              (mul_le_mul_of_nonneg_right hx.1 hb0)
          _ ≤ u+1 := by linarith
    · intro x hx
      change |realDot x (realQuarterTurn w)| ≤ 0 ∧ |realDot x w| ≤ u+2 at hx
      have hx0 : realDot x (realQuarterTurn w)=0 := abs_nonpos_iff.mp hx.1
      have hcomm : realDot w n=realDot n w := by dsimp [realDot]; ring
      have hanti : realDot (realQuarterTurn w) n = -realDot (realQuarterTurn n) w := by
        dsimp [realDot,realQuarterTurn]; ring
      change |realDot x (realQuarterTurn n)| ≤ 1 ∧ |realDot x n| ≤ u+3
      rw [rotation_tan_formula w x n hunit,rotation_dot_formula w x n hunit]
      simp only [hx0,zero_mul,zero_sub,add_zero,hcomm,hanti,mul_neg,neg_neg,neg_zero]
      constructor
      · rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right hx.2 hb0).trans hbU2
      · rw [abs_mul]
        have hm := mul_le_mul hx.2 ha (abs_nonneg (realDot n w)) (by positivity : 0 ≤ u+2)
        nlinarith

end
end ConvexNivat.ExternalDynamicsHelpers
