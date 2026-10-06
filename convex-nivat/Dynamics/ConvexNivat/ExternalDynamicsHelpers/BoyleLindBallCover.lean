import ConvexNivat.ExternalDynamicsHelpers.BoyleLindDefinitions

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

private theorem ballCover_norm_sq (x : RealPlane) :
    planeNorm x ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  simpa [planeNorm, euclideanCoordinates, Fin.sum_univ_two] using
    EuclideanSpace.real_norm_sq_eq (euclideanCoordinates x)

private theorem ballCover_normal (p : RealPlane) :
    ∃ n ∈ unitNormals, realDot p (realQuarterTurn n) = 0 ∧
      realDot p n = planeNorm p := by
  have hp0 : 0 ≤ planeNorm p := norm_nonneg _
  have hps := ballCover_norm_sq p
  by_cases hp : planeNorm p = 0
  · have hp1 : p.1 = 0 := by nlinarith [sq_nonneg p.2]
    have hp2 : p.2 = 0 := by nlinarith [sq_nonneg p.1]
    refine ⟨(1,0), ?_, ?_, ?_⟩
    · change planeNorm (1,0) = 1
      have hs := ballCover_norm_sq (1,0)
      have hn0 : 0 ≤ planeNorm (1,0) := norm_nonneg _
      change planeNorm (1,0)^2 = (1:ℝ)^2 + 0^2 at hs
      nlinarith
    · simp [realDot,realQuarterTurn,hp1,hp2]
    · simp [realDot,hp1,hp2,hp]
  · refine ⟨(p.1 / planeNorm p, p.2 / planeNorm p), ?_, ?_, ?_⟩
    · change planeNorm (p.1 / planeNorm p, p.2 / planeNorm p) = 1
      have hs := ballCover_norm_sq (p.1 / planeNorm p, p.2 / planeNorm p)
      have hn0 : 0 ≤ planeNorm (p.1 / planeNorm p, p.2 / planeNorm p) := norm_nonneg _
      have hdiv : (p.1 / planeNorm p)^2 + (p.2 / planeNorm p)^2 = 1 := by
        rw [div_pow, div_pow, ← add_div, ← hps]
        exact div_self (pow_ne_zero _ hp)
      change planeNorm (p.1 / planeNorm p, p.2 / planeNorm p)^2 =
        (p.1 / planeNorm p)^2 + (p.2 / planeNorm p)^2 at hs
      nlinarith
    · simp only [realDot,realQuarterTurn]
      ring
    · simp only [realDot]
      field_simp
      nlinarith

private theorem ballCover_box (r t R c : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hsize : r^2 + (c+t)^2 ≤ R^2)
    (p n : RealPlane) (hn : n ∈ unitNormals)
    (hpt : realDot p (realQuarterTurn n) = 0)
    (hpn : |realDot p n - c| ≤ t+1) :
    ∃ a : RealPlane, realTranslate (lineBox n r t) a ⊆ realBall R ∧
      p ∈ realTranslate (lineBox n 0 (t+1)) a := by
  have hn2 : n.1^2+n.2^2=1 := by
    have hs := ballCover_norm_sq n
    change planeNorm n = 1 at hn
    nlinarith
  let a : RealPlane := (c*n.1,c*n.2)
  have hdot (q : RealPlane) : realDot (q-a) n = realDot q n - c := by
    dsimp [realDot,a]
    nlinarith [congrArg (fun v : ℝ => c*v) hn2]
  have htan (q : RealPlane) : realDot (q-a) (realQuarterTurn n) =
      realDot q (realQuarterTurn n) := by
    dsimp [realDot,realQuarterTurn,a]
    ring
  refine ⟨a, ?_, ?_⟩
  · intro q hq
    change |realDot (q-a) (realQuarterTurn n)| ≤ r ∧
      |realDot (q-a) n| ≤ t at hq
    rw [hdot,htan] at hq
    have hqn : |realDot q n| ≤ c+t := by
      calc
        |realDot q n| = |(realDot q n-c)+c| := by congr 1; ring
        _ ≤ |realDot q n-c|+|c| := abs_add_le _ _
        _ ≤ t+c := add_le_add hq.2 (le_of_eq (abs_of_nonneg hc))
        _ = c+t := add_comm _ _
    have hsq : planeNorm q^2 = (realDot q n)^2 + (realDot q (realQuarterTurn n))^2 := by
      rw [ballCover_norm_sq]
      dsimp [realDot,realQuarterTurn]
      nlinarith [congrArg (fun v : ℝ => (q.1^2+q.2^2)*v) hn2]
    have h1 := sq_le_sq₀ (abs_nonneg (realDot q n)) (by positivity : 0 ≤ c+t) |>.mpr hqn
    have h2 := sq_le_sq₀ (abs_nonneg (realDot q (realQuarterTurn n))) hr |>.mpr hq.1
    rw [sq_abs] at h1 h2
    change planeNorm q ≤ R
    nlinarith [norm_nonneg (euclideanCoordinates q)]
  · change |realDot (p-a) (realQuarterTurn n)| ≤ 0 ∧ |realDot (p-a) n| ≤ t+1
    rw [hdot,htan,hpt,abs_zero]
    exact ⟨le_rfl,hpn⟩

/-- The geometric flat-boundary claim inside Theorem 3.6, V={0}, d=2. -/
theorem large_ball_growth_box_cover (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ p ∈ realBall (R + 1 / 2), ∃ n ∈ unitNormals, ∃ a : RealPlane,
        realTranslate (lineBox n r t) a ⊆ realBall R ∧
        p ∈ realTranslate (lineBox n 0 (t + 1)) a := by
  refine ⟨r^2+(t+1)^2+1, by positivity, ?_⟩
  intro R hR p hp
  change planeNorm p ≤ R+1/2 at hp
  have hR0 : 0 ≤ R := by nlinarith [sq_nonneg r, sq_nonneg (t+1)]
  obtain ⟨n,hn,hpt,hpn⟩ := ballCover_normal p
  refine ⟨n,hn,?_⟩
  have hp0 : 0 ≤ planeNorm p := norm_nonneg _
  by_cases hsmall : planeNorm p ≤ t+1
  · refine ballCover_box r t R 0 hr.le ht.le hR0 (by norm_num) ?_ p n hn hpt ?_
    · nlinarith [sq_nonneg (R-1), sq_nonneg r, sq_nonneg t]
    · rw [hpn,sub_zero,abs_of_nonneg hp0]
      exact hsmall
  · have hc : 0 ≤ planeNorm p-t-1 := by linarith
    refine ballCover_box r t R (planeNorm p-t-1) hr.le ht.le hR0 hc ?_ p n hn hpt ?_
    · have hupper : (planeNorm p-1)^2 ≤ (R-1/2)^2 := by
        nlinarith
      nlinarith
    · rw [hpn]
      have he : planeNorm p-(planeNorm p-t-1)=t+1 := by ring
      rw [he,abs_of_nonneg (by positivity)]


/-- Applying the real-shift finite code at every covering box. -/
theorem uniform_box_code_large_ball_growth (ξ : Configuration ℤ)
    (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hcode : ∀ n ∈ unitNormals,
      RealCodes ξ (lineBox n r t) (lineBox n 0 (t + 1))) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      RealCodes ξ (realBall R) (realBall (R + 1 / 2)) := by
  obtain ⟨R₀,hR₀,hcover⟩ := large_ball_growth_box_cover r t hr ht
  refine ⟨R₀,hR₀,?_⟩
  intro R hR b x hx y hy hag z hz
  obtain ⟨n,hn,a,hsub,hz'⟩ := hcover R hR (embed z-b) hz
  have he (w : Lattice) : embed w-(b+a) = (embed w-b)-a := by abel
  apply hcode n hn (b+a) x hx y hy ?_ z ?_
  · intro w hw
    apply hag w
    apply hsub
    change (embed w-b)-a ∈ lineBox n r t
    rw [← he]
    exact hw
  · change embed z-(b+a) ∈ lineBox n 0 (t+1)
    rw [he]
    exact hz'

end
end ConvexNivat.ExternalDynamicsHelpers
